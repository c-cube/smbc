
(* This file is free software. See file "license" for more details. *)

let get_time : unit -> float =
  let start = Unix.gettimeofday() in
  fun () ->
    Unix.gettimeofday() -. start

module FI = Msat.Formula_intf
module TI = Msat.Theory_intf
module SI = Msat.Solver_intf

module Fmt = CCFormat

let fpf = Format.fprintf

(** {1 Solver} *)

module type CONFIG = sig
  val max_depth: int

  val deepening_step : int option
  (** Increment between two successive max depths in iterative deepening *)

  val progress: bool
  (** progress display progress bar *)

  val pp_hashcons: bool

  val dimacs_file : string option
  (** File for dumping the SAT problem *)
end

(** {2 The Main Solver} *)

module Make(Config : CONFIG)(Dummy : sig end) = struct
  exception Error of string

  let () = Printexc.register_printer
      (function
        | Error msg -> Some ("internal error: " ^ msg)
        | _ -> None)

  let errorf msg = Fmt.ksprintf msg ~f:(fun s -> raise (Error s))

  type level = int

  let stat_num_cst_expanded = ref 0
  let stat_num_uty_expanded = ref 0
  let stat_num_clause_push = ref 0
  let stat_num_clause_tautology = ref 0
  let stat_num_propagations = ref 0
  let stat_num_unif = ref 0

  (* for objects that are expanded on demand only *)
  type 'a lazily_expanded =
    | Lazy_some of 'a
    | Lazy_none

  (* reference into the stack *)
  type db_index = int

  type 'a db_env = {
    db_st: 'a list;  (* the stack *)
    db_size: int;     (* the stack size *)
  }

  type quant =
    | Forall
    | Exists

  type let_kind =
    | Let_lazy
    | Let_eager

  (* program: the static part of computations *)
  type prgm =
    | P_return of prgm_const (* return value (in current env) *)
    | P_let of let_kind * prgm * prgm
    (* [Let (a,b)] means putting a thunk of [a] on the stack at position [0],
       then evaluating [b] *)
    | P_match of db_index * (int * prgm) ID.Map.t
    (* [match k m] matches value number [k] on the stack against [m].
       An entry [(n,cont)] in [m] means that [n] values have to be pushed
       on the stack before calling continuation [cont] *)
    | P_if of db_index * prgm * prgm
    (* depending on value of [k], follow one of the branches *)
    | P_call of prgm * prgm list
    (* call given program with the arguments *)
    | P_lazy of prgm lazy_t
    (* used for recursion *)
    | P_and of db_index * db_index
    | P_not of db_index
    | P_eq of db_index * db_index
    | P_equiv of db_index * db_index

  (* TODO: switch/quant/check *)

  (* a "literal" constant occurring in the program *)
  and prgm_const =
    | C_true
    | C_false
    | C_cstor of cstor * prgm_const list (* apply constructor *)
    | C_dom_elt of dom_elt (* domain element *)
    | C_const of cst_undef (* undefined constant. Will evaluated further *)
    | C_var of db_index (* dereference eagerly *)

  (* an on-going (or terminated) computation, using call-by-need.
     A thunk is either resolved (into a weak-head normal form)
     or ongoing (as a suspension or some boolean operator) *)
  and thunk = {
    t_view: thunk_view; (* view *)
    t_deps: thunk_deps lazy_t; (* blocking the thunk *)
  }
  and thunk_view =
    | T_value of value
    | T_const of cst_undef
    | T_par_and of thunk * explanation * thunk * explanation
    (* parallel "and" of the two thunks *)
    | T_seq_and of thunk * thunk
    (* sequential "and" (left one first) *)
    | T_eq of thunk * thunk
    | T_equiv of thunk * thunk
    | T_not of thunk
    | T_ref of thunk_ref
    (* [T_ref (e, t)] is a mutable reference that, conceptually,
       evaluates into [t] with explanation [e]. It can be updated
       when [t] reduces to [u], but this update is backtrackable.
       [T_ref] is useful for sharing computations. *)
    | T_lazy of prgm * eval_env
    (* unevaluated thunk *)
    | T_suspend of prgm * db_index * eval_env * explanation
    (* a suspended program: the current codepointer,
       with the stack. The evaluation is blocked because the program
       needs the value of something on the stack (whose index is given).
       There is a partial explanation attached, for when this reduces to a value *)
    | T_check_assign of cst_undef * value
    (* [T_check_assign (c,v)] is true if [c := v], false otherwise *)

  (* a reference to a pair [explanation * thunk] *)
  and thunk_ref = (explanation * thunk) ref

  (* environment for evaluation *)
  and eval_env = thunk db_env

  (** A value in WHNF *)
  and value =
    | V_true
    | V_false
    | V_cstor of cstor * thunk list
    | V_dom_elt of dom_elt

  (* bag of atomic explanations. It is optimized for traversal
     and fast cons/snoc/append *)
  and explanation =
    | E_empty
    | E_leaf of lit
    | E_append of explanation * explanation * int (* size *)
    | E_or of explanation * explanation * int (* disjunction! *)

  (* what can block the evaluation of a thunk *)
  and thunk_deps = thunk_dep list

  and thunk_dep  =
    | Dep_cst of cst_undef
      (* blocked by non-refined constant *)
    | Dep_uty of ty_uninterpreted_slice
      (* blocked because this type is not expanded enough *)

  (* an "undefined" constant (i.e. an unknown we have to refine) *)
  and cst_undef = {
    cst_id: ID.t;
    cst_ty: ty;
    cst_depth: int;
    (* refinement depth, used for iterative deepening *)
    cst_parent: cst_undef option;
    (* if const was created as a parameter to some cases of some other constant *)
    cst_exist_conds: cst_exist_conds;
    (* disjunction of possible conditions for cst to exist/be relevant *)
    mutable cst_cases: value list lazily_expanded;
    (* cover set (lazily evaluated) *)
    mutable cst_complete: bool;
    (* does [cst_cases] cover all possible cases, or only
       a subset? Affects completeness *)
    mutable cst_cur_case: (explanation * value) option;
    (* current choice of normal form *)
  }

  and cstor = {
    cstor_id: ID.t;
    cstor_ty: ty;
  }

  and dom_elt = {
    dom_elt_id: ID.t;
    dom_elt_ty: ty;
  } (* TODO: also put the slice in it *)

  and ty =
    | Ty_arrow of ty * ty
    | Ty_prop
    | Ty_atomic of ID.t * ty_atomic
  and ty_atomic =
    | Ty_data of (cstor * ty) lazy_t list
    | Ty_uninterpreted of ty_uninterpreted_slice

  (* this is a disjunction of sufficient conditions for the existence of
     some meta (cst). Each condition is a literal *)
  and cst_exist_conds = lit lazy_t list ref

  (* TODO
  (* a table [m] from values of type [switch_ty_arg]
     to terms of type [switch_ty_ret],
     created by refining a meta [switch_cst : switch_ty_arg -> switch_ty_ret]
     into [fun x:switch_ty_arg. case x m] *)
  and switch_cell = {
    switch_tbl: switch_tbl;
    (* value -> term *)
    switch_ty_arg: ty_h;
    (* type of arguments *)
    switch_ty_ret: ty_h;
    (* type of return *)
    switch_make_new: (unit -> term);
    (* closure used to add a new case. Call it with a pure value
       that doesn't belong (yet) to [switch_tbl]. *)
    switch_cst: cst;
    (* constant refined into [fun x. case x m] *)
    switch_id: int;
    (* unique ID for this case *)
  }

  and switch_tbl = term ID.Tbl.t
  *)

  (* boolean literal *)
  and lit = {
    lit_view: lit_view;
    lit_sign: bool;
    mutable lit_id: int; (* hashconsing ID *)
    mutable lit_neg: lit; (* negation *)
  }

  and lit_view =
    | Lit_fresh of ID.t (* fresh literals *)
    | Lit_atom of int * thunk (* unique generative ID + the thunk to evaluate *)
    | Lit_assign of cst_undef * value (* [cst := value] *)
    | Lit_uty_empty of ty_uninterpreted_slice

  (* current status of this slice of uninterpreted type in the model *)
  and ty_uninterpreted_status =
    | Uty_empty
    | Uty_nonempty

  (* TODO *)
  (* A slice of an uninterpreted type's the domain.
     For instance, if [u] is uninterpreted, it might be defined as
     [(u0 | (u1 | (empty)))] where [empty] will be expanded into [(u2 | empty)]
     if needed. We write [u[3:]] to designate the slice of [u]'s domain
     that skips the first 3 elements. *)
  and ty_uninterpreted_slice = {
    uty_id: ID.t;
    (* the ID of the type *)
    uty_offset: int;
    (* length of path from root [Uninterpreted]; in other words, the
       number of elements that have been skipped. *)
    uty_parent: ty_uninterpreted_slice option;
    (* if [offset>0], the previous slice *)
    mutable uty_pair: (cst_undef * ty_uninterpreted_slice) lazily_expanded;
    (* the domain constant, must be Cst_uninterpreted_dom_elt,
       and the next slice.
       Expanded on demand. *)
    mutable uty_status: (explanation * ty_uninterpreted_status) option;
    (* current status in the model *)
  }

  let pp_quant out = function
    | Forall -> Fmt.string out "forall"
    | Exists -> Fmt.string out "exists"

  module Ty = struct
    type t = ty

    let view (t:ty) = t

    let rec equal a b = match view a, view b with
      | Ty_prop, Ty_prop -> true
      | Ty_atomic (i1,_), Ty_atomic (i2,_) -> ID.equal i1 i2
      | Ty_arrow (a1,b1), Ty_arrow (a2,b2) ->
        equal a1 a2 && equal b1 b2
      | Ty_prop, _
      | Ty_atomic _, _
      | Ty_arrow _, _ -> false

    let rec hash t = match view t with
      | Ty_prop -> 1
      | Ty_atomic (i,_) -> Hash.combine2 2 (ID.hash i)
      | Ty_arrow (a,b) -> Hash.combine3 3 (hash a) (hash b)

    let prop = Ty_prop
    let atomic id def = Ty_atomic (id,def)
    let arrow a b = Ty_arrow (a,b)
    let arrow_l = List.fold_right arrow

    let is_prop t = match view t with Ty_prop -> true | _ -> false

    let is_data t = match view t with Ty_atomic (_, Ty_data _) -> true | _ -> false

    let unfold ty : t list * t =
      let rec aux acc ty = match view ty with
        | Ty_arrow (a,b) -> aux (a::acc) b
        | _ -> List.rev acc, ty
      in
      aux [] ty

    let rec pp out t = match view t with
      | Ty_prop -> Fmt.string out "prop"
      | Ty_atomic (id, _) -> ID.pp out id
      | Ty_arrow _ ->
        let args, ret = unfold t in
        Format.fprintf out "(@[=>@ %a@ %a@])"
          (Utils.pp_list pp) args pp ret

    (* representation as a single identifier *)
    let rec mangle t : string = match view t with
      | Ty_prop -> "prop"
      | Ty_atomic (id,_) -> ID.to_string id
      | Ty_arrow (a,b) -> mangle a ^ "_" ^ mangle b

    module Tbl = CCHashtbl.Make(struct type t=ty let equal=equal let hash=hash end)
  end

  module DB_env = struct
    type 'a t = 'a db_env

    let push x env = { db_size=env.db_size+1; db_st=x::env.db_st }
    let push_l l env = List.fold_left (fun e x -> push x e) env l
    let empty = {db_st=[]; db_size=0}
    let singleton x = {db_st=[x]; db_size=1}
    let size env = env.db_size
    let get n env : _ option =
      if n < env.db_size then Some (List.nth env.db_st n) else None
    let get_exn n env =
      if n < env.db_size then List.nth env.db_st n else invalid_arg "DB_env.get_exn"
    let set_ n v env =
      if n >= env.db_size then invalid_arg "DB_env.set";
      {env with db_st = CCList.Idx.set env.db_st n v}
    let pp pp_x out e =
      let l = List.mapi (fun i o -> i,o) e.db_st in
      if not (CCList.is_empty l) then (
        let pp_pair out (i,x) =
          Format.fprintf out "@[%d: %a@]" i pp_x x
        in
        Fmt.list ~sep:"," pp_pair out l
      )
  end

  module Cst_undef = struct
    type t = cst_undef

    let id t = t.cst_id
    let depth (c:t): int = c.cst_depth

    let make ?parent ?exist_if ?slice ~depth:cst_depth id ty =
      assert (CCOpt.for_all (fun p -> cst_depth > depth p) parent);
      { cst_id=id;
        cst_ty=ty;
        cst_depth;
        cst_parent=parent;
        cst_exist_conds=CCOpt.get_lazy (fun ()->ref []) exist_if;
        cst_cases=Lazy_none;
        cst_complete=true;
        cst_cur_case=None;
      }

    let equal a b = ID.equal a.cst_id b.cst_id
    let compare a b = ID.compare a.cst_id b.cst_id
    let hash t = ID.hash t.cst_id
    let pp out a = ID.pp out a.cst_id

    module Map = CCMap.Make(struct type t = cst_undef let compare = compare end)
  end

  let cmp_uty a b =
    let c = ID.compare a.uty_id b.uty_id in
    if c<>0 then c
    else CCOrd.int_ a.uty_offset b.uty_offset

  let equal_uty a b = cmp_uty a b = 0

  let hash_uty uty =
    Hash.combine3 104 (ID.hash uty.uty_id) uty.uty_offset

  let cmp_lit a b = CCInt.compare a.lit_id b.lit_id
  let eq_lit a b = a.lit_id=b.lit_id
  let hash_lit a = a.lit_id

  let pp_uty out uty =
    let n = uty.uty_offset in
    if n=0
    then fpf out "%a[:]" ID.pp uty.uty_id
    else fpf out "%a[%d:]" ID.pp uty.uty_id n

  let pp_uty_status out = function
    | Uty_empty -> Fmt.string out "empty"
    | Uty_nonempty -> Fmt.string out "non_empty"

  let pp_dep out = function
    | Dep_cst c -> Cst_undef.pp out c
    | Dep_uty uty -> pp_uty out uty

  module Backtrack = struct
    type _level = level
    type level = _level

    let dummy_level = -1

    type stack_cell =
      | S_set_nf of
          thunk_ref * (explanation * thunk)
          (* t1.nf <- t2 *)
      | S_set_cst_case of
          cst_undef * (explanation * value) option
          (* c1.cst_case <- t2 *)
      | S_set_uty of
          ty_uninterpreted_slice * (explanation * ty_uninterpreted_status) option
          (* uty1.uty_status <- status2 *)

    type stack = stack_cell CCVector.vector

    (* the global stack *)
    let st_ : stack = CCVector.create()

    let backtrack (l:level): unit =
      Log.debugf 2
        (fun k->k "@{<Yellow>** now at level %d (backtrack)@}" l);
      while CCVector.length st_ > l do
        match CCVector.pop_exn st_ with
          | S_set_nf (t, nf) -> t := nf
          | S_set_cst_case (cst, v) -> cst.cst_cur_case <- v;
          | S_set_uty (uty, s) -> uty.uty_status <- s;
      done;
      ()

    let cur_level () = CCVector.length st_

    let push_level () : unit =
      let l = cur_level() in
      Log.debugf 2 (fun k->k "@{<Yellow>** now at level %d (push)@}" l);
      ()

    let push_set_nf_ (r:thunk_ref) =
      CCVector.push st_ (S_set_nf (r, !r))

    let push_set_cst_case_ (cst:cst_undef) =
      CCVector.push st_ (S_set_cst_case (cst, cst.cst_cur_case))

    let push_uty_status (uty:ty_uninterpreted_slice) =
      CCVector.push st_ (S_set_uty (uty, uty.uty_status))
  end

  let new_switch_id_ =
    let n = ref 0 in
    fun () -> incr n; !n

  let pp_db out (i:int) = fpf out "%%%d" i

  module Prgm = struct
    type t = prgm

    let view (p:t) = p

    let true_ = C_true
    let false_ = C_false
    let cstor c args = C_cstor (c,args)
    let cstor0 c = cstor c []
    let dom_elt c = C_dom_elt c
    let const c = C_const c
    let var v = C_var v

    let return v = P_return v
    let let_ k a b = P_let (k,a,b)
    let match_ u m = P_match (u,m)
    let if_ a b c = P_if (a,b,c)
    let call p args = P_call (p,args)
    let lazy_ p = P_lazy p
    let and_ a b = P_and (a,b)
    let not_ a = P_not a
    let eq a b = P_eq (a,b)
    let equiv a b = P_equiv (a,b)

    let rec pp_const out = function
      | C_true -> Fmt.string out "true"
      | C_false -> Fmt.string out "false"
      | C_cstor (a,[]) -> ID.pp out a.cstor_id
      | C_cstor (a,l) ->
        fpf out "(@[%a@ %a@])" ID.pp a.cstor_id (Utils.pp_list pp_const) l
      | C_const c -> Cst_undef.pp out c
      | C_dom_elt c -> ID.pp out c.dom_elt_id
      | C_var v -> pp_db out v

    let pp_let_kind out =
      function Let_lazy -> () | Let_eager -> Fmt.string out "!"

    let rec pp out = function
      | P_return v -> fpf out "(@[<2>return@ %a@])" pp_const v
      | P_let (k,a,b) -> fpf out "(@[<2>let%a@ %a@ %a@])" pp_let_kind k pp a pp b
      | P_match (u,m) ->
        let pp_bind out (id,(n,rhs)) =
          fpf out "(@[<1>%a/%d@ %a@])" ID.pp id n pp rhs
        in
        let print_map =
          Fmt.seq ~start:"" ~stop:"" ~sep:" " pp_bind
        in
        fpf out "(@[match %a@ (@[<hv>%a@])@])"
          pp_db u print_map (ID.Map.to_seq m)
      | P_if (a,b,c) ->
        fpf out "(@[<hv2>if %a@ %a@ %a@])" pp_db a pp b pp c
      | P_call (p,args) ->
        fpf out "(@[<2>call@ %a@ args: [@[%a@]]@])" pp p (Utils.pp_list pp) args
      | P_lazy _ -> Fmt.string out "<lazy>"
      | P_and (a,b) -> fpf out "(@[<2>and@ %a@ %a@])" pp_db a pp_db b
      | P_eq (a,b) -> fpf out "(@[<2>eq@ %a@ %a@])" pp_db a pp_db b
      | P_equiv (a,b) -> fpf out "(@[<2>equiv@ %a@ %a@])" pp_db a pp_db b
      | P_not a -> fpf out "(@[not@ %a@])" pp_db a
  end

  let cmp_dep_ a b =
    let to_int_ = function
      | Dep_cst _ -> 0
      | Dep_uty _ -> 1
    in
    begin match a, b with
      | Dep_cst c1, Dep_cst c2 -> Cst_undef.compare c1 c2
      | Dep_uty u1, Dep_uty u2 ->
        let (<?>) = CCOrd.(<?>) in
        ID.compare u1.uty_id u2.uty_id
        <?> (CCOrd.int_, u1.uty_offset, u2.uty_offset)
      | Dep_cst _, _
      | Dep_uty _, _
        -> CCOrd.int_ (to_int_ a) (to_int_ b)
    end

  let rec pp_thunk out (t:thunk): unit = match t.t_view with
    | T_value v -> pp_value out v
    | T_const c -> Cst_undef.pp out c
    | T_par_and (a,_,b,_) -> fpf out "(@[<hv2>and@ %a@ %a@])" pp_thunk a pp_thunk b
    | T_seq_and (a,b) -> fpf out "(@[<hv2>&&@ %a@ %a@])" pp_thunk a pp_thunk b
    | T_eq (a,b) -> fpf out "(@[<hv2>=@ %a@ %a@])" pp_thunk a pp_thunk b
    | T_equiv (a,b) -> fpf out "(@[<hv2><=>@ %a@ %a@])" pp_thunk a pp_thunk b
    | T_not a -> fpf out "(@[<2>not@ %a@])" pp_thunk a
    | T_ref {contents=(_,u)} -> fpf out "(@[<2>ref@ %a@])" pp_thunk u
    | T_lazy (p,env) ->
      fpf out "(@[<2>lazy %a@ [@[%a@]]@])"
        Prgm.pp p (DB_env.pp pp_thunk) env
    | T_suspend (p,i,env,_) ->
      fpf out "(@[<2>suspend %a@ [@[%a@]]/%d@])"
        Prgm.pp p (DB_env.pp pp_thunk) env i
    | T_check_assign (c,v) ->
      fpf out "(@[<2>check %a :=@ %a@])" Cst_undef.pp c pp_value v

  and pp_value out (v:value): unit = match v with
    | V_true -> Fmt.string out "true"
    | V_false -> Fmt.string out "false"
    | V_cstor (a,[]) -> ID.pp out a.cstor_id
    | V_cstor (a,l) ->
      fpf out "(@[%a@ %a@])" ID.pp a.cstor_id (Utils.pp_list pp_thunk) l
    | V_dom_elt c -> ID.pp out c.dom_elt_id

  module Value = struct
    type t = value

    let true_ = V_true
    let false_ = V_false
    let cstor a l = V_cstor (a,l)
    let dom_elt c= V_dom_elt c

    (* shallow equality, sufficient in most cases. Do not look inside. *)
    let equal_shallow (a:t)(b:t): bool = match a, b with
      | V_true, V_true
      | V_false, V_false -> true
      | V_dom_elt c1, V_dom_elt c2 -> ID.equal c1.dom_elt_id c2.dom_elt_id
      | V_cstor (c1,_), V_cstor (c2,_) -> ID.equal c1.cstor_id c2.cstor_id
      | V_true, _
      | V_false, _
      | V_dom_elt _, _
      | V_cstor _, _
        -> false

    let hash_shallow (a:t): int = match a with
      | V_true -> 1
      | V_false -> 2
      | V_dom_elt c -> Hash.combine2 3 (ID.hash c.dom_elt_id)
      | V_cstor (c,l) ->
        Hash.combine3 4 (ID.hash c.cstor_id) (Hash.int (List.length l))

    let pp = pp_value
  end

  module Thunk = struct
    type t = thunk

    let view t = t.t_view
    let deps (t:thunk): thunk_deps = Lazy.force t.t_deps

    let merge_deps = CCList.sorted_merge_uniq ~cmp:cmp_dep_

    let compute_deps (t:thunk_view): thunk_deps = match t with
      | T_check_assign (c,_) | T_const c -> [Dep_cst c]
      | T_lazy _
      | T_value _ -> []
      | T_seq_and (a, _) | T_not a -> deps a
      | T_par_and (a,_,b,_) | T_equiv (a,b) | T_eq (a,b) ->
        merge_deps (deps a) (deps b)
      | T_ref {contents=(_,u)} -> deps u
      | T_suspend (_,i,env,_) -> deps (DB_env.get_exn i env)

    let mk_ view = {
      t_view=view;
      t_deps=lazy (compute_deps view);
    }

    let value v = mk_ (T_value v)
    let true_ = value V_true
    let false_ = value V_false
    let cstor a l = value (V_cstor (a,l))
    let dom_elt c = value (V_dom_elt c)

    let abs (t:thunk): t * bool = match t.t_view with
      | T_value V_false -> true_, false
      | T_not u -> u, false
      | _ -> t, true

    let is_value t = match view t with T_value _ -> true | _ -> false

    let cst_undef c = mk_ (T_const c)

    let not_ t = match t.t_view with
      | T_not a -> a
      | T_value V_true -> false_
      | T_value V_false -> true_
      | _ -> mk_ (T_not t)

    let and_ a b = mk_ (T_par_and (a, E_empty, b, E_empty))

    let rec and_l = function
      | [] -> true_
      | [a] -> a
      | a :: l -> and_ a (and_l l)

    let and_par a e_a b e_b = mk_ (T_par_and (a, e_a, b, e_b))

    let and_seq a b = mk_ (T_seq_and (a,b))

    let eq a b = mk_ (T_eq (a,b))

    let equiv a b = mk_ (T_equiv (a,b))

    let ref_ t = mk_ (T_ref (ref (E_empty, t)))

    let mk_ref r = mk_ (T_ref r)

    let check_assign c v = mk_ (T_check_assign (c,v))

    let lazy_ p env = mk_ (T_lazy (p, env))

    let suspend p i env e =
      assert (i >= 0 && i < DB_env.size env);
      mk_ (T_suspend (p,i,env,e))

    let pp = pp_thunk

    (* evaluate program literal under given environment *)
    let rec eval_const (env:thunk db_env) (v:prgm_const) : thunk =
      begin match v with
        | C_true -> true_
        | C_false -> false_
        | C_cstor (a,[]) -> cstor a []
        | C_cstor (a,l) -> cstor a (List.map (eval_const env) l)
        | C_dom_elt c -> dom_elt c
        | C_const c -> cst_undef c
        | C_var i -> DB_env.get_exn i env
      end

    (* return [Some] iff the term is an undefined constant *)
    let as_cst_undef (t:thunk): cst_undef option = match t.t_view with
      | T_const c -> Some c | _ -> None

    (* return [Some (cstor,ty,args)] if the thunk is a constructor
       applied to some arguments *)
    let as_cstor_app (t:thunk): (cstor * thunk list) option = match t.t_view with
      | T_value (V_cstor (a,l)) -> Some (a,l)
      | _ -> None

    let as_domain_elt (t:thunk): dom_elt option = match t.t_view with
      | T_value (V_dom_elt c) -> Some c
      | _ -> None

    (* typical view for unification/equality *)
    type unif_form =
      | Unif_cst of cst_undef
      | Unif_cstor of cstor * thunk list
      | Unif_dom_elt  of dom_elt
      | Unif_none

    let as_unif (t:thunk): unif_form = match t.t_view with
      | T_const c -> Unif_cst c
      | T_value (V_cstor (a,l)) -> Unif_cstor (a,l)
      | T_value (V_dom_elt c) -> Unif_dom_elt c
      | _ -> Unif_none
  end

  let pp_lit out l =
    let pp_lit_view out = function
      | Lit_fresh i -> fpf out "#%a" ID.pp i
      | Lit_atom (i,t) -> fpf out "(@[<1>atom_%d@ %a@])" i Thunk.pp t
      | Lit_assign (c,v) ->
        fpf out "(@[:= %a@ %a@])" Cst_undef.pp c Value.pp v
      | Lit_uty_empty u -> fpf out "(empty %a)" pp_uty u
    in
    if l.lit_sign then pp_lit_view out l.lit_view
    else fpf out "(@[@<1>¬@ %a@])" pp_lit_view l.lit_view

  (** {2 Literals} *)
  module Lit : sig
    type t = lit
    val neg : t -> t
    val abs : t -> t
    val sign : t -> bool
    val view : t -> lit_view
    val as_atom : t -> (thunk * bool) option
    val as_atom_exn : t -> thunk * bool
    val fresh_with : ID.t -> t
    val fresh : unit -> t
    val dummy : t
    val atom : ?sign:bool -> thunk -> t
    val eq : thunk -> thunk -> t
    val cst_choice : cst_undef -> value -> t
    val uty_choice_empty : ty_uninterpreted_slice -> t
    val uty_choice_nonempty : ty_uninterpreted_slice -> t
    val uty_choice_status : ty_uninterpreted_slice -> ty_uninterpreted_status -> t
    val hash : t -> int
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val print : t Fmt.printer
    val pp : t Fmt.printer
    val norm : t -> t * FI.negated
    module Set : CCSet.S with type elt = t
    module Tbl : CCHashtbl.S with type key = t
  end = struct
    type t = lit

    let neg l = l.lit_neg

    let equal_lit_ a b =
      a.lit_sign = b.lit_sign &&
      begin match a.lit_view, b.lit_view with
        | Lit_fresh i1, Lit_fresh i2 -> ID.equal i1 i2
        | Lit_atom (i1,_), Lit_atom (i2,_)-> CCInt.equal i1 i2
        | Lit_assign (c1,t1), Lit_assign (c2,t2) ->
          Cst_undef.equal c1 c2 && Value.equal_shallow t1 t2
        | Lit_uty_empty u1, Lit_uty_empty u2 -> equal_uty u1 u2
        | Lit_fresh _, _
        | Lit_atom _, _
        | Lit_assign _, _
        | Lit_uty_empty _, _
          -> false
      end

    let hash_lit_ a =
      let sign = a.lit_sign in
      begin match a.lit_view with
        | Lit_fresh i -> Hash.combine3 1 (Hash.bool sign) (ID.hash i)
        | Lit_atom (i,_) -> Hash.combine3 2 (Hash.bool sign) (Hash.int i)
        | Lit_assign (c,v) ->
          Hash.combine4 3 (Hash.bool sign) (Cst_undef.hash c) (Value.hash_shallow v)
        | Lit_uty_empty uty -> Hash.combine3 4 (Hash.bool sign) (hash_uty uty)
      end

    module H = Hashcons.Make(struct
        type t = lit
        let equal = equal_lit_
        let hash = hash_lit_
        let set_id lit id =
          assert (lit.lit_id = -1);
          lit.lit_id <- id
      end)

    let sign t = t.lit_sign
    let view (t:t): lit_view = t.lit_view

    let abs t: t = if t.lit_sign then t else neg t

    let rec make ~sign view: lit =
      let rec lit = {
        lit_id= -1;
        lit_view=view;
        lit_sign= sign;
        lit_neg=lit;
      } in
      let lit' = H.hashcons lit in
      if lit == lit' then (
        assert (lit'.lit_neg == lit');
        lit'.lit_neg <- make view ~sign:(not sign); (* ensure negation exists *)
      );
      lit'

    (* assume the ID is fresh *)
    let fresh_with id = make ~sign:true (Lit_fresh id)

    (* fresh boolean literal *)
    let fresh: unit -> t =
      let n = ref 0 in
      fun () ->
        let id = ID.makef "#fresh_%d" !n in
        incr n;
        make ~sign:true (Lit_fresh id)

    let dummy = fresh()

    let atom =
      let n = ref 0 in
      fun ?(sign=true) (t:thunk) : t ->
        let t, sign' = Thunk.abs t in
        let sign = if not sign' then not sign else sign in
        incr n;
        make ~sign (Lit_atom (!n,t))

    let eq a b = atom ~sign:true (Thunk.eq a b)
    let cst_choice c t = make ~sign:true (Lit_assign (c, t))
    let uty_choice_empty uty = make ~sign:true (Lit_uty_empty uty)
    let uty_choice_nonempty uty : t = make ~sign:false (Lit_uty_empty uty)
    let uty_choice_status uty s : t = match s with
      | Uty_empty -> uty_choice_empty uty
      | Uty_nonempty -> uty_choice_nonempty uty

    let as_atom (lit:t) : (thunk * bool) option = match lit.lit_view with
      | Lit_atom (_,t) -> Some (t, lit.lit_sign)
      | _ -> None

    let as_atom_exn lit = match as_atom lit with
      | Some (t,b) -> t, b
      | None -> invalid_arg "Lit.as_atom_exn"

    let hash = hash_lit
    let compare = cmp_lit
    let equal = eq_lit
    let pp = pp_lit
    let print = pp

    let norm l =
      if l.lit_sign then l, FI.Same_sign else neg l, FI.Negated

    module Set = CCSet.Make(struct type t = lit let compare=compare end)
    module Tbl = CCHashtbl.Make(struct type t = lit let equal=equal let hash=hash end)
  end

  module Explanation = struct
    type t = explanation
    let empty : t = E_empty
    let return e = E_leaf e
    let size = function
      | E_empty -> 0
      | E_leaf _ -> 1
      | E_append (_,_,n) | E_or (_,_,n) -> n
    let or_ a b = match a, b with
      | E_empty, _ -> b
      | _, E_empty -> a
      | _ -> E_or (a, b, size a + size b)
    let append s1 s2 = match s1, s2 with
      | E_empty, _ -> s2
      | _, E_empty -> s1
      | _ -> E_append (s1, s2, size s1+size s2)
    let cons e s = append (return e) s

    let is_empty = function
      | E_empty -> true
      | E_leaf _ | E_or _ | E_append _ -> false (* by smart cstor *)

    let to_lists e: lit list Sequence.t =
      let open Sequence.Infix in
      let rec aux acc = function
        | E_empty -> Sequence.return acc
        | E_leaf x -> Sequence.return (x::acc)
        | E_append (a,b,_) ->
          aux acc a >>= fun acc ->
          aux acc b
        | E_or (a,b,_) ->
          Sequence.append (aux acc a)(aux acc b)
      in
      aux [] e

    let to_lists_l e: lit list list = to_lists e |> Sequence.to_rev_list

    let to_lists_uniq e =
      let f l = Lit.Set.of_list l |> Lit.Set.to_list in
      to_lists e |> Sequence.map f

    let to_lists_uniq_l e =
      to_lists_uniq e |> Sequence.to_rev_list

    let pp out e =
      let pp1 out l =
        fpf out "(@[%a@])"
          (Utils.pp_list Lit.pp) l
      in
      match to_lists_uniq_l e with
        | [] -> assert false
        | [e] -> pp1 out e
        | l ->
          fpf out "(@[<hv2>or@ %a@])"
            (Utils.pp_list pp1) l
  end

  (** {2 Clauses} *)

  module Clause : sig
    type t = private {
      lits: Lit.t list;
      id: int;
    }
    val make : Lit.t list -> t
    val lits : t -> Lit.t list
    val lemma_queue : t Queue.t
    val push_new : t -> unit
    val push_new_l : t list -> unit
    val iter : (Lit.t -> unit) -> t -> unit
    val to_seq : t -> Lit.t Sequence.t
    val pp : t Fmt.printer
  end = struct
    type t = {
      lits: Lit.t list;
      id: int;
    }

    let lits c = c.lits

    let pp out c = match c.lits with
      | [] -> Fmt.string out "false"
      | [lit] -> Lit.pp out lit
      | _ ->
        fpf out "(@[<hv1>or@ %a@ id: %d@])"
          (Utils.pp_list Lit.pp) c.lits c.id

    (* canonical form: sorted list *)
    let make =
      let n_ = ref 0 in
      fun l ->
        let c = {
          lits=CCList.sort_uniq ~cmp:Lit.compare l;
          id= !n_;
        } in
        incr n_;
        c

    let equal_ c1 c2 = CCList.equal Lit.equal c1.lits c2.lits
    let hash_ c = Hash.list Lit.hash c.lits

    module Tbl = CCHashtbl.Make(struct
        type t_ = t
        type t = t_
        let equal = equal_
        let hash = hash_
      end)

    (* all lemmas generated so far, to avoid duplicates *)
    let all_lemmas_ : unit Tbl.t = Tbl.create 1024

    (* list of clauses that have been newly generated, waiting
       to be propagated to Msat.
       invariant: those clauses must be tautologies *)
    let lemma_queue : t Queue.t = Queue.create()

    let push_new (c:t): unit =
      begin match c.lits with
        | [a;b] when Lit.equal (Lit.neg a) b -> () (* trivial *)
        | _ when Tbl.mem all_lemmas_ c -> () (* already asserted *)
        | _ ->
          Log.debugf 3
            (fun k->k "(@[<1>@{<green>new_tautology@}@ @[%a@]@])" pp c);
          incr stat_num_clause_tautology;
          Tbl.add all_lemmas_ c ();
          Queue.push c lemma_queue
      end;
      ()

    let push_new_l = List.iter push_new

    let iter f c = List.iter f c.lits
    let to_seq c = Sequence.of_list c.lits
  end

  (** {2 Iterative Deepening} *)

  module Iterative_deepening : sig
    type t = private int
    val max_depth : t

    type state =
      | At of t * Lit.t
      | Exhausted

    val reset : unit -> unit
    val current : unit -> state
    val current_depth : unit -> t
    val current_lit : unit -> Lit.t
    val next : unit -> state
    val lit_of_depth : int -> Lit.t option
    val lit_max_smaller_than : int -> int * Lit.t
    (** maximal literal strictly smaller than the given depth *)

    val pp: t Fmt.printer
  end = struct
    type t = int

    let pp = Fmt.int

    (* how much between two consecutive depths? *)
    let step_ = match Config.deepening_step with
      | None -> 5
      | Some s ->
        if s < 1 then invalid_arg "depth-step must be >= 1";
        s

    (* truncate at powers of {!step_} *)
    let max_depth =
      if Config.max_depth < step_
      then errorf "max-depth should be >= %d" step_;
      let rem = Config.max_depth mod step_ in
      let res = Config.max_depth - rem in
      Log.debugf 1 (fun k->k "(set_max_depth %d)" res);
      assert (res mod step_ = 0);
      res

    type state =
      | At of t * Lit.t
      | Exhausted

    (* create a literal standing for [max_depth = d] *)
    let mk_lit_ d : Lit.t =
      let id = ID.makef "max_depth_leq_%d" d in
      Lit.fresh_with id

    let lits_ : (int, Lit.t) Hashtbl.t = Hashtbl.create 32

    (* get the literal correspond to depth [d], if any *)
    let rec lit_of_depth d : Lit.t option =
      if d < step_ || (d mod step_ <> 0) || d > max_depth
      then None
      else match CCHashtbl.get lits_ d with
        | Some l -> Some l
        | None ->
          let lit = mk_lit_ d in
          Hashtbl.add lits_ d lit;
          (* relation with previous lit: [prev_lit => lit] *)
          begin match prev d with
            | None -> assert (d=step_); ()
            | Some prev_lit ->
              let c = Clause.make [Lit.neg prev_lit; lit] in
              Clause.push_new c;
          end;
          Some lit

    (* previous literal *)
    and prev d : Lit.t option =
      assert (d mod step_ = 0);
      lit_of_depth (d - step_)

    let lit_max_smaller_than d =
      (* find the largest [prev_depth]
         s.t. [prev_depth mod step=0] and [prev_depth<d] *)
      let d_prev = max 0 (d-1) in
      let prev_depth = d_prev - (d_prev mod step_) in
      assert (prev_depth >= 0 && (prev_depth mod step_ = 0));
      match lit_of_depth prev_depth with
        | Some lit -> prev_depth, lit
        | None ->
          assert (prev_depth = 0);
          prev_depth, Lit.atom Thunk.true_

    (* initial state *)
    let start_ =
      match lit_of_depth step_ with
        | None -> assert false
        | Some lit -> At (step_, lit)

    let cur_ = ref start_
    let reset () = cur_ := start_
    let current () = !cur_

    let current_depth () = match !cur_ with
      | Exhausted -> max_depth
      | At (d,_) -> d

    let current_lit () = match !cur_ with
      | Exhausted -> assert false
      | At (_,lit) -> lit

    (* next state *)
    let next () = match !cur_ with
      | Exhausted -> assert false
      | At (l_old, _) ->
        (* update level and current lit *)
        let l = l_old + step_ in
        let st =
          if l > max_depth
          then Exhausted
          else (
            let lit =
              match lit_of_depth l with
                | Some lit -> lit
                | None -> errorf "increased depth to %d, but not lit" l
            in
            Log.debugf 2
              (fun k->k
                  "(@[<1>iterative_deepening :level %d :lit %a@])" l Lit.pp lit);
            At (l, lit)
          )
        in
        cur_ := st;
        st
  end

  (** {2 Case Expansion} *)

  let declare_defined_cst _ = ()

  module Expand = struct
    (* make a fresh constant, with a unique name *)
    let new_cst_ =
      let n = ref 0 in
      fun ?slice ?exist_if ~parent ~depth name ty : cst_undef ->
        let id = ID.makef "?%s_%d" name !n in
        incr n;
        Cst_undef.make ?slice ?exist_if ~parent ~depth id ty

    (* [imply_opt g cs] returns [F => cs] if [g=Some F], or [cs] otherwise *)
    let imply_opt g (c:Lit.t list): Lit.t list = match g with
      | None -> c
      | Some g -> Lit.neg g :: c

    (* [imply_product l cs] builds the list of
       [F => cs] for each [F] in [l], or returns [cs] if [l] is empty *)
    let imply_product guards (c:Lit.t list) : Lit.t list list =
      match guards with
        | [] -> [c]
        | l -> List.map (fun f -> Lit.neg f :: c) l

    (* build the list of clauses that enforce the choice between
       [uty = empty] and [uty = c_head : uty_tail] *)
    let clauses_of_uty (uty:ty_uninterpreted_slice) : Clause.t list =
      let n = uty.uty_offset in
      let guard = Iterative_deepening.lit_of_depth n in
      let lit_nonempty = Lit.uty_choice_nonempty uty in
      (* - if we have a parent:
           nonempty => the previous slice must also be nonempty
         - if we don't have a parent:
           must never be empty*)
      let c_inherit = match uty.uty_parent with
        | None -> [lit_nonempty] |> Clause.make
        | Some uty' ->
          [Lit.neg lit_nonempty; Lit.uty_choice_nonempty uty'] |> Clause.make
      (* depth limit *)
      and cs_limit = match guard with
        | None -> []
        | Some g ->
          [[Lit.neg lit_nonempty; Lit.neg g] |> Clause.make]
      in
      c_inherit :: cs_limit

    (* expand the given slice, if needed, adding required constraints
       to {!Clause}, and return its head constant and remaining slice. E.g.,
       on [τ[4:]], it will return [τ_4, τ[5:]]. *)
    let expand_uninterpreted_slice (_uty:ty_uninterpreted_slice) = assert false
      (* TODO: update
      : cst * ty_uninterpreted_slice * Clause.t list =
      match uty.uty_pair with
        | Lazy_none ->
          (* create a new domain element *)
          let lazy ty = uty.uty_self in
          let n = uty.uty_offset in
          (* find a name for the new domain element *)
          let c_id =
            let ty_id = match Ty.view ty with
              | Atomic (i, _) -> i
              | _ -> assert false
            in
            ID.makef "$%a_%d" ID.pp_name ty_id n
          in
          let c_head = Cst_undef.make_uty_dom_elt c_id ty uty in
          (* create the next slice *)
          let uty_tail = {
            uty_self=uty.uty_self;
            uty_parent=Some uty;
            uty_pair=Lazy_none;
            uty_offset=n+1;
            uty_status=None;
          } in
          Log.debugf 5
            (fun k->k "expand slice %a@ into (@[%a,@ %a@])"
                pp_uty uty Cst_undef.pp c_head pp_uty uty_tail);
          (* memoize *)
          uty.uty_pair <- Lazy_some (c_head, uty_tail);
          (* emit clauses *)
          let clauses = clauses_of_uty uty in
          c_head, uty_tail, clauses
        | Lazy_some (hd,tl) ->
          hd, tl, [] (* already expanded *)
      *)

    let depth_of_value (v:value): int = match v with
      | V_true | V_false -> 0
      | V_dom_elt _ -> assert false (* TODO *)
      | V_cstor (_, l) ->
        List.fold_left
          (fun cur_max th -> match Thunk.view th with
             | T_const c -> max cur_max (Cst_undef.depth c + 1)
             | _ -> cur_max)
          0 l

    (* build clause(s) that explains that [c] must be one of its
       cases *)
    let clauses_of_cases (c:cst_undef) (l:value list): Clause.t list =
      let guard_parent =
        List.map
          (fun (lazy lits) -> lits)
          !(c.cst_exist_conds)
      in
      (* lits with the corresponding depth guard, if any *)
      let lits =
        List.map
          (fun rhs ->
             let lit = Lit.cst_choice c rhs in
             let guard = match depth_of_value rhs with
               | 0 -> None
               | depth_rhs ->
                 assert (depth_rhs > 0);
                 let _, guard = Iterative_deepening.lit_max_smaller_than depth_rhs in
                 Some guard
             in
             lit, guard)
          l
      in
      (* NOTE: still needed? *)
      let cs_possible_depth = [] in
      (*
      (* if all cases go over the depth limit, then we must revert the
         choice of [parent] *)
      let all_need_guard = List.for_all (fun (_,g) -> CCOpt.is_some g) lits in
      let cs_possible_depth = match lit_guard, guard_parent, all_need_guard with
        | _, [], true -> assert false (* depth 0 ?! *)
        | Some guard, _::_, true ->
          (* each [parent=parent_case] that leads to [c] is incompatible
             with [guard] because it would use too deep constants *)
          List.map
            (fun parent ->
               [Lit.neg guard; Lit.neg parent] |> Clause.make)
            guard_parent
        | _ -> []
      in
      *)
      (* at least one case. We only enforce that if the
         parent constant has the proper case *)
      let cs_choose : Clause.t list =
        List.map fst lits
        |> imply_product guard_parent
        |> List.map Clause.make
      (* at most one case *)
      and cs_once : Clause.t list =
        CCList.diagonal lits
        |> List.map
          (fun ((l1,_),(l2,_)) -> Clause.make [Lit.neg l1; Lit.neg l2])
      (* enforce depth limit *)
      and cs_limit : Clause.t list =
        CCList.flat_map
          (fun (lit,guard_opt) ->
             match guard_opt with
               | Some guard ->
                 (* if [lit], then [not (depth <= max_depth_rhs-1)] *)
                 [Clause.make [ Lit.neg lit; Lit.neg guard ]]
               | _ -> [])
          lits
      in
      cs_possible_depth @ cs_limit @ cs_choose @ cs_once

    (* build the disjunction [l] of cases for [info]. Might expand other
       objects, such as uninterpreted slices. *)
    let expand_cases (cst:cst_undef) : value list * Clause.t list  =
      assert (cst.cst_cases = Lazy_none);
      (* make a sub-constant with given type *)
      let mk_sub_cst ?slice ?exist_if ~parent ~depth ty_arg =
        let basename = Ty.mangle ty_arg in
        new_cst_ ?slice ?exist_if basename ty_arg ~parent ~depth
      in
      (* table of already built constants, by type *)
      let memo : (cst_undef * cst_exist_conds) list Ty.Tbl.t = Ty.Tbl.create 16 in
      (* get or create a constant that has this type *)
      let get_or_create_cst
          ~(parent:cst_undef) ~(used:cst_undef list ref) ~depth ty_arg
          : cst_undef * cst_exist_conds =
        let usable =
          Ty.Tbl.get_or ~or_:[] memo ty_arg
          |> List.filter
            (fun (c',_) -> not (List.exists (Cst_undef.equal c') !used))
        in
        match usable with
          | [] ->
            (* make a new constant and remember it *)
            let plist = ref [] in
            let cst = mk_sub_cst ~exist_if:plist ~parent ~depth ty_arg in
            Ty.Tbl.add_list memo ty_arg (cst,plist);
            used := cst :: !used; (* cannot use it in the same case *)
            cst, plist
          | (cst,plist) :: _ ->
            (* [cst] has the proper type, and is not used yet *)
            used := cst :: !used;
            cst, plist
      in
      (* expand constant depending on its type *)
      let by_ty, other_clauses = match Ty.view cst.cst_ty with
        | Ty_atomic (_, Ty_data cstors) ->
          (* datatype: refine by picking the head constructor *)
          List.map
            (fun (lazy (c_id, c_ty)) ->
               let rec case = lazy (
                 let ty_args, _ = Ty.unfold c_ty in
                 (* elements of [memo] already used when generating the
                    arguments of this particular case,
                    so we do not use a constant twice *)
                 let used = ref [] in
                 let args =
                   List.map
                     (fun ty_arg ->
                        (* depth increases linearly in the number of arguments *)
                        let depth = cst.cst_depth + List.length ty_args in
                        assert (depth > cst.cst_depth);
                        let c, plist =
                          get_or_create_cst ty_arg ~parent:cst ~used ~depth
                        in
                        let cond = lazy (Lit.cst_choice cst (Lazy.force case)) in
                        plist := cond :: !plist;
                        Thunk.cst_undef c)
                     ty_args
                 in
                 Value.cstor c_id args
               ) in
               Lazy.force case)
            cstors, []
        | Ty_atomic (_, Ty_uninterpreted _uty_root) ->
          assert false
          (* TODO
          assert (Ty.equal ty (Lazy.force uty_root.uty_self));
          (* find the proper uninterpreted slice *)
          let uty = match cst.cst_kind with
            | Cst_undef (_, _, Some u) -> u
            | Cst_undef ({ty_cell=Atomic (_,Uninterpreted uty); _}, _, _) -> uty
            | _ -> assert false
          in
          (* first, expand slice if required *)
          let c_head, uty_tail, cs = expand_uninterpreted_slice uty in
          (* two cases: either [c_head], or some new, deeper constant somewhere
             in the slice [uty_tail] *)
          let case1 = Term.const c_head in
          let case2 =
            let cond = lazy (Lit.uty_choice_nonempty uty) in
            let plist = ref [cond] in
            (* [cst = cst'], but [cst'] is deeper and belongs to the next slice *)
            let depth = info.cst_depth+1 in
            let cst' =
              mk_sub_cst ty ~slice:uty_tail ~exist_if:plist ~parent:cst ~depth
            in
            Term.const cst'
          in
          (* additional clause to specify that [is_empty uty_tail => cst = case1] *)
          let c_not_empty =
            [Lit.neg (Lit.uty_choice_empty uty_tail); Lit.cst_choice cst case1]
            |> Clause.make
          in
          [case1; case2], c_not_empty :: cs
             *)
        | Ty_arrow (_ty_arg, _ty_ret) ->
          assert false
          (* TODO: add a "dynamic function" case to values?
          (* synthesize a function [fun x:ty_arg. body]
             where [body] will destruct [x] depending on its type,
             or [fun _:ty_arg. constant] *)
          let the_param = Term.db (DB.make 0 ty_arg) in
          let rec body = lazy (
            (* only one parent in any case *)
            let exist_if = ref [lazy (Lit.cst_choice cst (Lazy.force fun_destruct))] in
            match Ty.view ty_arg with
            | Prop ->
              (* make a test on [the_param] *)
              let depth = info.cst_depth+1 in
              let then_ = mk_sub_cst ty_ret ~depth ~parent:cst ~exist_if |> Term.const in
              let else_ = mk_sub_cst ty_ret ~depth ~parent:cst ~exist_if |> Term.const in
              Term.if_ the_param then_ else_
            | Atomic (_, Data cstors) ->
              (* we cannot enumerate all functions on datatypes *)
              info.cst_complete <- false;
              (* match without recursion on some parameter *)
              let m =
                cstors
                |> List.map
                  (fun (lazy cstor) ->
                     let ty_cstor_args, _ =
                       Cst_undef.ty cstor |> Ty.unfold
                     in
                     let n_ty_args = List.length ty_cstor_args in
                     (* build a function over the cstor arguments *)
                     let ty_sub_f = Ty.arrow_l ty_cstor_args ty_ret in
                     let depth = info.cst_depth+1 in
                     let sub_f =
                       mk_sub_cst ty_sub_f ~parent:cst ~exist_if ~depth
                     in
                     (* apply [sub_f] to the cstor's arguments *)
                     let sub_params =
                       List.mapi
                         (fun i ty_arg ->
                            let db_arg = DB.make (n_ty_args-i-1) ty_arg in
                            Term.db db_arg)
                         ty_cstor_args
                     in
                     let rhs = Term.app_cst sub_f sub_params in
                     cstor.cst_id, (ty_cstor_args, rhs)
                  )
                |> ID.Map.of_list
              in
              Term.match_ the_param m
            | Atomic (_, Uninterpreted _) ->
              (* by case. We make a flat table from values to new
                 meta-variables of type [ty_ret] *)
              let switch_make_new () =
                let depth = info.cst_depth+1 in
                let sub = mk_sub_cst ty_ret ~depth ~parent:cst ~exist_if in
                Term.const sub
              in
              let m = {
                switch_tbl=ID.Tbl.create 16;
                switch_ty_arg=ty_arg;
                switch_ty_ret=ty_ret;
                switch_cst=cst;
                switch_id=new_switch_id_();
                switch_make_new;
              } in
              Term.switch the_param m
            | Arrow _ ->
              assert false (* TODO: support HO? *)
          )
          and fun_destruct =
            lazy (Term.fun_ ty_arg (Lazy.force body))
          (* constant function that does not look at input *)
          and body_const = lazy (
            let exist_if = ref [lazy (Lit.cst_choice cst (Lazy.force fun_const))] in
            (* only one parent in any case *)
            let depth = info.cst_depth+1 in
            let c' = mk_sub_cst ty_ret ~depth ~parent:cst ~exist_if in
            Term.const c'
          )
          and fun_const =
            lazy (Term.fun_ ty_arg (Lazy.force body_const))
          in
          [Lazy.force fun_destruct; Lazy.force fun_const], []
          *)
        | Ty_prop ->
          (* simply try true/false *)
          [Value.true_; Value.false_], []
      in
      (* build clauses *)
      let case_clauses = clauses_of_cases cst by_ty in
      by_ty, List.rev_append other_clauses case_clauses

    (* expand the given constant so that, later, it will be
       assigned a value by the SAT solver *)
    let expand_cst (c:cst_undef): unit =
      let depth = c.cst_depth in
      (* check whether [c] is expanded *)
      begin match c.cst_cases with
        | Lazy_none ->
          (* [c] is blocking, not too deep, but not expanded *)
          let l, clauses = expand_cases c in
          Log.debugf 2
            (fun k->k "(@[<1>expand_cst@ @[%a@]@ :into (@[%a@])@ :depth %d@])"
                Cst_undef.pp c (Utils.pp_list Value.pp) l depth);
          c.cst_cases <- Lazy_some l;
          incr stat_num_cst_expanded;
          Clause.push_new_l clauses
        | Lazy_some _ -> ()
      end

    let expand_uty (uty:ty_uninterpreted_slice): unit =
      let depth = uty.uty_offset in
      (* check whether [c] is expanded *)
      begin match uty.uty_pair with
        | Lazy_none ->
          (* [uty] is blocking, not too deep, but not expanded *)
          let c_head, uty_tail, clauses = expand_uninterpreted_slice uty in
          Log.debugf 2
            (fun k->k
                "(@[<1>expand_uty@ @[%a@]@ :into (@[%a ++@ %a@])@ :depth %d@])"
                pp_uty uty Cst_undef.pp c_head pp_uty uty_tail depth);
          uty.uty_pair <- Lazy_some (c_head, uty_tail);
          incr stat_num_uty_expanded;
          Clause.push_new_l clauses
        | Lazy_some _ -> ()
      end
  end

  let pp_dep_full out = function
    | Dep_cst c ->
      let nf = match c.cst_cur_case with
        | None -> Thunk.cst_undef c
        | Some (_, v) -> Thunk.value v
      in
      fpf out
        "(@[%a@ nf:%a@ :expanded %B@])"
        Cst_undef.pp c Thunk.pp nf
        (c.cst_cases <> Lazy_none)
    | Dep_uty uty ->
      fpf out
        "(@[%a@ :expanded %B@])"
        pp_uty uty (uty.uty_pair<>Lazy_none)

  (* for each explanation [e1, e2, ..., en] build the guard
         [e1 & e2 & ... & en => …], that is, the clause
         [not e1 | not e2 | ... | not en] *)
  let clause_guard_of_exp_ (e:explanation): Lit.t list Sequence.t =
    let l = Explanation.to_lists e in
    Sequence.map
      (fun e ->
         List.map Lit.neg e (* this is a guard! *)
         |> CCList.sort_uniq ~cmp:Lit.compare)
      l

  (** {2 Reduction to Normal Form} *)
  module Reduce = struct

    let cycle_check_l ~sub:_ _ = false
    (* TODO: not needed? or only on constants?
    let cycle_check_tbl : unit Term.Tbl.t = Term.Tbl.create 32

    (* [cycle_check sub into] checks whether [sub] occurs in [into] under
       a non-empty path traversing only constructors. *)
    let cycle_check_l ~(sub:term) (l:term list): bool =
      let tbl_ = cycle_check_tbl in
      Term.Tbl.clear tbl_;
      let rec aux u =
        Term.equal sub u
        ||
        begin
          if Term.Tbl.mem tbl_ u then false
          else (
            Term.Tbl.add tbl_ u ();
            match Term.as_cstor_app u with
              | None -> false
              | Some (_, _, l) -> List.exists aux l
          )
        end
      in
      List.exists aux l

    let cycle_check ~(sub:term) (into:term): bool =
      cycle_check_l ~sub [into]
       *)

    module E = Explanation

    let rec compute_nf (t:thunk): explanation * thunk =
      begin match Thunk.view t with
        | T_value _ -> E.empty, t
        | T_const c ->
          begin match c.cst_cur_case with
            | None -> E.empty, t
            | Some (e, v) -> e, Thunk.value v
          end
        | T_check_assign (c, v) ->
          begin match c.cst_cur_case with
            | None -> E.empty, t
            | Some (e, v') ->
              if Value.equal_shallow v v'
              then e, Thunk.true_
              else e, Thunk.false_
          end
        | T_par_and (a, e_a, b, e_b) ->
          let e_a, a' = compute_nf_add e_a a in
          let e_b, b' = compute_nf_add e_b b in
          begin match Thunk.view a', Thunk.view b' with
            | T_value V_true, T_value V_true ->
              E.append e_a e_b, Thunk.true_
            | T_value V_false, T_value V_false ->
              E.append e_a e_b, Thunk.false_
            | T_value V_false, _ ->
              e_a, Thunk.false_
            | _, T_value V_false ->
              e_b, Thunk.false_
            | T_value _, _ | _, T_value _ -> assert false
            | _ ->
              (* no reduction yet *)
              let t' =
                if a==a' && b==b' then t else Thunk.and_par a' e_a b' e_b
              in
              E.empty, t'
          end
        | T_seq_and (a,b) ->
          let e_a, a' = compute_nf a in
          begin match Thunk.view a' with
            | T_value V_true -> compute_nf_add e_a b
            | T_value V_false -> e_a, Thunk.false_
            | _ ->
              e_a, (if a==a' then t else Thunk.and_seq a' b)
          end
        | T_not u ->
          let e_u, u' = compute_nf u in
          begin match Thunk.view u' with
            | T_value V_true -> e_u, Thunk.false_
            | T_value V_false -> e_u, Thunk.true_
            | T_value _ -> assert false
            | _ ->
              e_u, (if u==u' then t else Thunk.not_ u')
          end
        | T_equiv (a,b) ->
          let e_a, a' = compute_nf a in
          let e_b, b' = compute_nf b in
          let e_ab = Explanation.append e_a e_b in
          let default() = if a==a' && b==b' then t else Thunk.equiv a' b' in
          begin match Thunk.view a', Thunk.view b' with
            | T_value V_true, T_value V_true
            | T_value V_false, T_value V_false -> e_ab, Thunk.true_
            | T_value V_true, T_value V_false
            | T_value V_false, T_value V_true -> e_ab, Thunk.false_
            | _ ->  e_ab, default()
          end
        | T_eq (a,b) ->
          compute_nf_eq t a b
        | T_ref {contents=(e_a, a)} when Thunk.is_value a ->
          e_a, a (* optim for values *)
        | T_ref ({contents=(e_a, a)} as t_ref) ->
          let e_a, a' = compute_nf_add e_a a in
          begin match Thunk.view a' with
            | T_value _ -> e_a, a' (* return value *)
            | _ ->
              (* evaluation stays blocked, but makes some progress *)
              if a != a' then (
                Backtrack.push_set_nf_ t_ref;
                t_ref := (e_a, a');
              );
              E.empty, t (* not a value yet, continue sharing computation *)
          end
        | T_lazy (p, env) ->
          (* start execution of [p] in environment [env] *)
          compute_nf_prgm E.empty p env
        | T_suspend (p, i, env, e) ->
          let t_i = DB_env.get_exn i env in
          let e, t_i' = compute_nf_add e t_i in
          let env' = if t_i==t_i' then env else DB_env.set_ i t_i' env in
          if Thunk.is_value t_i'
          then compute_nf_prgm e p env'
          else (
            (* do not return yet *)
            let new_t = if env==env' then t else Thunk.suspend p i env' e in
            E.empty, new_t
          )
      end

    (* compute nf of [t], append [e] to the explanation *)
    and compute_nf_add (e : explanation) (t:thunk) : explanation * thunk =
      let e', t' = compute_nf t in
      Explanation.append e e', t'

    (* compute the result of running this program in this environment *)
    and compute_nf_prgm (e: explanation) (p:prgm) (env:eval_env): explanation * thunk =
      begin match Prgm.view p with
        | P_return c ->
          (* eval [c] in current environment *)
          let th = Thunk.eval_const env c in
          compute_nf_add e th
        | P_let (Let_eager, a, b) ->
          (* evaluate [a] right now and push it on the stack *)
          let e, th_a = compute_nf_prgm e a env in
          let env = DB_env.push th_a env in
          compute_nf_prgm e b env
        | P_let (Let_lazy, a, b) ->
          (* push a lazy thunk for computing [a] onto the stack, then eval [b] *)
          let th_a = Thunk.ref_ (Thunk.lazy_ a env) in
          let env = DB_env.push th_a env in
          compute_nf_prgm e b env
        | P_lazy (lazy p_cont) -> compute_nf_prgm e p_cont env
        | P_match (v, m) ->
          let th = DB_env.get_exn v env in
          let e, th' = compute_nf_add e th in
          let env' = if th==th' then env else DB_env.set_ v th' env in
          begin match Thunk.view th with
            | T_value (V_cstor (c, args)) ->
              begin match ID.Map.get c.cstor_id m with
                | None -> assert false
                | Some (n, p_cont) ->
                  (* follow [p_cont] *)
                  assert (n = List.length args);
                  let env' = DB_env.push_l args env' in
                  compute_nf_prgm e p_cont env'
              end
            | T_value _ -> assert false
            | _ ->
              (* suspend, waiting for [th] to become a value *)
              E.empty, Thunk.suspend p v env' e
          end
        | P_if (v,a,b) ->
          let th = DB_env.get_exn v env in
          let e, th' = compute_nf_add e th in
          let env' = if th==th' then env else DB_env.set_ v th' env in
          begin match Thunk.view th with
            | T_value V_true -> compute_nf_prgm e a env'
            | T_value V_false -> compute_nf_prgm e b env'
            | T_value _ -> assert false
            | _ ->
              (* suspend, waiting for [th] to become a value *)
              E.empty, Thunk.suspend p v env' e
          end
        | P_equiv (a,b) ->
          let th = Thunk.equiv (DB_env.get_exn a env) (DB_env.get_exn b env) in
          compute_nf_add e th
        | P_eq (a,b) ->
          let th = Thunk.eq (DB_env.get_exn a env) (DB_env.get_exn b env) in
          compute_nf_add e th
        | P_and (a,b) ->
          let th = Thunk.and_ (DB_env.get_exn a env) (DB_env.get_exn b env) in
          compute_nf_add e th
        | P_not a ->
          compute_nf_add e (DB_env.get_exn a env)
        | P_call (p_cont, []) -> compute_nf_prgm e p_cont DB_env.empty
        | P_call (p_cont, args) ->
          (* new stack for args, then jump *)
          (* TODO: do not exactly wrap into [lazy]. Instead, we should have
             a "cheap_eval" function that keeps values as they are,
             dereferences in the environment, but do not do match/if or
             function calls (in this case, it uses [lazy]). This makes
             passing values cheap, and other arguments reasonable. *)
          let args = List.map (fun p_a -> Thunk.lazy_ p_a env) args in
          let env = DB_env.push_l args DB_env.empty in
          compute_nf_prgm e p_cont env
      end

    and compute_nf_eq eq_ab a b =
      let e_a, a' = compute_nf a in
      let e_b, b' = compute_nf b in
      let e_ab = Explanation.append e_a e_b in
      let default() =
        if a==a' && b==b' then eq_ab else Thunk.eq a' b'
      in
      begin match Thunk.as_unif a', Thunk.as_unif b' with
        | Thunk.Unif_cstor (c1,l1), Thunk.Unif_cstor (c2,l2) ->
          if not (ID.equal c1.cstor_id c2.cstor_id)
          then
            (* [c1 ... = c2 ...] --> false, as distinct constructors
               can never be equal *)
            e_ab, Thunk.false_
          else if ID.equal c1.cstor_id c2.cstor_id
               && List.length l1 = List.length l2
               && List.length l1 = List.length (fst (Ty.unfold c1.cstor_ty))
          then (
            (* same constructor, fully applied -> injectivity:
               arguments are pairwise equal.
               We need to evaluate the arguments further (e.g.
               if they start with constructors) *)
            List.map2 Thunk.eq l1 l2
            |> Thunk.and_l
            |> compute_nf_add e_ab
          )
          else e_ab, default()
        | Thunk.Unif_cstor (_, l), _ when cycle_check_l ~sub:b' l ->
          (* acyclicity rule *)
          e_ab, Thunk.false_
        | _, Thunk.Unif_cstor (_, l) when cycle_check_l ~sub:a' l ->
          e_ab, Thunk.false_
        | Thunk.Unif_dom_elt c1, Thunk.Unif_dom_elt c2 ->
          (* domain elements: they are all distinct *)
          assert (Ty.equal c1.dom_elt_ty c2.dom_elt_ty);
          if ID.equal c1.dom_elt_id c2.dom_elt_id
          then e_ab, Thunk.true_
          else e_ab, Thunk.false_
        | Thunk.Unif_cstor (cstor, args), Thunk.Unif_cst c
        | Thunk.Unif_cst c, Thunk.Unif_cstor (cstor, args) ->
          (* expand right now, so we can get a list of cases *)
          Expand.expand_cst c;
          begin match c.cst_cases with
            | Lazy_none -> assert false
            | Lazy_some cases ->
              assert c.cst_complete;
              (* unification: use the literal [c := case] for
                 the [case in cases] that matches [cstor].
                 Reduce to [:= c case & case.i=args.i] *)
              let case, sub_args =
                CCList.find_map
                  (fun v -> match v with
                     | V_cstor (cstor', args) ->
                       if ID.equal cstor.cstor_id cstor'.cstor_id
                       then Some (v, args)
                       else None
                     | _ -> assert false)
                  cases
                |> (function | Some x->x | None -> assert false)
              in
              assert (List.length sub_args = List.length args);
              let check_case = Thunk.check_assign c case in
              let check_subs =
                List.map2 Thunk.eq args sub_args |> Thunk.and_l
              in
              incr stat_num_unif;
              (* eager "and", as a "if" *)
              let new_thunk = Thunk.and_seq check_case check_subs in
              compute_nf_add e_ab new_thunk
          end
        | Thunk.Unif_dom_elt dom_elt, Thunk.Unif_cst c
        | Thunk.Unif_cst c, Thunk.Unif_dom_elt dom_elt ->
          assert false
        (* TODO
           let dom_elt_offset = uty_dom_elt.uty_offset in
           (* we know that [uty] is expanded deep enough that [dom_elt]
           exists, so we can simply reduce [?c = dom_elt_n] into
           [¬empty(uty[0:]) & .. & ¬empty(uty[:n]) & ?c := dom_elt_n] *)
           let traverse e_c c uty = match uty.uty_pair with
           | Lazy_none ->
            (* we are too deep in [uty], cannot hold *)
            assert (dom_elt_offset < uty.uty_offset);
            Explanation.empty, Thunk.false_
           | Lazy_some _ when dom_elt_offset < uty.uty_offset ->
            (* we are too deep in [uty], cannot hold *)
            Explanation.empty, Thunk.false_
           | Lazy_some (dom_elt', _) ->
            Expand.expand_cst c;
            let check_uty = Thunk.check_empty_uty uty |> Thunk.not_ in
            if Cst_undef.equal dom_elt dom_elt'
            then (
              incr stat_num_unif;
              (* check assignment *)
              Thunk.and_eager check_uty
                (Thunk.check_assign c (Thunk.const dom_elt))
              |> compute_nf_add e_c
            ) else (
              begin match c.cst_kind with
                | Cst_undef (_, {cst_cases=Lazy_some cases; _}, _) ->
                  (* [c=dom_elt' OR c=c'] *)
                  let c' = match cases with
                    | [a;b] ->
                      begin match Thunk.as_cst_undef a, Thunk.as_cst_undef b with
                        | Some (c',_,_,_), _ | _, Some (c',_,_,_) -> c'
                        | _ -> assert false
                      end
                    | _ -> assert false
                  in
                  assert (c != c');
                  Thunk.and_eager
                    check_uty
                    (Thunk.and_
                       (Thunk.check_assign c (Thunk.const c'))
                       (Thunk.eq (Thunk.const c') (Thunk.const dom_elt)))
                  |> compute_nf_add e_c
                | Cst_undef (_, {cst_cases=Lazy_none; _}, _) ->
                  (* blocked: could not expand *)
                  e_c, Thunk.eq (Thunk.const c) (Thunk.const dom_elt)
                | _ -> assert false
              end
            )
           in
           let uty_root = match c.cst_kind, uty_dom_elt.uty_self with
           | Cst_undef (_, _, Some uty), _ -> uty
           | _, lazy {ty_cell=Atomic (_, Uninterpreted uty); _} -> uty
           | _ -> assert false
           in
           traverse e_ab c uty_root
        *)
        | _ -> e_ab, default()
      end

    (* follow the "normal form" pointer *)
    let compute_nf_lit (t:lit): explanation * thunk = match t.lit_view with
      | Lit_atom (_, th) ->
        let e, th = compute_nf th in
        let th = if Lit.sign t then th else Thunk.not_ th in
        e, th
      | _ -> assert false
  end

  (** {2 A literal asserted to SAT}

      A set of terms that must be evaluated (and their value, propagated)
      in the current partial model. *)

  module Top_terms : sig
    type t = private lit

    val of_term : thunk -> t
    val to_lit : t -> Lit.t
    val pp : t Fmt.printer
    val watch : thunk -> unit
    val update : t -> unit
    (** re-check value, maybe propagate *)

    val size : unit -> int
    val to_seq : t Sequence.t
    val update_all : unit -> unit (** update all top terms *)
  end = struct
    type t = lit

    let to_lit t = t
    let pp = Lit.pp
    let of_term t = Lit.atom (Thunk.ref_ t) (* memoization *)
    let abs (t:t) : t = Lit.abs t

    (* clauses for [e => l] *)
    let clause_imply (l:lit) (e:explanation): Clause.t Sequence.t =
      clause_guard_of_exp_ e
      |> Sequence.map
        (fun guard -> l :: guard |> Clause.make)

    let propagate_lit_ (t:lit) (e:explanation): unit =
      let cs = clause_imply t e |> Sequence.to_rev_list in
      Log.debugf 4
        (fun k->k
            "(@[<hv1>@{<green>propagate_lit@}@ %a@ clauses: (@[%a@])@])"
            Lit.pp t (Utils.pp_list Clause.pp) cs);
      incr stat_num_propagations;
      Clause.push_new_l cs;
      ()

    let expand_cst_ (c:cst_undef) : unit =
      Log.debugf 2 (fun k->k "(@[<1>watch_cst@ %a@])" Cst_undef.pp c);
      Expand.expand_cst c;
      ()

    let expand_uty_ (uty:ty_uninterpreted_slice) : unit =
      Log.debugf 2 (fun k->k "(@[<1>watch_uty@ %a@])" pp_uty uty);
      Expand.expand_uty uty;
      ()

    let expand_dep (d:thunk_dep) : unit = match d with
      | Dep_cst c -> expand_cst_ c
      | Dep_uty uty -> expand_uty_ uty

    (* evaluate [t] in current partial model, and expand the constants
       that block it *)
    let update (t:t): unit =
      let e, new_t = Reduce.compute_nf_lit t in
      (* if [new_t = true/false], propagate literal *)
      begin match Thunk.view new_t with
        | T_value V_true -> propagate_lit_ t e
        | T_value V_false -> propagate_lit_ (Lit.neg t) e
        | _ ->
          Log.debugf 4
            (fun k->k
                "(@[<1>update@ %a@ @[<1>:normal_form@ %a@]@ \
                 :deps (@[%a@])@ :exp @[<hv>%a@]@])"
                pp t Thunk.pp new_t
                (Utils.pp_list pp_dep) (Thunk.deps new_t)
                Explanation.pp e);
          List.iter expand_dep (Thunk.deps new_t);
      end;
      ()

    (* NOTE: we use a list because it's lightweight, fast to iterate
       on, and we only add elements in it at the beginning *)
    let top_ : t list ref = ref []

    let mem_top_ (t:t): bool =
      List.exists (fun t' -> Lit.equal (abs t) (abs t')) !top_

    let watch (t:thunk) =
      let lit = of_term t in
      if not (mem_top_ lit) then (
        Log.debugf 3
          (fun k->k "(@[<1>@{<green>watch_lit@}@ %a@])" pp lit);
        top_ := lit :: !top_;
        (* also ensure it is watched properly *)
        update lit;
      )

    let to_seq yield = List.iter yield !top_

    let size () = List.length !top_

    (* update all top terms (whose dependencies have been changed) *)
    let update_all () =
      to_seq
      |> Sequence.iter update
  end

  (** {2 Sat Solver} *)

  (* formulas for msat *)
  module M_expr
    : Msat.Formula_intf.S
      with type t = Lit.t
       and type proof = unit
  = struct
    include Lit
    type proof = unit (* TODO later *)
  end

  let print_progress () : unit =
    Printf.printf "\r[%.2f] depth %d | expanded %d | clauses %d | lemmas %d | lits %d%!"
      (get_time())
      (Iterative_deepening.current_depth() :> int)
      !stat_num_cst_expanded
      !stat_num_clause_push
      !stat_num_clause_tautology
      (Top_terms.size())

  (* TODO: find the proper code for "kill line" *)
  let flush_progress (): unit =
    Printf.printf "\r%-80d\r%!" 0

  (** {2 Toplevel Goals}

      List of toplevel goals to satisfy
  *)

  module Top_goals: sig
    val push : thunk  -> unit
    val to_seq : thunk Sequence.t
    val check: unit -> unit
  end = struct
    (* list of terms to fully evaluate *)
    let toplevel_goals_ : lit list ref = ref []

    (* add [t] to the set of terms that must be evaluated *)
    let push (t:thunk): unit =
      let lit = Lit.atom t in
      toplevel_goals_ := lit :: !toplevel_goals_;
      ()

    let to_seq_ k = List.iter k !toplevel_goals_

    let to_seq =
      to_seq_
      |> Sequence.map
        (fun lit ->
           let t, b = Lit.as_atom_exn lit in
           if b then t else Thunk.not_ t)

    (* check that this term fully evaluates to [true] *)
    let is_true_ (t:lit): bool =
      let _, t' = Reduce.compute_nf_lit t in
      match Thunk.view t' with
        | T_value V_true -> true
        | _ -> false

    let check () =
      if not (List.for_all is_true_ !toplevel_goals_)
      then (
        if Config.progress then flush_progress();
        Log.debugf 1
          (fun k->
             let pp_dep out = function
               | Dep_cst c ->
                 let _, nf = Reduce.compute_nf (Thunk.cst_undef c) in
                 fpf out
                   "(@[%a@ nf:%a@ :expanded %B@])"
                   Cst_undef.pp c Thunk.pp nf
                   (c.cst_cases <> Lazy_none)
               | Dep_uty uty ->
                 fpf out
                   "(@[%a@ :expanded %B@])"
                   pp_uty uty (uty.uty_pair<>Lazy_none)
             in
             let pp_lit out l =
               let e, nf = Reduce.compute_nf_lit l in
               fpf out
                 "(@[<hv1>%a@ nf: %a@ exp: %a@ deps: (@[<hv>%a@])@])"
                 Lit.pp l Thunk.pp nf Explanation.pp e
                 (Utils.pp_list pp_dep) (Thunk.deps nf)
             in
             k "(@[<hv1>status_watched_lit@ (@[<v>%a@])@])"
               (Utils.pp_list pp_lit) !toplevel_goals_);
        assert false;
      )
  end

  (* the "theory" part: propagations *)
  module M_th : sig
    val set_active: bool -> unit
    include Msat.Theory_intf.S
      with type formula = M_expr.t
       and type proof = M_expr.proof
  end = struct
    type formula = M_expr.t
    type proof = M_expr.proof

    type level = Backtrack.level

    let dummy = Backtrack.dummy_level

    (* if true, perform theory propagation; otherwise do nothing *)
    let active = ref true
    let set_active b = active := b

    (* increment and return level *)
    let current_level () =
      Backtrack.push_level ();
      Backtrack.cur_level ()

    let backtrack = Backtrack.backtrack

    (* push clauses from {!lemma_queue} into the slice *)
    let flush_new_clauses_into_slice slice =
      while not (Queue.is_empty Clause.lemma_queue) do
        let c = Queue.pop Clause.lemma_queue in
        Log.debugf 5 (fun k->k "(@[<2>push_lemma@ %a@])" Clause.pp c);
        let lits = Clause.lits c in
        slice.TI.push lits ();
      done

    (* assert [c := v], or conflict *)
    let assert_choice (c:cst_undef) (v:value) : unit =
      begin match c.cst_cur_case with
        | None ->
          let e = Explanation.return (Lit.cst_choice c v) in
          Backtrack.push_set_cst_case_ c;
          c.cst_cur_case <- Some (e, v);
        | Some (_,v') ->
          Log.debugf 1
            (fun k->k "(@[<hv1>assert_choice %a@ :to %a@ :cur %a@])"
                Cst_undef.pp c Value.pp v Value.pp v');
          assert (Value.equal_shallow v v');
      end

    let assert_uty
        (uty:ty_uninterpreted_slice)
        (status:ty_uninterpreted_status)
      : unit =
      Log.debugf 2
        (fun k->k "(@[<1>@{<green>assume_uty@}@ @[%a@] %a@])"
        pp_uty uty pp_uty_status status);
      begin match uty.uty_status with
        | None ->
          let e = Explanation.return (Lit.uty_choice_status uty status) in
          Backtrack.push_uty_status uty;
          uty.uty_status <- Some (e, status);
        | Some (_, ((Uty_empty | Uty_nonempty) as s)) ->
          Log.debugf 1
            (fun k->k "(@[<hv1>assert_uty %a@ :to %a@ :cur %a@])"
                pp_uty uty pp_uty_status status pp_uty_status s);
          assert (s = status)
      end

    (* handle a literal assumed by the SAT solver *)
    let assume_lit (lit:Lit.t) : unit =
      Log.debugf 2
        (fun k->k "(@[<1>@{<green>assume_lit@}@ @[%a@]@])" Lit.pp lit);
      (* check consistency first *)
      begin match Lit.view lit with
        | Lit_fresh _ -> ()
        | Lit_atom _ ->
          let e, t' = Reduce.compute_nf_lit lit in
          begin match Thunk.view t' with
            | T_value V_true -> ()
            | T_value V_false ->
              (* conflict! *)
              let cs =
                clause_guard_of_exp_ e
                |> Sequence.map
                  (fun guard -> Lit.neg lit :: guard |> Clause.make)
              in
              Sequence.iter Clause.push_new cs
            | _ -> ()
          end
        | Lit_assign(c, t) ->
          if Lit.sign lit then assert_choice c t
        | Lit_uty_empty uty ->
          let status = if Lit.sign lit then Uty_empty else Uty_nonempty in
          assert_uty uty status
      end

    (* propagation from the bool solver *)
    let assume slice =
      let start = slice.TI.start in
      assert (slice.TI.length > 0);
      (* do the propagations in a local frame *)
      if Config.progress then print_progress();
      (* first, empty the tautology queue *)
      flush_new_clauses_into_slice slice;
      for i = start to start + slice.TI.length - 1 do
        let lit = slice.TI.get i in
        assume_lit lit;
      done;
      if !active then (
        Top_terms.update_all();
      );
      flush_new_clauses_into_slice slice;
      TI.Sat

    (* TODO: move checking code from Main_loop here? *)
    let if_sat _slice = TI.Sat
  end

  module M = Msat.Solver.Make(M_expr)(M_th)(struct end)

  (* push one clause into [M], in the current level (not a lemma but
     an axiom) *)
  let push_clause (c:Clause.t): unit =
    Log.debugf 2 (fun k->k "(@[<1>push_clause@ @[%a@]@])" Clause.pp c);
    (* reduce to normal form the literals, ensure they
         are added to the proper constant watchlist(s) *)
    Clause.to_seq c
      |> Sequence.filter_map Lit.as_atom
      |> Sequence.map fst
      |> Sequence.iter Top_terms.watch;
    incr stat_num_clause_push;
    M.assume [Clause.lits c]

  (** {2 Conversion} *)

  (* list of constants we are interested in *)
  let model_support_ : Cst_undef.t list ref = ref []

  let model_env_ : Ast.env ref = ref Ast.env_empty

  (* list of (uninterpreted) types we are interested in *)
  let model_utys : Ty.t list ref = ref []

  let add_cst_support_ (c:cst_undef): unit =
    CCList.Ref.push model_support_ c

  let add_ty_support_ (ty:Ty.t): unit =
    CCList.Ref.push model_utys ty

  module Conv = struct
    (* for converting Ast.Ty into Ty *)
    let ty_tbl_ : Ty.t lazy_t ID.Tbl.t = ID.Tbl.create 16

    type decl_ty_entry =
      | Decl_cst_undef of cst_undef
      | Decl_cstor of cstor

    (* for converting constants *)
    let decl_ty_ : decl_ty_entry lazy_t ID.Tbl.t = ID.Tbl.create 16

    (* environment for variables *)
    type conv_env = {
      bindings: (prgm * int) ID.Map.t;
      (* set ofbound variables. int=depth at binding position (for shifting) *)
      depth: int;
      (* size of [bindings] *)
    }

    let empty_env : conv_env =
      {let_bound=ID.Map.empty; bound=ID.Map.empty; depth=0}

    let add_bound env v =
      { env with
        depth=env.depth+1;
        bound=ID.Map.add (Ast.Var.id v) env.depth env.bound }

    (* add [v := t] to bindings. Depth is not increment (there will be no binders) *)
    let add_let_bound env v t =
      { env with
        let_bound=ID.Map.add (Ast.Var.id v) (t,env.depth) env.let_bound }

    let find_env env v =
      let id = Ast.Var.id v in
      ID.Map.get id env.let_bound, ID.Map.get id env.bound

    let rec conv_ty (ty:Ast.Ty.t): Ty.t = match ty with
      | Ast.Ty.Prop -> Ty.prop
      | Ast.Ty.Const id ->
        begin try ID.Tbl.find ty_tbl_ id |> Lazy.force
          with Not_found -> errorf "type %a not in ty_tbl" ID.pp id
        end
      | Ast.Ty.Arrow (a,b) -> Ty.arrow (conv_ty a) (conv_ty b)

    (* TODO:
       translate terms into programs (with some additional fun
       that converts to values, to be used to return values more
       efficiently: when returning [cstor args], use the specialized
       fun to convert [args] into values, too).

       Most operations should be relatively straightforward. For the
       other (mostly values) we separate the computations
       and the resulting shape by introducing let-bindings.
       The function returning values should also return some lazy let bindings
       that will wrap the entire value. *)

    (* compilation to programs *)
    let rec term_to_prgm (env:conv_env) (t:Ast.term): prgm =
      begin match Ast.term_view t with
        | Ast.True -> Prgm.true_
        | Ast.False -> Prgm.false_
        | Ast.Const id ->
          begin match ID.Tbl.get decl_ty_ id with
            | Some (lazy (Decl_cst_undef c)) -> Prgm.const c
            | Some (lazy (Decl_cstor c)) -> Prgm.cstor0 c
            | None ->
              errorf "could not find constant `%a`" ID.pp id
          end
        | Ast.App (f, l) ->
          (* first, convert [l] *)
          let env', bindings =
            CCList.fold_map
              (fun env arg ->
                 let arg = term_to_prgm env arg in
                 (* let! introduce the argument *)
                 let v = ID.make "_" in
                 let env = add_bound env v in
                 env, (v, arg))
              env l
          in
          let args = List.map (fun (v,_) -> Prgm.var
          let res = match Ast.term_view f with
            | Ast.Const id when ID.Tbl.mem decl_ty_ id ->
              let lazy entry = ID.Tbl.find decl_ty_ id in
              begin match entry with
                | Decl_cstor c ->
                  Prgm.cstor c (List.map (fun (v,_) -> Prgm.var v)) bindings
                | _ -> Prgm.call (term_to_prgm env f)
                | Decl_cst_undef c ->
                  Prgm.call (Prgm.const c) (
              end

            | _ ->
              let f = conv_term_rec env f in
              let l = List.map (conv_term_rec env) bindings in
              Prgm.call f l
          end
        | Ast.Var v ->
          begin match find_env env v with
            | Some (t', depth_t'), _ ->
              assert (env.depth >= depth_t');
              let t' = Term.shift_db (env.depth - depth_t') t' in
              t'
            | None, Some d ->
              let ty = Ast.Var.ty v |> conv_ty in
              let level = env.depth - d - 1 in
              Term.db (DB.make level ty)
            | None, None -> errorf "could not find var `%a`" Ast.Var.pp v
          end
        | Ast.Fun (v,body) ->
          let env' = add_bound env v in
          let body = conv_term_rec env' body in
          let ty = Ast.Var.ty v |> conv_ty in
          Term.fun_ ty body
        | Ast.Forall (v,body) ->
          let env' = add_bound env v in
          let body = conv_term_rec env' body in
          let uty =
            let ty = Ast.Var.ty v |> conv_ty in
            match Ty.view ty with
              | Atomic (_, Uninterpreted uty) -> uty
              | _ -> errorf "forall: need to quantify on an uninterpreted type, not %a" Ty.pp ty
          in
          Term.forall uty body
        | Ast.Exists (v,body) ->
          let env' = add_bound env v in
          let body = conv_term_rec env' body in
          let uty =
            let ty = Ast.Var.ty v |> conv_ty in
            match Ty.view ty with
              | Atomic (_, Uninterpreted uty) -> uty
              | _ -> errorf "exists: need to quantify on an uninterpreted type, not %a" Ty.pp ty
          in
          Term.exists uty body
        | Ast.Mu (v,body) ->
          let env' = add_bound env v in
          let body = conv_term_rec env' body in
          Term.mu body
        | Ast.Match (u,m) ->
          let any_rhs_depends_vars = ref false in (* some RHS depends on matched arg? *)
          let m =
            ID.Map.map
              (fun (vars,rhs) ->
                 let n_vars = List.length vars in
                 let env', tys =
                   CCList.fold_map
                     (fun env v -> add_bound env v, Ast.Var.ty v |> conv_ty)
                     env vars
                 in
                 let rhs = conv_term_rec env' rhs in
                 let depends_on_vars =
                   Term.to_seq_depth rhs
                   |> Sequence.exists
                     (fun (t,k) -> match t.term_cell with
                        | DB db ->
                          DB.level db < n_vars + k (* [k]: number of intermediate binders *)
                        | _ -> false)
                 in
                 if depends_on_vars then any_rhs_depends_vars := true;
                 tys, rhs)
              m
          in
          (* optim: check whether all branches return the same term, that
             does not depend on matched variables *)
          (* TODO: do the closedness check during conversion, above *)
          let rhs_l =
            ID.Map.values m
            |> Sequence.map snd
            |> Sequence.to_rev_list
            |> CCList.Set.uniq ~eq:Term.equal
          in
          begin match rhs_l with
            | [x] when not (!any_rhs_depends_vars) ->
              (* every branch yields the same [x], which does not depend
                 on the argument: remove the match and return [x] instead *)
              x
            | _ ->
              let u = conv_term_rec env u in
              Term.match_ u m
          end
        | Ast.Switch _ ->
          errorf "cannot convert switch %a" Ast.pp_term t
        | Ast.Let (v,t,u) ->
          (* substitute on the fly *)
          let t = conv_term_rec env t in
          let env' = add_let_bound env v t in
          conv_term_rec env' u
        | Ast.If (a,b,c) ->
          let b = conv_term_rec env b in
          let c = conv_term_rec env c in
          (* optim: [if _ b b --> b] *)
          if Term.equal b c
          then b
          else Term.if_ (conv_term_rec env a) b c
        | Ast.Not t -> Term.not_ (conv_term_rec env t)
        | Ast.Binop (op,a,b) ->
          let a = conv_term_rec env a in
          let b = conv_term_rec env b in
          begin match op with
            | Ast.And -> Term.and_ a b
            | Ast.Or -> Term.or_ a b
            | Ast.Imply -> Term.imply a b
            | Ast.Eq -> Term.eq a b
          end
      end

    (* convert this term into a program constant, as much as possible.
       It also returns a new environment containing local bindings
       (an extension of the input env) *)
  and term_to_value (env:conv_env) (t:Ast.term): conv_env * prgm_const =
    begin match Ast.term_view t with
      | _ -> 
    end

    let rec conv_term_rec
        (env: conv_env)
        (t:Ast.term): term = match Ast.term_view t with
      | Ast.True -> Term.true_
      | Ast.False -> Term.false_
      | Ast.Const id ->
        begin
          try ID.Tbl.find decl_ty_ id |> Lazy.force |> Term.const
          with Not_found ->
            errorf "could not find constant `%a`" ID.pp id
        end
      | Ast.App (f, l) ->
        let f = conv_term_rec env f in
        let l = List.map (conv_term_rec env) l in
        Term.app f l
      | Ast.Var v ->
        begin match find_env env v with
          | Some (t', depth_t'), _ ->
            assert (env.depth >= depth_t');
            let t' = Term.shift_db (env.depth - depth_t') t' in
            t'
          | None, Some d ->
            let ty = Ast.Var.ty v |> conv_ty in
            let level = env.depth - d - 1 in
            Term.db (DB.make level ty)
          | None, None -> errorf "could not find var `%a`" Ast.Var.pp v
        end
      | Ast.Fun (v,body) ->
        let env' = add_bound env v in
        let body = conv_term_rec env' body in
        let ty = Ast.Var.ty v |> conv_ty in
        Term.fun_ ty body
      | Ast.Forall (v,body) ->
        let env' = add_bound env v in
        let body = conv_term_rec env' body in
        let uty =
          let ty = Ast.Var.ty v |> conv_ty in
          match Ty.view ty with
            | Atomic (_, Uninterpreted uty) -> uty
            | _ -> errorf "forall: need to quantify on an uninterpreted type, not %a" Ty.pp ty
        in
        Term.forall uty body
      | Ast.Exists (v,body) ->
        let env' = add_bound env v in
        let body = conv_term_rec env' body in
        let uty =
          let ty = Ast.Var.ty v |> conv_ty in
          match Ty.view ty with
            | Atomic (_, Uninterpreted uty) -> uty
            | _ -> errorf "exists: need to quantify on an uninterpreted type, not %a" Ty.pp ty
        in
        Term.exists uty body
      | Ast.Mu (v,body) ->
        let env' = add_bound env v in
        let body = conv_term_rec env' body in
        Term.mu body
      | Ast.Match (u,m) ->
        let any_rhs_depends_vars = ref false in (* some RHS depends on matched arg? *)
        let m =
          ID.Map.map
            (fun (vars,rhs) ->
               let n_vars = List.length vars in
               let env', tys =
                 CCList.fold_map
                   (fun env v -> add_bound env v, Ast.Var.ty v |> conv_ty)
                   env vars
               in
               let rhs = conv_term_rec env' rhs in
               let depends_on_vars =
                 Term.to_seq_depth rhs
                 |> Sequence.exists
                   (fun (t,k) -> match t.term_cell with
                      | DB db ->
                        DB.level db < n_vars + k (* [k]: number of intermediate binders *)
                      | _ -> false)
               in
               if depends_on_vars then any_rhs_depends_vars := true;
               tys, rhs)
            m
        in
        (* optim: check whether all branches return the same term, that
           does not depend on matched variables *)
        (* TODO: do the closedness check during conversion, above *)
        let rhs_l =
          ID.Map.values m
          |> Sequence.map snd
          |> Sequence.to_rev_list
          |> CCList.Set.uniq ~eq:Term.equal
        in
        begin match rhs_l with
          | [x] when not (!any_rhs_depends_vars) ->
            (* every branch yields the same [x], which does not depend
               on the argument: remove the match and return [x] instead *)
            x
          | _ ->
            let u = conv_term_rec env u in
            Term.match_ u m
        end
      | Ast.Switch _ ->
        errorf "cannot convert switch %a" Ast.pp_term t
      | Ast.Let (v,t,u) ->
        (* substitute on the fly *)
        let t = conv_term_rec env t in
        let env' = add_let_bound env v t in
        conv_term_rec env' u
      | Ast.If (a,b,c) ->
        let b = conv_term_rec env b in
        let c = conv_term_rec env c in
        (* optim: [if _ b b --> b] *)
        if Term.equal b c
        then b
        else Term.if_ (conv_term_rec env a) b c
      | Ast.Not t -> Term.not_ (conv_term_rec env t)
      | Ast.Binop (op,a,b) ->
        let a = conv_term_rec env a in
        let b = conv_term_rec env b in
        begin match op with
          | Ast.And -> Term.and_ a b
          | Ast.Or -> Term.or_ a b
          | Ast.Imply -> Term.imply a b
          | Ast.Eq -> Term.eq a b
        end

    let conv_term t =
      let t' = conv_term_rec empty_env t in
      Log.debugf 2
        (fun k->k "(@[conv_term@ @[%a@]@ yields: %a@])" Ast.pp_term t Term.pp t');
      t'

    let add_statement st =
      Log.debugf 2
        (fun k->k "(@[add_statement@ @[%a@]@])" Ast.pp_statement st);
      model_env_ := Ast.env_add_statement !model_env_ st;
      match st with
        | Ast.Assert t ->
          let t = conv_term t in
          Top_goals.push t;
          push_clause (Clause.make [Lit.atom t])
        | Ast.Goal (vars, t) ->
          (* skolemize *)
          let env, consts =
            CCList.fold_map
              (fun env v ->
                 let ty = Ast.Var.ty v |> conv_ty in
                 let c = Cst_undef.make_undef ~depth:0 (Ast.Var.id v) ty in
                 add_let_bound env v (Term.const c), c)
              empty_env
              vars
          in
          (* model should contain values of [consts] *)
          List.iter add_cst_support_ consts;
          let t = conv_term_rec env t in
          Top_goals.push t;
          push_clause (Clause.make [Lit.atom t])
        | Ast.TyDecl id ->
          let rec ty = lazy (
            let ty0 = {
              uty_self=ty;
              uty_parent=None;
              uty_offset=0; (* root *)
              uty_pair=Lazy_none;
              uty_status=None;
            } in
            Ty.atomic id (Uninterpreted ty0)
          ) in
          (* model should contain domain of [ty] *)
          add_ty_support_ (Lazy.force ty);
          ID.Tbl.add ty_tbl_ id ty
        | Ast.Decl (id, ty) ->
          assert (not (ID.Tbl.mem decl_ty_ id));
          let ty = conv_ty ty in
          let cst = Cst_undef.make_undef ~depth:0 id ty in
          add_cst_support_ cst; (* need it in model *)
          ID.Tbl.add decl_ty_ id (Lazy.from_val cst)
        | Ast.Data l ->
          (* declare the type, and all the constructors *)
          List.iter
            (fun {Ast.Ty.data_id; data_cstors} ->
               let ty = lazy (
                 let cstors =
                   ID.Map.to_seq data_cstors
                   |> Sequence.map
                     (fun (id_c, ty_c) ->
                        let c = lazy (
                          let ty_c = conv_ty ty_c in
                          Cst_undef.make_cstor id_c ty_c
                        ) in
                        ID.Tbl.add decl_ty_ id_c c; (* declare *)
                        c)
                   |> Sequence.to_rev_list
                 in
                 Ty.atomic data_id (Data cstors)
               ) in
               ID.Tbl.add ty_tbl_ data_id ty;
            )
            l;
          (* force evaluation *)
          List.iter
            (fun {Ast.Ty.data_id; _} ->
               ID.Tbl.find ty_tbl_ data_id |> Lazy.force |> ignore)
            l
        | Ast.Define l ->
          (* declare the mutually recursive functions *)
          List.iter
            (fun (id,ty,rhs) ->
               let ty = conv_ty ty in
               let rhs = lazy (conv_term rhs) in
               let cst = lazy (
                 Cst_undef.make_defined id ty rhs
               ) in
               ID.Tbl.add decl_ty_ id cst)
            l;
          (* force thunks *)
          List.iter
            (fun (id,_,_) ->
               let c = ID.Tbl.find decl_ty_ id |> Lazy.force in
               begin match c.cst_kind with
                 | Cst_defined  (_, lazy _) -> () (* also force definition *)
                 | _ -> assert false
               end;
               (* also register the constant for expansion *)
               declare_defined_cst c
            )
            l

    let add_statement_l = List.iter add_statement

    module A = Ast

    let rec ty_to_ast (t:Ty.t): A.Ty.t = match t.ty_cell with
      | Prop -> A.Ty.Prop
      | Atomic (id,_) -> A.Ty.const id
      | Arrow (a,b) -> A.Ty.arrow (ty_to_ast a) (ty_to_ast b)

    let fresh_var =
      let n = ref 0 in
      fun ty ->
        let id = ID.makef "x%d" !n in
        incr n;
        A.Var.make id (ty_to_ast ty)

    let with_var ty env ~f =
      let v = fresh_var ty in
      let env = DB_env.push (A.var v) env in
      f v env

    let with_vars tys env ~f =
      let vars = List.map fresh_var tys in
      let env = DB_env.push_l (List.map A.var vars) env in
      f vars env

    let term_to_ast (t:term): Ast.term =
      let rec aux env t = match t.term_cell with
        | True -> A.true_
        | False -> A.false_
        | DB d ->
          begin match DB_env.get d env with
            | Some t' -> t'
            | None -> errorf "cannot find DB %a in env" Term.pp t
          end
        | Const cst -> A.const cst.cst_id (ty_to_ast (Term.ty t))
        | App (f,l) -> A.app (aux env f) (List.map (aux env) l)
        | Fun (ty,bod) ->
          with_var ty env
            ~f:(fun v env -> A.fun_ v (aux env bod))
        | Mu _ -> assert false
        | If (a,b,c) -> A.if_ (aux env a)(aux env b) (aux env c)
        | Match (u,m) ->
          let u = aux env u in
          let m =
            ID.Map.map
              (fun (tys,rhs) ->
                 with_vars tys env ~f:(fun vars env -> vars, aux env rhs))
              m
          in
          A.match_ u m
        | Switch (u,m) ->
          let u = aux env u in
          let m =
            ID.Tbl.to_seq m.switch_tbl
            |> Sequence.map (fun (c,rhs) -> c, aux env rhs)
            |> ID.Map.of_seq
          in
          A.switch u m
        | Quant (q,uty,bod) ->
          let lazy ty = uty.uty_self in
          with_var ty env
            ~f:(fun v env ->
              let bod = aux env bod in
              match q with
                | Forall -> A.forall v bod
                | Exists -> A.exists v bod)
        | Builtin b ->
          begin match b with
            | B_not t -> A.not_ (aux env t)
            | B_and (a,_,b,_) -> A.and_ (aux env a) (aux env b)
            | B_or (a,b) -> A.or_ (aux env a) (aux env b)
            | B_eq (a,b) -> A.eq (aux env a) (aux env b)
            | B_imply (a,b) -> A.imply (aux env a) (aux env b)
          end
        | Check_assign (c,t) ->
          aux env (Term.eq (Term.const c) t) (* becomes a mere equality *)
        | Check_empty_uty _ -> assert false
      in aux DB_env.empty t
  end

  (** {2 Main} *)

  type unknown =
    | U_timeout
    | U_max_depth
    | U_incomplete

  type model = Model.t
  let pp_model = Model.pp

  type res =
    | Sat of model
    | Unsat (* TODO: proof *)
    | Unknown of unknown

  (* follow "normal form" pointers deeply in the term *)
  let deref_deep (doms:cst list Ty.Tbl.t) (t:term) : term =
    let rec aux t =
      let _, t = Reduce.compute_nf t in
      match t.term_cell with
        | True | False | DB _ -> t
        | Const _ -> t
        | App (f,l) ->
          Term.app (aux f) (List.map aux l)
        | If (a,b,c) -> Term.if_ (aux a)(aux b)(aux c)
        | Match (u,m) ->
          let m = ID.Map.map (fun (tys,rhs) -> tys, aux rhs) m in
          Term.match_ (aux u) m
        | Switch (u,m) ->
          let dom =
            try Ty.Tbl.find doms m.switch_ty_arg
            with Not_found ->
              errorf "could not find domain of type %a" Ty.pp m.switch_ty_arg
          in
          let switch_tbl=
            ID.Tbl.to_seq m.switch_tbl
            |> Sequence.filter_map
              (fun (id,rhs) ->
                 (* only keep this case if [member id dom] *)
                 if List.exists (fun c -> ID.equal id c.cst_id) dom
                 then Some (id, aux rhs)
                 else None)
            |> ID.Tbl.of_seq
          in
          if ID.Tbl.length switch_tbl = 0
          then (
            (* make a new unknown constant of the proper type *)
            let c =
              Cst_undef.make_undef ~depth:0
                (ID.makef "?default_%s" (Ty.mangle m.switch_ty_ret))
                m.switch_ty_ret
            in
            Term.const c
          ) else (
            let m =
                 { m with
                     switch_tbl;
                     switch_id=new_switch_id_();
                 } in
            Term.switch (aux u) m
          )
        | Quant (q,uty,body) -> Term.quant q uty (aux body)
        | Fun (ty,body) -> Term.fun_ ty (aux body)
        | Mu body -> Term.mu (aux body)
        | Builtin b -> Term.builtin (Term.map_builtin aux b)
        | Check_assign _
        | Check_empty_uty _
          -> assert false
    in
    aux t

  let rec find_domain_ (uty:ty_uninterpreted_slice): cst list =
    match uty.uty_status, uty.uty_pair with
      | _, Lazy_none -> [] (* we did not need this slice *)
      | None, Lazy_some _ -> assert false
      | Some (_, Uty_empty), _ -> []
      | Some (_, Uty_nonempty), Lazy_some (c_head, uty_tail) ->
        c_head :: find_domain_ uty_tail

  let compute_model_ () : model =
    let env = !model_env_ in
    (* compute domains of uninterpreted types *)
    let doms =
      !model_utys
      |> Sequence.of_list
      |> Sequence.map
        (fun ty -> match ty.ty_cell with
           | Atomic (_, Uninterpreted uty) -> ty, find_domain_ uty
           | _ -> assert false)
      |> Ty.Tbl.of_seq
    in
    (* compute values of meta variables *)
    let consts =
      !model_support_
      |> Sequence.of_list
      |> Sequence.map
        (fun c ->
           (* find normal form of [c] *)
           let t = Term.const c in
           let t = deref_deep doms t |> Conv.term_to_ast in
           c.cst_id, t)
      |> ID.Map.of_seq
    in
    (* now we can convert domains *)
    let domains =
      Ty.Tbl.to_seq doms
      |> Sequence.map
        (fun (ty,dom) -> Conv.ty_to_ast ty, List.map Cst_undef.id dom)
      |> Ast.Ty.Map.of_seq
    in
    Model.make ~env ~consts ~domains

  let model_check m =
    Log.debugf 1 (fun k->k "checking model…");
    Log.debugf 5 (fun k->k "(@[<1>candidate model: %a@])" Model.pp m);
    let goals =
      Top_goals.to_seq
      |> Sequence.map Conv.term_to_ast
      |> Sequence.to_list
    in
    Model.check m ~goals

  let clause_of_mclause (c:M.St.clause): Clause.t =
    M.Proof.to_list c |> List.map (fun a -> a.M.St.lit) |> Clause.make

  (* convert unsat-core *)
  let clauses_of_unsat_core (core:M.St.clause list): Clause.t Sequence.t =
    Sequence.of_list core
    |> Sequence.map clause_of_mclause

  let pp_stats out () : unit =
    fpf out
      "(@[<hv1>stats@ \
       :num_expanded %d@ \
       :num_uty_expanded %d@ \
       :num_clause_push %d@ \
       :num_clause_tautology %d@ \
       :num_lits %d@ \
       :num_propagations %d@ \
       :num_unif %d@ \
       @])"
      !stat_num_cst_expanded
      !stat_num_uty_expanded
      !stat_num_clause_push
      !stat_num_clause_tautology
      (Top_terms.size())
      !stat_num_propagations
      !stat_num_unif

  let do_on_exit ~on_exit =
    List.iter (fun f->f()) on_exit;
    ()

  let add_statement_l = Conv.add_statement_l

  let pp_proof out p =
    let pp_step_res out p =
      let {M.Proof.conclusion; _ } = M.Proof.expand p in
      let conclusion = clause_of_mclause conclusion in
      Clause.pp out conclusion
    in
    let pp_step out = function
      | M.Proof.Lemma () -> fpf out "(@[<1>lemma@ ()@])"
      | M.Proof.Resolution (p1, p2, _) ->
        fpf out "(@[<1>resolution@ %a@ %a@])"
          pp_step_res p1 pp_step_res p2
      | _ -> Fmt.string out "<other>"
    in
    fpf out "(@[<v>";
    M.Proof.fold
      (fun () {M.Proof.conclusion; step } ->
         let conclusion = clause_of_mclause conclusion in
         fpf out "(@[<hv1>step@ %a@ @[<1>from:@ %a@]@])@,"
           Clause.pp conclusion pp_step step)
      () p;
    fpf out "@])";
    ()

  type proof_status =
    | PS_depth_limited of Lit.t
    | PS_complete
    | PS_incomplete

  let pp_proof_status out = function
    | PS_depth_limited lit ->
      fpf out "(@[depth_limited@ by: %a@])" Lit.pp lit
    | PS_complete -> Fmt.string out "complete"
    | PS_incomplete -> Fmt.string out "incomplete"

  (* precondition: solving under assumption [depth_lit] returned unsat *)
  let proof_status depth_lit : proof_status =
    let sat_res =
      M_th.set_active false; (* no propagation, just check the boolean formula *)
      CCFun.finally
        ~h:(fun () -> M_th.set_active true)
        ~f:(fun () -> M.solve ~assumptions:[] ())
    in
    begin match sat_res with
      | M.Sat _ ->
        (* was unsat because of the assumption *)
        PS_depth_limited depth_lit
      | M.Unsat us ->
        (* really unsat, now we need to know if it involves some
           incomplete choices *)
        let p = us.SI.get_proof () in
        let core = p |> M.unsat_core in
        let incomplete =
          clauses_of_unsat_core core
          |> Sequence.flat_map Clause.to_seq
          |> Sequence.exists
            (fun lit -> match Lit.view lit with
               | Lit_assign (c,_) ->
                 begin match c.cst_kind with
                   | Cst_undef (_, i, _) when not i.cst_complete -> true
                   | _ -> false
                 end
               | _ -> false)
        in
        if incomplete then PS_incomplete else PS_complete
    end

  let dump_dimacs () = match Config.dimacs_file with
    | None -> ()
    | Some file ->
      Log.debugf 2 (fun k->k "dump SAT problem into file `%s`" file);
      CCIO.with_out file
        (fun oc ->
           let out = Format.formatter_of_out_channel oc in
           fpf out "@[<v>%a@]@." M.export_dimacs ())

  let solve ?(on_exit=[]) ?(check=true) () =
    let on_exit = dump_dimacs :: on_exit in
    let module ID = Iterative_deepening in
    (* iterated deepening *)
    let rec iter state = match state with
      | ID.Exhausted ->
        do_on_exit ~on_exit;
        Unknown U_max_depth
      | ID.At (cur_depth, cur_lit) ->
        (* restrict depth *)
        match M.solve ~assumptions:[cur_lit] () with
          | M.Sat _ ->
            let m = compute_model_ () in
            Log.debugf 1
              (fun k->k "@{<Yellow>** found SAT@} at depth %a"
                  ID.pp cur_depth);
            do_on_exit ~on_exit;
            if check then model_check m;
            Sat m
          | M.Unsat us ->
            (* check if [max depth] literal involved in proof;
               - if not, truly UNSAT
               - if yes, try next level
            *)
            let p = us.SI.get_proof () in
            Log.debugf 4 (fun k->k "proof: @[%a@]@." pp_proof p);
            let status = proof_status cur_lit in
            Log.debugf 1
              (fun k->k
                  "@{<Yellow>** found Unsat@} at depth %a;@ \
                   status: %a"
                  ID.pp cur_depth pp_proof_status status);
            match status with
              | PS_depth_limited _ ->
                (* negation of the previous limit *)
                push_clause (Clause.make [Lit.neg cur_lit]);
                iter (ID.next ()) (* deeper! *)
              | PS_incomplete ->
                do_on_exit ~on_exit;
                Unknown U_incomplete
              | PS_complete ->
                do_on_exit ~on_exit;
                Unsat
    in
    ID.reset ();
    iter (ID.current ())
end

