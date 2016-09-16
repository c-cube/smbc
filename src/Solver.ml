
(* This file is free software. See file "license" for more details. *)

let get_time : unit -> float =
  let start = Unix.gettimeofday() in
  fun () ->
    Unix.gettimeofday() -. start

module FI = Msat.Formula_intf
module TI = Msat.Theory_intf
module SI = Msat.Solver_intf

(** {1 Solver} *)

module type CONFIG = sig
  val max_depth: int

  val deepening_step : int option
  (** Increment between two successive max depths in iterative deepening *)

  val progress: bool
  (** progress display progress bar *)

  val pp_hashcons: bool
end

(** {2 The Main Solver} *)

module Make(Config : CONFIG)(Dummy : sig end) = struct
  exception Error of string

  let () = Printexc.register_printer
      (function
        | Error msg -> Some ("internal error: " ^ msg)
        | _ -> None)

  let errorf msg = CCFormat.ksprintf msg ~f:(fun s -> raise (Error s))

  type level = int

  let stat_num_cst_expanded = ref 0
  let stat_num_uty_expanded = ref 0
  let stat_num_clause_push = ref 0
  let stat_num_clause_tautology = ref 0
  let stat_num_propagations = ref 0

  (* for objects that are expanded on demand only *)
  type 'a lazily_expanded =
    | Lazy_some of 'a
    | Lazy_none

  module IntMap = CCMap.Make(CCInt)

  type 'a registers = 'a IntMap.t
  (* map from registers to something *)

  (* main term cell *)
  type term = {
    mutable term_id: int; (* unique ID *)
    mutable term_ty: ty_h;
    term_cell: term_cell;
    mutable term_nf: (term * explanation) option;
      (* normal form + explanation of why *)
    mutable term_deps: term_dep list;
    (* set of undefined constants
       that can make evaluation go further *)
  }

  (* term shallow structure *)
  and term_cell =
    | True
    | False
    | DB of db (* de bruijn indice *)
    | Reg of register (* de bruijn level *)
    | Const of cst
    | App of term * term list
    | Fun of ty_h * term
    | Mu of term
    | If of term * term * term
    | Match of term * (ty_h list * term) ID.Map.t
    | Switch of term * switch_cell (* function table *)
    | Quant of quant * ty_uninterpreted_slice * term
      (* quantification on finite types *)
    | Memo_call of memo_call
      (* call to memoized function. *)
    | Builtin of builtin

  and db = int * ty_h

  and register = int * ty_h
  (* register for storing sub-terms in memoization trees *)

  and quant =
    | Forall
    | Exists

  (* what can block evaluation of a term *)
  and term_dep =
    | Dep_cst of cst
      (* blocked by non-refined constant *)
    | Dep_uty of ty_uninterpreted_slice
      (* blocked because this type is not expanded enough *)
    | Dep_reg of register
      (* blocked because of this unassigned register *)

  and builtin =
    | B_not of term
    | B_eq of term * term
    | B_and of term * term * term * term (* parallel and *)
    | B_or of term * term
    | B_imply of term * term

  (* memoization table for some function *)
  and memo_tbl = {
    memo_fun: ID.t; (* function name *)
    memo_cst: cst lazy_t; (* the typed constant *)
    memo_ty: ty_h; (* type of function (with [memo_arity] arguments) *)
    memo_arity: int; (* num of arguments *)
    memo_dtree: memo_decision_tree;
    (* the partial pattern-match tree storing the
       current subset of memoized values for this function.
       Invariant: the tree matches registers from 0...n in that order.
     *)
  }

  (* a call to a memoized function.
     Invariants:
     [forall r in mc_concrete_terms, r < mc_offset] *)
  and memo_call = {
    mc_tbl: memo_tbl;
    mc_deps: term_dep list; (* term blocking evaluation (in all states) *)
    mc_dt: memo_decision_tree; (* current position in the decision tree *)
    mc_concrete_terms: term registers; (* register -> concrete term *)
    mc_explanation: explanation; (* explanations so far (when evaluating arguments) *)
  }

  and memo_symbolic_value =
    | Memo_true
    | Memo_false
    | Memo_cstor of cst * ty_h * register list
    | Memo_dom_elt of cst

  (* a (mutable) decision tree for memoization. The internal nodes represent
     choices (if/match) on some register; the leaves are either fail (cache miss)
     or yield (cache hit). As time goes, the tree grows and contains more
     and more yields. *)
  and memo_decision_tree = {
    mc_dt_offset: int; (* next free register *)
    mc_dt_term: term lazy_t; (* current term (as symbolic evaluation) *)
    mutable mc_dt_cell: memo_decision_tree_cell; (* tree shape *)
  }

   (* TODO: add "switch" for memoizing on uninterpreted types *)
  and memo_decision_tree_cell =
    | Memo_fail (* cache miss *)
    | Memo_yield (* yield the [mc_dt_tree], depends on registers *)
    | Memo_match of register * (register list * memo_decision_tree) ID.Map.t
    | Memo_if of register * memo_decision_tree * memo_decision_tree (* if *)

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

  (* bag of atomic explanations. It is optimized for traversal
     and fast cons/snoc/append *)
  and explanation=
    | E_empty
    | E_leaf of lit
    | E_append of explanation * explanation

  (* boolean literal *)
  and lit = {
    lit_view: lit_view;
    lit_sign: bool;
  }

  and lit_view =
    | Lit_fresh of ID.t (* fresh literals *)
    | Lit_atom of term
    | Lit_assign of cst * term
    | Lit_uty_empty of ty_uninterpreted_slice

  and cst = {
    cst_id: ID.t;
    cst_kind: cst_kind;
  }

  and cst_kind =
    | Cst_undef of ty_h * cst_info * ty_uninterpreted_slice option
    | Cst_cstor of ty_h
    | Cst_uninterpreted_dom_elt of ty_h (* uninterpreted domain constant *)
    | Cst_defined of ty_h * term lazy_t * cst_memo_status

  and cst_memo_status =
    | Cst_trivial (* memoizable but too trivial *)
    | Cst_not_memoizable
    | Cst_memoizable of memo_tbl

  and cst_info = {
    cst_depth: int;
    (* refinement depth, used for iterative deepening *)
    cst_parent: cst option;
    (* if const was created as a parameter to some cases of some other constant *)
    cst_exist_conds: cst_exist_conds;
    (* disjunction of possible conditions for cst to exist/be relevant *)
    mutable cst_cases: term list lazily_expanded;
    (* cover set (lazily evaluated) *)
    mutable cst_complete: bool;
    (* does [cst_cases] cover all possible cases, or only
       a subset? Affects completeness *)
    mutable cst_cur_case: (explanation * term) option;
    (* current choice of normal form *)
    cst_watched: term Poly_set.t;
    (* set of literals (rather, boolean terms) that depend on this constant
       for evaluation.

       A literal [lit] can watch several typed constants. If
       [lit.nf = t], and [t]'s evaluation is blocked by [c1,...,ck],
       then [lit] will watch [c1,...,ck].

       Watch list only grow, they never shrink. *)
  }

  (* this is a disjunction of sufficient conditions for the existence of
     some meta (cst). Each condition is a literal *)
  and cst_exist_conds = lit lazy_t list ref

  and 'a db_env = {
    db_st: 'a option list;
    db_size: int;
  }

  (* environment for evaluation: not-yet-evaluated terms *)
  and eval_env = term db_env

  (* Hashconsed type *)
  and ty_h = {
    mutable ty_id: int;
    ty_cell: ty_cell;
  }

  and ty_def =
    | Uninterpreted of ty_uninterpreted (* uninterpreted type, with its domain *)
    | Data of cst lazy_t list (* set of constructors *)

  and ty_cell =
    | Prop
    | Atomic of ID.t * ty_def
    | Arrow of ty_h * ty_h

  and ty_uninterpreted = ty_uninterpreted_slice

  (* current status of this slice of uninterpreted type in the model *)
  and ty_uninterpreted_status =
    | Uty_empty
    | Uty_nonempty

  (* A slice of an uninterpreted type's the domain.
     For instance, if [u] is uninterpreted, it might be defined as
     [(u0 | (u1 | (empty)))] where [empty] will be expanded into [(u2 | empty)]
     if needed. We write [u[3:]] to designate the slice of [u]'s domain
     that skips the first 3 elements. *)
  and ty_uninterpreted_slice = {
    uty_self: ty_h lazy_t;
    (* pointer to the root type *)
    uty_offset: int;
    (* length of path from root [Uninterpreted]; in other words, the
       number of elements that have been skipped. *)
    uty_parent: ty_uninterpreted_slice option;
    (* if [offset>0], the previous slice *)
    mutable uty_pair: (cst * ty_uninterpreted_slice) lazily_expanded;
    (* the domain constant, must be Cst_uninterpreted_dom_elt,
       and the next slice.
       Expanded on demand. *)
    mutable uty_status: (explanation * ty_uninterpreted_status) option;
    (* current status in the model *)
    uty_watched: term Poly_set.t;
    (* set of terms whose evaluation is blocked by this uty.
       See {!info.cst_watched} for more details *)
  }

  let pp_quant out = function
    | Forall -> CCFormat.string out "forall"
    | Exists -> CCFormat.string out "exists"

  module Ty = struct
    type t = ty_h

    let view t = t.ty_cell

    let equal a b = a.ty_id = b.ty_id
    let compare a b = CCOrd.int_ a.ty_id b.ty_id
    let hash a = a.ty_id

    module H = Hashcons.Make(struct
        type t = ty_h
        let equal a b = match a.ty_cell, b.ty_cell with
          | Prop, Prop -> true
          | Atomic (i1,_), Atomic (i2,_) -> ID.equal i1 i2
          | Arrow (a1,b1), Arrow (a2,b2) ->
            equal a1 a2 && equal b1 b2
          | Prop, _
          | Atomic _, _
          | Arrow _, _ -> false

        let hash t = match t.ty_cell with
          | Prop -> 1
          | Atomic (i,_) -> Hash.combine2 2 (ID.hash i)
          | Arrow (a,b) -> Hash.combine3 3 (hash a) (hash b)

        let set_id ty i = ty.ty_id <- i
      end)

    (* hashcons terms *)
    let hashcons_ ty_cell =
      H.hashcons { ty_cell; ty_id = -1; }

    let prop = hashcons_ Prop

    let atomic id def = hashcons_ (Atomic (id,def))

    let arrow a b = hashcons_ (Arrow (a,b))
    let arrow_l = List.fold_right arrow

    let is_prop t =
      match t.ty_cell with | Prop -> true | _ -> false

    let is_data t =
      match t.ty_cell with | Atomic (_, Data _) -> true | _ -> false

    let unfold ty : t list * t =
      let rec aux acc ty = match ty.ty_cell with
        | Arrow (a,b) -> aux (a::acc) b
        | _ -> List.rev acc, ty
      in
      aux [] ty

    let rec pp out t = match t.ty_cell with
      | Prop -> CCFormat.string out "prop"
      | Atomic (id, _) -> ID.pp out id
      | Arrow _ ->
        let args, ret = unfold t in
        Format.fprintf out "(@[->@ %a@ %a@])"
          (Utils.pp_list pp) args pp ret

    (* representation as a single identifier *)
    let rec mangle t : string = match t.ty_cell with
      | Prop -> "prop"
      | Atomic (id,_) -> ID.to_string id
      | Arrow (a,b) -> mangle a ^ "_" ^ mangle b

    module Tbl = CCHashtbl.Make(struct
        type t = ty_h
        let equal = equal
        let hash = hash
      end)
  end

  let eq_reg (i1,ty1)(i2,ty2) = i1=i2 && Ty.equal ty1 ty2

  (** {2 Typed De Bruijn indices} *)
  module DB = struct
    type t = db
    let level = fst
    let ty = snd
    let succ (i,ty) = i+1,ty
    let hash (i,ty) = Hash.combine Ty.hash i ty
    let equal x y = level x = level y && Ty.equal (ty x) (ty y)
    let make i ty = i,ty
    let pp out (i,_) = Format.fprintf out "%%%d" i
  end

  module DB_env = struct
    type 'a t = 'a db_env

    let push x env = { db_size=env.db_size+1; db_st=Some x :: env.db_st }
    let push_l l env = List.fold_left (fun e x -> push x e) env l
    let push_none env =
      { db_size=env.db_size+1; db_st=None::env.db_st }
    let push_none_l l env = List.fold_left (fun e _ -> push_none e) env l
    let empty = {db_st=[]; db_size=0}
    let singleton x = {db_st=[Some x]; db_size=1}
    let size env = env.db_size
    let get ((n,_):DB.t) env : _ option =
      if n < env.db_size then List.nth env.db_st n else None
  end

  let term_equal_ (a:term) b = a==b
  let term_hash_ a = a.term_id
  let term_cmp_ a b = CCOrd.int_ a.term_id b.term_id

  module Typed_cst = struct
    type t = cst

    let id t = t.cst_id

    let ty_of_kind = function
      | Cst_defined (ty, _, _)
      | Cst_undef (ty, _, _)
      | Cst_uninterpreted_dom_elt ty
      | Cst_cstor ty -> ty

    let ty t = ty_of_kind t.cst_kind

    let make cst_id cst_kind = {cst_id; cst_kind}
    let make_cstor id ty =
      let _, ret = Ty.unfold ty in
      assert (Ty.is_data ret);
      make id (Cst_cstor ty)
    let make_defined id ty t memo = make id (Cst_defined (ty, t, memo))
    let make_uty_dom_elt id ty = make id (Cst_uninterpreted_dom_elt ty)

    let make_undef ?parent ?exist_if ?slice id ty =
      let info =
        let cst_depth = match parent with
          | Some {cst_kind=Cst_undef (ty, i, _); _} ->
            begin match Ty.view ty with
              | Arrow _ -> i.cst_depth
              | Atomic _ | Prop -> i.cst_depth + 1
            end
          | Some _ ->
            invalid_arg "make_const: parent should be a constant"
          | None -> 0
        in
        { cst_depth;
          cst_parent=parent;
          cst_exist_conds=CCOpt.get_lazy (fun ()->ref []) exist_if;
          cst_cases=Lazy_none;
          cst_complete=false;
          cst_cur_case=None;
          cst_watched=
            Poly_set.create ~eq:term_equal_ 16;
        }
      in
      make id (Cst_undef (ty, info, slice))

    let as_undefined (c:t)
      : (t * Ty.t * cst_info * ty_uninterpreted_slice option) option =
      match c.cst_kind with
        | Cst_undef (ty,i,slice) -> Some (c,ty,i,slice)
        | Cst_defined _ | Cst_cstor _ | Cst_uninterpreted_dom_elt _ -> None

    let as_undefined_exn (c:t): t * Ty.t * cst_info * ty_uninterpreted_slice option=
      match as_undefined c with
        | Some tup -> tup
        | None -> assert false

    let equal a b = ID.equal a.cst_id b.cst_id
    let compare a b = ID.compare a.cst_id b.cst_id
    let hash t = ID.hash t.cst_id
    let pp out a = ID.pp out a.cst_id

    module Map = CCMap.Make(struct
        type t = cst
        let compare = compare
      end)
  end

  let cmp_uty a b =
    let c = Ty.compare (Lazy.force a.uty_self) (Lazy.force b.uty_self) in
    if c<>0 then c
    else CCOrd.int_ a.uty_offset b.uty_offset

  let equal_uty a b = cmp_uty a b = 0

  let hash_uty uty =
    Hash.combine3 104 (Ty.hash (Lazy.force uty.uty_self)) uty.uty_offset

  let eq_memo_tbl t1 t2 = ID.equal t1.memo_fun t2.memo_fun

  let eq_memo_call_ a b =
    eq_memo_tbl a.mc_tbl b.mc_tbl &&
    term_equal_ (Lazy.force a.mc_dt.mc_dt_term) (Lazy.force b.mc_dt.mc_dt_term) &&
    IntMap.equal term_equal_ a.mc_concrete_terms b.mc_concrete_terms

  let hash_memo_call m =
    (* defines the relation between concrete arguments and symbolic registers *)
    let h_concrete =
      Hash.seq (Hash.pair Hash.int term_hash_) (IntMap.to_seq m.mc_concrete_terms)
    in
    (* the memo call is equivalent to this term on the symbolic side *)
    let h_symb = term_hash_ (Lazy.force m.mc_dt.mc_dt_term) in
    Hash.combine4 1234 (ID.hash m.mc_tbl.memo_fun) h_concrete h_symb

  let rec cmp_lit a b =
    let c = CCOrd.bool_ a.lit_sign b.lit_sign in
    if c<>0 then c
    else
      let int_of_cell_ = function
        | Lit_fresh _ -> 0
        | Lit_atom _ -> 1
        | Lit_assign _ -> 2
        | Lit_uty_empty _ -> 3
      in
      match a.lit_view, b.lit_view with
        | Lit_fresh i1, Lit_fresh i2 -> ID.compare i1 i2
        | Lit_atom t1, Lit_atom t2 -> term_cmp_ t1 t2
        | Lit_assign (c1,t1), Lit_assign (c2,t2) ->
          CCOrd.(Typed_cst.compare c1 c2 <?> (term_cmp_, t1, t2))
        | Lit_uty_empty u1, Lit_uty_empty u2 -> cmp_uty u1 u2
        | Lit_fresh _, _
        | Lit_atom _, _
        | Lit_assign _, _
        | Lit_uty_empty _, _
          ->
          CCOrd.int_ (int_of_cell_ a.lit_view) (int_of_cell_ b.lit_view)

  (* comparison of explanations as ordered sequences of literals *)
  and cmp_expl (e1:explanation)(e2:explanation): int =
    let rec aux l1 l2 = match l1, l2 with
      | [], [] -> 0
      | [], _ -> -1
      | _, [] -> 1
      | E_empty :: l1', _ -> aux l1' l2
      | _, E_empty :: l2' -> aux l1 l2'
      | E_append (a,b) :: l1', _ -> aux (a::b::l1') l2
      | _, E_append (a,b) :: l2' -> aux l1 (a::b::l2')
      | E_leaf a :: l1', E_leaf b :: l2' ->
        let c = cmp_lit a b in
        if c=0 then aux l1' l2' else c
    in
    aux [e1] [e2]

  let eq_lit a b = (cmp_lit a b) = 0
  let eq_expl a b = (cmp_expl a b) = 0

  let rec hash_lit a =
    let sign = a.lit_sign in
    match a.lit_view with
      | Lit_fresh i -> Hash.combine3 1 (Hash.bool sign) (ID.hash i)
      | Lit_atom t -> Hash.combine3 2 (Hash.bool sign) (term_hash_ t)
      | Lit_assign (c,t) ->
        Hash.combine4 3 (Hash.bool sign) (Typed_cst.hash c) (term_hash_ t)
      | Lit_uty_empty uty -> Hash.combine3 4 (Hash.bool sign) (hash_uty uty)

  and hash_expl e = match e with
    | E_empty -> 0
    | E_leaf l -> hash_lit l
    | E_append (a,b) -> Hash.combine2 (hash_expl a) (hash_expl b)

  let pp_uty out uty =
    let n = uty.uty_offset in
    let lazy ty = uty.uty_self in
    if n=0
    then Format.fprintf out "%a[:]" Ty.pp ty
    else Format.fprintf out "%a[%d:]" Ty.pp ty n

  let pp_uty_status out = function
    | Uty_empty -> CCFormat.string out "empty"
    | Uty_nonempty -> CCFormat.string out "non_empty"

  let pp_dep out = function
    | Dep_cst c -> Typed_cst.pp out c
    | Dep_uty uty -> pp_uty out uty
    | Dep_reg (i,_) -> Format.fprintf out "reg_%d" i

  module Backtrack = struct
    type _level = level
    type level = _level

    let dummy_level = -1

    type stack_cell =
      | S_set_nf of
          term * (term * explanation) option
          (* t1.nf <- t2 *)
      | S_set_cst_case of
          cst_info * (explanation * term) option
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
          | S_set_nf (t, nf) -> t.term_nf <- nf;
          | S_set_cst_case (info, c) -> info.cst_cur_case <- c;
          | S_set_uty (uty, s) -> uty.uty_status <- s;
      done;
      ()

    let cur_level () = CCVector.length st_

    let push_level () : unit =
      let l = cur_level() in
      Log.debugf 2 (fun k->k "@{<Yellow>** now at level %d (push)@}" l);
      ()

    let push_set_nf_ (t:term) =
      CCVector.push st_ (S_set_nf (t, t.term_nf))

    let push_set_cst_case_ (i:cst_info) =
      CCVector.push st_ (S_set_cst_case (i, i.cst_cur_case))

    let push_uty_status (uty:ty_uninterpreted_slice) =
      CCVector.push st_ (S_set_uty (uty, uty.uty_status))
  end

  let new_switch_id_ =
    let n = ref 0 in
    fun () -> incr n; !n

  module Term = struct
    type t = term

    let sub_hash (t:term): int = t.term_id

    module H = Hashcons.Make(struct
        type t = term

        (* shallow hash *)
        let hash (t:term) : int = match t.term_cell with
          | True -> 1
          | False -> 2
          | DB d -> Hash.combine DB.hash 3 d
          | Reg (i,ty) -> Hash.combine3 300001 i (Ty.hash ty)
          | Const c ->
            Hash.combine2 4 (Typed_cst.hash c)
          | App (f,l) ->
            Hash.combine3 5 f.term_id (Hash.list sub_hash l)
          | Fun (ty, f) -> Hash.combine3 6 (Ty.hash ty) f.term_id
          | If (a,b,c) -> Hash.combine4 7 a.term_id b.term_id c.term_id
          | Match (u,m) ->
            let hash_case (tys,rhs) =
              Hash.combine2 (Hash.list Ty.hash tys) rhs.term_id
            in
            let hash_m =
              Hash.seq (Hash.pair ID.hash hash_case) (ID.Map.to_seq m)
            in
            Hash.combine3 8 u.term_id hash_m
          | Builtin (B_not a) -> Hash.combine2 20 a.term_id
          | Builtin (B_and (t1,t2,t3,t4)) ->
            Hash.list sub_hash [t1;t2;t3;t4]
          | Builtin (B_or (t1,t2)) -> Hash.combine3 22 t1.term_id t2.term_id
          | Builtin (B_imply (t1,t2)) -> Hash.combine3 23 t1.term_id t2.term_id
          | Builtin (B_eq (t1,t2)) -> Hash.combine3 24 t1.term_id t2.term_id
          | Mu sub -> Hash.combine sub_hash 30 sub
          | Switch (t, tbl) ->
            Hash.combine3 31 (sub_hash t) tbl.switch_id
          | Quant (q,ty,bod) ->
            Hash.combine4 32 (Hash.poly q) (hash_uty ty) (sub_hash bod)
          | Memo_call m -> hash_memo_call m

        (* equality that relies on physical equality of subterms *)
        let equal t1 t2 : bool = match t1.term_cell, t2.term_cell with
          | True, True
          | False, False -> true
          | DB x, DB y -> DB.equal x y
          | Const (c1), Const (c2) ->
            Typed_cst.equal c1 c2
          | App (f1, l1), App (f2, l2) ->
            f1 == f2 && CCList.equal (==) l1 l2
          | Fun (ty1,f1), Fun (ty2,f2) -> Ty.equal ty1 ty2 && f1 == f2
          | If (a1,b1,c1), If (a2,b2,c2) ->
            a1 == a2 && b1 == b2 && c1 == c2
          | Match (u1, m1), Match (u2, m2) ->
            u1 == u2 &&
            ID.Map.for_all
              (fun k1 (_,rhs1) ->
                 try rhs1 == snd (ID.Map.find k1 m2)
                 with Not_found -> false)
              m1
            &&
            ID.Map.for_all (fun k2 _ -> ID.Map.mem k2 m1) m2
          | Switch (t1,m1), Switch (t2,m2) ->
            t1==t2 && m1.switch_id = m2.switch_id
          | Builtin b1, Builtin b2 ->
            begin match b1, b2 with
              | B_not a1, B_not a2 -> a1 == a2
              | B_and (a1,b1,c1,d1), B_and (a2,b2,c2,d2) ->
                a1 == a2 && b1 == b2 && c1 == c2 && d1 == d2
              | B_or (a1,b1), B_or (a2,b2)
              | B_eq (a1,b1), B_eq (a2,b2)
              | B_imply (a1,b1), B_imply (a2,b2) -> a1 == a2 && b1 == b2
              | B_not _, _ | B_and _, _ | B_eq _, _
              | B_or _, _ | B_imply _, _ -> false
            end
          | Mu t1, Mu t2 -> t1==t2
          | Quant (q1,ty1,bod1), Quant (q2,ty2,bod2) ->
            q1=q2 && equal_uty ty1 ty2 && bod1==bod2
          | Memo_call m1, Memo_call m2 -> eq_memo_call_ m1 m2
          | True, _
          | False, _
          | DB _, _
          | Reg _, _
          | Const _, _
          | App _, _
          | Fun _, _
          | If _, _
          | Match _, _
          | Builtin _, _
          | Mu _, _
          | Switch _, _
          | Quant _, _
          | Memo_call _, _
            -> false

        let set_id t i = t.term_id <- i
      end)

    let mk_bool_ (b:bool) : term =
      let t = {
        term_id= -1;
        term_ty=Ty.prop;
        term_cell=if b then True else False;
        term_nf=None;
        term_deps=[];
      } in
      H.hashcons t

    let true_ = mk_bool_ true
    let false_ = mk_bool_ false

    type deps =
      | Term_dep_cst of cst (* the term itself is a constant *)
      | Term_dep_none
      | Term_dep_sub of term
      | Term_dep_sub2 of term * term
      | Term_dep_uty of ty_uninterpreted_slice
      | Term_dep_exact of term_dep list
      | Term_dep_reg of register

    type delayed_ty =
      | DTy_direct of ty_h
      | DTy_lazy of (unit -> ty_h)

    let sorted_merge_ l1 l2 = CCList.sorted_merge_uniq ~cmp:compare l1 l2

    let cmp_term_dep_ a b =
      let to_int_ = function
        | Dep_cst _ -> 0
        | Dep_uty _ -> 1
        | Dep_reg _ -> 2
      in
      let (<?>) = CCOrd.(<?>) in
      match a, b with
      | Dep_cst c1, Dep_cst c2 -> Typed_cst.compare c1 c2
      | Dep_uty u1, Dep_uty u2 ->
        Ty.compare (Lazy.force u1.uty_self) (Lazy.force u2.uty_self)
        <?> (CCOrd.int_, u1.uty_offset, u2.uty_offset)
      | Dep_reg (i1,ty1), Dep_reg (i2,ty2) ->
        CCOrd.int_ i1 i2 <?> (Ty.compare, ty1, ty2)
      | Dep_cst _, _
      | Dep_uty _, _
      | Dep_reg _, _
        -> CCOrd.int_ (to_int_ a) (to_int_ b)

    (* build a term. If it's new, add it to the watchlist
       of every member of [watching] *)
    let mk_term_ ~(deps:deps) cell ~(ty:delayed_ty) : term =
      let t = {
        term_id= -1;
        term_ty=Ty.prop; (* will be changed *)
        term_cell=cell;
        term_nf=None;
        term_deps=[];
      } in
      let t' = H.hashcons t in
      if t==t' then (
        (* compute ty *)
        t.term_ty <- begin match ty with
          | DTy_direct ty -> ty
          | DTy_lazy f -> f ()
        end;
        (* compute evaluation dependencies *)
        let deps = match deps with
          | Term_dep_none -> []
          | Term_dep_cst c -> [Dep_cst c]
          | Term_dep_sub t -> t.term_deps
          | Term_dep_sub2 (a,b) ->
            CCList.sorted_merge_uniq
              ~cmp:cmp_term_dep_ a.term_deps b.term_deps
          | Term_dep_uty uty -> [Dep_uty uty]
          | Term_dep_exact l -> l
          | Term_dep_reg r -> [Dep_reg r]
        in
        t'.term_deps <- deps
      );
      t'

    let db d =
      mk_term_ ~deps:Term_dep_none (DB d) ~ty:(DTy_direct (DB.ty d))

    let reg ((i,ty) as r) =
      assert (i>=0);
      mk_term_ ~deps:(Term_dep_reg r) (Reg r) ~ty:(DTy_direct ty)

    let const c =
      let deps = match c.cst_kind with
        | Cst_undef _ -> Term_dep_cst c (* depends on evaluation! *)
        | Cst_defined _ | Cst_cstor _ | Cst_uninterpreted_dom_elt _ -> Term_dep_none
      in
      mk_term_ ~deps (Const c) ~ty:(DTy_direct (Typed_cst.ty c))

    (* type of an application *)
    let rec app_ty_ ty l : Ty.t = match Ty.view ty, l with
      | _, [] -> ty
      | Arrow (ty_a,ty_rest), a::tail ->
        assert (Ty.equal ty_a a.term_ty);
        app_ty_ ty_rest tail
      | (Prop | Atomic _), _::_ ->
        assert false

    let app f l = match l with
      | [] -> f
      | _ ->
        (* watch head, not arguments *)
        let t = match f.term_cell with
          | App (f1, l1) ->
            let l' = l1 @ l in
            mk_term_ ~deps:(Term_dep_sub f1) (App (f1, l'))
              ~ty:(DTy_lazy (fun () -> app_ty_ f1.term_ty l'))
          | _ ->
            mk_term_ ~deps:(Term_dep_sub f) (App (f,l))
              ~ty:(DTy_lazy (fun () -> app_ty_ f.term_ty l))
        in
        t

    let app_cst f l = app (const f) l

    let fun_ ty body =
      (* do not add watcher: propagation under λ forbidden *)
      mk_term_ ~deps:Term_dep_none (Fun (ty, body))
        ~ty:(DTy_lazy (fun () -> Ty.arrow ty body.term_ty))

    let fun_l = List.fold_right fun_

    let mu t =
      mk_term_ ~deps:Term_dep_none (Mu t) ~ty:(DTy_direct t.term_ty)

    (* TODO: check types *)

    let match_ u m =
      (* propagate only from [u] *)
      let t =
        mk_term_ ~deps:(Term_dep_sub u) (Match (u,m))
          ~ty:(DTy_lazy (fun () ->
              let _, (_,rhs) = ID.Map.choose m in
              rhs.term_ty
            ))
      in
      t

    let switch u m =
      let t =
        mk_term_ ~deps:(Term_dep_sub u) (Switch (u,m))
          ~ty:(DTy_direct m.switch_ty_ret)
      in
      t

    let if_ a b c =
      assert (Ty.equal b.term_ty c.term_ty);
      (* propagate under test only *)
      let t =
        mk_term_ ~deps:(Term_dep_sub a)
          (If (a,b,c)) ~ty:(DTy_direct b.term_ty) in
      t

    let builtin_ ~deps b =
      (* normalize a bit *)
      let b = match b with
        | B_eq (a,b) when a.term_id > b.term_id -> B_eq (b,a)
        | B_and (a,b,c,d) when a.term_id > b.term_id -> B_and (b,a,d,c)
        | B_or (a,b) when a.term_id > b.term_id -> B_or (b,a)
        | _ -> b
      in
      let t = mk_term_ ~deps (Builtin b) ~ty:(DTy_direct Ty.prop) in
      t

    let builtin b =
      let deps = match b with
        | B_not u -> Term_dep_sub u
        | B_and (_,_,a,b)
        | B_or (a,b)
        | B_eq (a,b) | B_imply (a,b) -> Term_dep_sub2 (a,b)
      in
      builtin_ ~deps b

    let not_ t = match t.term_cell with
      | True -> false_
      | False -> true_
      | Builtin (B_not t') -> t'
      | _ -> builtin_ ~deps:(Term_dep_sub t) (B_not t)

    (* might need to tranfer the negation from [t] to [sign] *)
    let abs t : t * bool = match t.term_cell with
      | False -> true_, false
      | Builtin (B_not t) -> t, false
      | _ -> t, true

    let quant q uty body =
      assert (Ty.is_prop body.term_ty);
      (* evaluation is blocked by the uninterpreted type *)
      let deps = Term_dep_uty uty in
      mk_term_ ~deps ~ty:(DTy_direct Ty.prop) (Quant (q,uty,body))

    let memo_call (m:memo_call): t =
      let deps = Term_dep_exact m.mc_deps in
      let _, ty = Ty.unfold m.mc_tbl.memo_ty in
      mk_term_ ~ty:(DTy_direct ty) ~deps (Memo_call m)

    let forall = quant Forall
    let exists = quant Exists

    let and_ a b = builtin_ ~deps:(Term_dep_sub2 (a,b)) (B_and (a,b,a,b))
    let or_ a b = builtin_ ~deps:(Term_dep_sub2 (a,b)) (B_or (a,b))
    let imply a b = builtin_ ~deps:(Term_dep_sub2 (a,b)) (B_imply (a,b))
    let eq a b = builtin_ ~deps:(Term_dep_sub2 (a,b)) (B_eq (a,b))
    let neq a b = not_ (eq a b)

    let and_par a b c d =
      builtin_ ~deps:(Term_dep_sub2 (c,d)) (B_and (a,b,c,d))

    let and_l = function
      | [] -> true_
      | [t] -> t
      | a :: l -> List.fold_left and_ a l

    let or_l = function
      | [] -> false_
      | [t] -> t
      | a :: l -> List.fold_left or_ a l

    let fold_map_builtin
        (f:'a -> term -> 'a * term) (acc:'a) (b:builtin): 'a * builtin =
      let fold_binary acc a b =
        let acc, a = f acc a in
        let acc, b = f acc b in
        acc, a, b
      in
      match b with
        | B_not t ->
          let acc, t' = f acc t in
          acc, B_not t'
        | B_and (a,b,c,d) ->
          let acc, a, b = fold_binary acc a b in
          let acc, c, d = fold_binary acc c d in
          acc, B_and (a,b,c,d)
        | B_or (a,b) ->
          let acc, a, b = fold_binary acc a b in
          acc, B_or (a, b)
        | B_eq (a,b) ->
          let acc, a, b = fold_binary acc a b in
          acc, B_eq (a, b)
        | B_imply (a,b) ->
          let acc, a, b = fold_binary acc a b in
          acc, B_imply (a, b)

    let is_const t = match t.term_cell with
      | Const _ -> true
      | _ -> false

    let map_builtin f b =
      let (), b = fold_map_builtin (fun () t -> (), f t) () b in
      b

    let builtin_to_seq b yield = match b with
      | B_not t -> yield t
      | B_or (a,b)
      | B_imply (a,b)
      | B_eq (a,b) -> yield a; yield b
      | B_and (a,b,c,d) -> yield a; yield b; yield c; yield d

    let ty t = t.term_ty

    let equal = term_equal_
    let hash = term_hash_
    let compare a b = CCOrd.int_ a.term_id b.term_id

    module As_key = struct
        type t = term
        let compare = compare
        let equal = equal
        let hash = hash
    end

    module Map = CCMap.Make(As_key)
    module Tbl = CCHashtbl.Make(As_key)

    let to_seq t yield =
      let rec aux t =
        yield t;
        match t.term_cell with
          | DB _ | Reg _ | Const _ | True | False -> ()
          | App (f,l) -> aux f; List.iter aux l
          | If (a,b,c) -> aux a; aux b; aux c
          | Match (t, m) ->
            aux t;
            ID.Map.iter (fun _ (_,rhs) -> aux rhs) m
          | Switch (u,_) -> aux u (* ignore the table *)
          | Builtin b -> builtin_to_seq b aux
          | Quant (_, _, body)
          | Mu body
          | Fun (_, body) -> aux body
          | Memo_call m -> aux (Lazy.force m.mc_dt.mc_dt_term)
      in
      aux t

    (* return [Some] iff the term is an undefined constant *)
    let as_cst_undef (t:term):
      (cst * Ty.t * cst_info * ty_uninterpreted_slice option) option
      =
      match t.term_cell with
        | Const c -> Typed_cst.as_undefined c
        | _ -> None

    (* return [Some (cstor,ty,args)] if the term is a constructor
       applied to some arguments *)
    let as_cstor_app (t:term): (cst * Ty.t * term list) option =
      match t.term_cell with
        | Const ({cst_kind=Cst_cstor ty; _} as c) -> Some (c,ty,[])
        | App (f, l) ->
          begin match f.term_cell with
            | Const ({cst_kind=Cst_cstor ty; _} as c) -> Some (c,ty,l)
            | _ -> None
          end
        | _ -> None

    let as_domain_elt (t:term): (cst * Ty.t) option =
      match t.term_cell with
        | Const ({cst_kind=Cst_uninterpreted_dom_elt ty; _} as c) -> Some (c,ty)
        | _ -> None

    (* unfold the function into [list of args, body] *)
    let unfold_fun (t:t): ty_h list * t =
      let rec aux acc t = match t.term_cell with
        | Fun (ty, bod) -> aux (ty::acc) bod
        | _ -> List.rev acc, t
      in
      aux [] t

    let fpf = Format.fprintf

    let pp_mc_dt out d = match d.mc_dt_cell with
      | Memo_fail -> CCFormat.string out "fail"
      | Memo_yield -> CCFormat.string out "yield"
      | Memo_if (r,_,_) -> Format.fprintf out "if %d" (fst r)
      | Memo_match (r, _) -> Format.fprintf out "match %d" (fst r)

    let pp_reg out (i,_) = Format.fprintf out "reg_%d" i

    let pp_sym_value out = function
      | Memo_true -> CCFormat.string out "true"
      | Memo_false -> CCFormat.string out "false"
      | Memo_cstor (c,_,[]) -> Format.fprintf out "(cstor %a)" ID.pp c.cst_id
      | Memo_cstor (c,_,regs) ->
        Format.fprintf out "(cstor %a %a)" ID.pp c.cst_id (Utils.pp_list pp_reg) regs
      | Memo_dom_elt c -> Format.fprintf out "(dom_elt %a)" ID.pp c.cst_id

    let pp_mc_ pp_term out m =
      let pp_regs out m =
        Format.fprintf out "(@[<hv>%a@])"
          (IntMap.print ~start:"" ~stop:"" ~arrow:":=" CCFormat.int pp_term) m
      in
      let lazy t = m.mc_dt.mc_dt_term in
      Format.fprintf out
        "(@[<hv1>memo_call %a@ term: %a@ \
         dt: %a @ regs: %a@ blocking: %a@ blocking_sym %a@])"
        ID.pp m.mc_tbl.memo_fun
        pp_term t
        pp_mc_dt m.mc_dt
        pp_regs m.mc_concrete_terms
        (Utils.pp_list pp_dep) m.mc_deps
        (Utils.pp_list pp_dep) t.term_deps

    let pp_top ~ids out t =
      let rec pp out t =
        pp_rec out t;
        if Config.pp_hashcons then Format.fprintf out "/%d" t.term_id;
        ()

      and pp_rec out t = match t.term_cell with
        | True -> CCFormat.string out "true"
        | False -> CCFormat.string out "false"
        | DB d -> DB.pp out d
        | Reg (i,_) -> fpf out "reg_%d" i
        | Const c ->
          if ids then Typed_cst.pp out c else ID.pp_name out c.cst_id
        | App (f,l) ->
          fpf out "(@[<1>%a@ %a@])" pp f (Utils.pp_list pp) l
        | Fun (ty,f) ->
          fpf out "(@[fun %a@ %a@])" Ty.pp ty pp f
        | Quant (q,uty,f) ->
          fpf out "(@[%a %a@ %a@])" pp_quant q pp_uty uty pp f
        | Mu sub -> fpf out "(@[mu@ %a@])" pp sub
        | If (a, b, c) ->
          fpf out "(@[if %a@ %a@ %a@])" pp a pp b pp c
        | Match (t,m) ->
          let pp_bind out (id,(_tys,rhs)) =
            fpf out "(@[<1>case %a@ %a@])" ID.pp id pp rhs
          in
          let print_map =
            CCFormat.seq ~start:"" ~stop:"" ~sep:" " pp_bind
          in
          fpf out "(@[match %a@ (@[<hv>%a@])@])"
            pp t print_map (ID.Map.to_seq m)
        | Switch (t, m) ->
          let pp_case out (lhs,rhs) =
            fpf out "(@[<1>case@ %a@ %a@])" ID.pp lhs pp rhs
          in
          let print_map =
            CCFormat.seq ~start:"" ~stop:"" ~sep:" " pp_case
          in
          fpf out "(@[switch %a@ (@[<hv>%a@])@])"
            pp t print_map (ID.Tbl.to_seq m.switch_tbl)
        | Memo_call m -> pp_mc_ pp out m
        | Builtin (B_not t) -> fpf out "(@[<hv1>not@ %a@])" pp t
        | Builtin (B_and (_, _, a,b)) ->
          fpf out "(@[<hv1>and@ %a@ %a@])" pp a pp b
        | Builtin (B_or (a,b)) ->
          fpf out "(@[<hv1>or@ %a@ %a@])" pp a pp b
        | Builtin (B_imply (a,b)) ->
          fpf out "(@[<hv1>=>@ %a@ %a@])" pp a pp b
        | Builtin (B_eq (a,b)) ->
          fpf out "(@[<hv1>=@ %a@ %a@])" pp a pp b
      in
      pp out t

    let pp = pp_top ~ids:true

    let pp_mc = pp_mc_ pp

    let map
      : f:('b_acc -> t-> t) ->
        bind:('b_acc -> ty_h -> 'b_acc) ->
      'b_acc -> t -> t
      = fun ~f ~bind b_acc t -> match t.term_cell with
        | True
        | False
        | Const _
        | Reg _
        | DB _ -> t
        | App (hd,l) ->
          app (f b_acc hd) (List.map (f b_acc) l)
        | Fun (ty,body) ->
          let b_acc = bind b_acc ty in
          fun_ ty (f b_acc body)
        | Mu t ->
          let b_acc = bind b_acc t.term_ty in
          mu (f b_acc t)
        | If (a,b,c) ->
          if_ (f b_acc a) (f b_acc b) (f b_acc c)
        | Match (u,m) ->
          let u = f b_acc u in
          let m =
            ID.Map.map
              (fun (tys, rhs) ->
                 let b_acc = List.fold_left bind b_acc tys in
                 tys, f b_acc rhs)
              m
          in
          match_ u m
        | Switch (u,m) ->
          let u = f b_acc u in
          let m = {
            m with
              switch_tbl=
                ID.Tbl.to_seq m.switch_tbl
                |> Sequence.map (fun (c,rhs) -> c, f b_acc rhs)
                |> ID.Tbl.of_seq;
          } in
          switch u m
        | Quant (q,uty,body) ->
          let b_acc = bind b_acc (Lazy.force uty.uty_self) in
          quant q uty (f b_acc body)
        | Memo_call m ->
          let m = {
            m with
              mc_concrete_terms=IntMap.map (f b_acc) m.mc_concrete_terms;
          } in
          memo_call m
        | Builtin b ->
          builtin (map_builtin (f b_acc) b)

    (* just evaluate the De Bruijn indices, and return
       the explanations used to evaluate subterms *)
    let eval_db (env:eval_env) (t:term) : term =
      if DB_env.size env = 0
      then t (* trivial *)
      else (
        let rec aux env t : term = match t.term_cell with
          | DB d ->
            begin match DB_env.get d env with
              | None -> t
              | Some t' -> t'
            end
          | Reg _
          | Const _
          | True
          | False -> t
          | Fun (ty, body) ->
            let body' = aux (DB_env.push_none env) body in
            if body==body' then t else fun_ ty body'
          | Mu body ->
            let body' = aux (DB_env.push_none env) body in
            if body==body' then t else mu body'
          | Quant (q, uty, body) ->
            let body' = aux (DB_env.push_none env) body in
            if body==body' then t else quant q uty body'
          | Match (u, m) ->
            let u = aux env u in
            let m =
              ID.Map.map
                (fun (tys,rhs) ->
                   tys, aux (DB_env.push_none_l tys env) rhs)
                m
            in
            match_ u m
          | Switch (u, m) ->
            let u = aux env u in
            (* NOTE: [m] should not contain De Bruijn indices at all *)
            switch u m
          | If (a,b,c) ->
            let a' = aux env a in
            let b' = aux env b in
            let c' = aux env c in
            if a==a' && b==b' && c==c' then t else if_ a' b' c'
          | App (_,[]) -> assert false
          | App (f, l) ->
            let f' = aux env f in
            let l' = aux_l env l in
            if f==f' && CCList.equal (==) l l' then t else app f' l'
          | Builtin b -> builtin (map_builtin (aux env) b)
          | Memo_call _ ->
            t (* NOTE: should not contain De Bruijn indices *)
        and aux_l env l =
          List.map (aux env) l
        in
        aux env t
      )
  end

  let rec to_seq_explanation_ e yield = match e with
    | E_empty -> ()
    | E_leaf x -> yield x
    | E_append (a,b) -> to_seq_explanation_ a yield; to_seq_explanation_ b yield

  let explanation_to_list_uniq_ e : lit list =
    to_seq_explanation_ e
    |> Sequence.to_rev_list
    |> CCList.sort_uniq ~cmp:cmp_lit

  let rec pp_lit out l =
    let pp_lit_view out = function
      | Lit_fresh i -> Format.fprintf out "#%a" ID.pp i
      | Lit_atom t -> Term.pp out t
      | Lit_assign (c,t) ->
        Format.fprintf out "(@[:= %a@ %a@])" Typed_cst.pp c Term.pp t
      | Lit_uty_empty u -> Format.fprintf out "(empty %a)" pp_uty u
    in
    if l.lit_sign then pp_lit_view out l.lit_view
    else Format.fprintf out "(@[@<1>¬@ %a@])" pp_lit_view l.lit_view

  and pp_explanation out (e:explanation) =
    Format.fprintf out "(@[%a@])"
      (Utils.pp_list pp_lit) (explanation_to_list_uniq_ e)

  (** {2 Literals} *)
  module Lit : sig
    type t = lit
    val neg : t -> t
    val abs : t -> t
    val sign : t -> bool
    val view : t -> lit_view
    val as_atom : t -> (term * bool) option
    val fresh_with : ID.t -> t
    val fresh : unit -> t
    val dummy : t
    val atom : ?sign:bool -> term -> t
    val eq : term -> term -> t
    val neq : term -> term -> t
    val cst_choice : cst -> term -> t
    val uty_choice_empty : ty_uninterpreted_slice -> t
    val uty_choice_nonempty : ty_uninterpreted_slice -> t
    val uty_choice_status : ty_uninterpreted_slice -> ty_uninterpreted_status -> t
    val hash : t -> int
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val print : t CCFormat.printer
    val pp : t CCFormat.printer
    val norm : t -> t * FI.negated
    module Set : CCSet.S with type elt = t
  end = struct
    type t = lit

    let neg l = {l with lit_sign=not l.lit_sign}

    let sign t = t.lit_sign
    let view (t:t): lit_view = t.lit_view

    let abs t: t = {t with lit_sign=true}

    let make ~sign v = {lit_sign=sign; lit_view=v}

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

    let atom ?(sign=true) (t:term) : t =
      let t, sign' = Term.abs t in
      let sign = if not sign' then not sign else sign in
      make ~sign (Lit_atom t)

    let eq a b = atom ~sign:true (Term.eq a b)
    let neq a b = atom ~sign:false (Term.eq a b)
    let cst_choice c t = make ~sign:true (Lit_assign (c, t))
    let uty_choice_empty uty = make ~sign:true (Lit_uty_empty uty)
    let uty_choice_nonempty uty : t = make ~sign:false (Lit_uty_empty uty)
    let uty_choice_status uty s : t = match s with
      | Uty_empty -> uty_choice_empty uty
      | Uty_nonempty -> uty_choice_nonempty uty

    let as_atom (lit:t) : (term * bool) option = match lit.lit_view with
      | Lit_atom t -> Some (t, lit.lit_sign)
      | _ -> None

    let hash = hash_lit
    let compare = cmp_lit
    let equal a b = compare a b = 0
    let pp = pp_lit
    let print = pp

    let norm l =
      if l.lit_sign then l, FI.Same_sign else neg l, FI.Negated

    module Set = CCSet.Make(struct type t = lit let compare=compare end)
  end

  module Explanation : sig
    type t = explanation
    val empty : t
    val return : lit -> t
    val cons : lit -> t -> t
    val append : t -> t -> t
    val is_empty : t -> bool
    val to_seq : t -> lit Sequence.t
    val to_list : t -> lit list
    val to_list_uniq : t -> lit list
    val pp : t CCFormat.printer
  end = struct
    type t = explanation
    let empty : t = E_empty
    let return e = E_leaf e
    let append s1 s2 = match s1, s2 with
      | E_empty, _ -> s2
      | _, E_empty -> s1
      | _ -> E_append (s1, s2)
    let cons x e = append (return x) e

    let is_empty = function
      | E_empty -> true
      | E_leaf _
      | E_append _ -> false (* by smart cstor *)

    let to_seq = to_seq_explanation_

    let to_list e =
      let rec aux acc = function
        | E_empty -> acc
        | E_leaf x -> x::acc
        | E_append (a,b) -> aux (aux acc a) b
      in
      aux [] e

    let to_list_uniq = explanation_to_list_uniq_

    let pp = pp_explanation
  end

  (** {2 Clauses} *)

  module Clause : sig
    type t = private {
      lits: Lit.t list;
      id: int;
    }
    val make : Lit.t list -> t
    val lits : t -> Lit.t list
    val conflicts : t Queue.t
    val lemma_queue : t Queue.t
    val push_new : t -> unit
    val push_new_l : t list -> unit
    val push_conflict : t -> unit
    val iter : (Lit.t -> unit) -> t -> unit
    val to_seq : t -> Lit.t Sequence.t
    val pp : t CCFormat.printer
  end = struct
    type t = {
      lits: Lit.t list;
      id: int;
    }

    let lits c = c.lits

    let pp out c = match c.lits with
      | [] -> CCFormat.string out "false"
      | [lit] -> Lit.pp out lit
      | _ ->
        Format.fprintf out "(@[<hv1>or@ %a@ id: %d@])"
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

    let conflicts : t Queue.t = Queue.create ()

    let push_conflict c = Queue.push c conflicts

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
    val next : unit -> state
    val lit_of_depth : int -> Lit.t option
    val pp: t CCFormat.printer
  end = struct
    type t = int

    let pp = CCFormat.int

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
    let lit_of_depth d : Lit.t option =
      if d < step_ || (d mod step_ <> 0) || d > max_depth
      then None
      else match CCHashtbl.get lits_ d with
        | Some l -> Some l
        | None ->
          let lit = mk_lit_ d in
          Hashtbl.add lits_ d lit;
          Some lit

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
      fun ?slice ?exist_if ~parent name ty ->
        let id = ID.makef "?%s_%d" name !n in
        incr n;
        Typed_cst.make_undef ?slice ?exist_if ~parent id ty

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
    let expand_uninterpreted_slice (uty:ty_uninterpreted_slice)
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
          let c_head = Typed_cst.make_uty_dom_elt c_id ty in
          (* create the next slice *)
          let uty_tail = {
            uty_self=uty.uty_self;
            uty_parent=Some uty;
            uty_pair=Lazy_none;
            uty_offset=n+1;
            uty_status=None;
            uty_watched=Poly_set.create 16 ~eq:term_equal_;
          } in
          Log.debugf 5
            (fun k->k "expand slice %a@ into (@[%a,@ %a@])"
                pp_uty uty Typed_cst.pp c_head pp_uty uty_tail);
          (* memoize *)
          uty.uty_pair <- Lazy_some (c_head, uty_tail);
          (* emit clauses *)
          let clauses = clauses_of_uty uty in
          c_head, uty_tail, clauses
        | Lazy_some (hd,tl) ->
          hd, tl, [] (* already expanded *)

    (* build clause(s) that explains that [c] must be one of its
       cases *)
    let clauses_of_cases (c:cst) (l:term list) (depth:int): Clause.t list =
      (* guard for non-constant cases (depth limit) *)
      let lit_guard = Iterative_deepening.lit_of_depth depth in
      let guard_is_some = CCOpt.is_some lit_guard in
      let info = match Typed_cst.as_undefined c with
        | None -> assert false
        | Some (_,_,info,_) -> info
      in
      let guard_parent =
        List.map
          (fun (lazy lits) -> lits)
          !(info.cst_exist_conds)
      in
      (* lits with a boolean indicating whether they have
           to be depth-guarded *)
      let lits =
        List.map
          (fun rhs ->
             let lit = Lit.cst_choice c rhs in
             (* does [rhs] use constants deeper than [d]? *)
             let needs_guard =
               guard_is_some &&
               Term.to_seq rhs
               |> Sequence.exists
                 (fun sub -> match sub.term_cell with
                    | Const {cst_kind=Cst_undef (_,info,_); _} ->
                      (* is [sub] a constant deeper than [d]? *)
                      info.cst_depth > depth
                    | Switch (_,{switch_cst={cst_kind=Cst_undef (_,info,_); _}; _}) ->
                      (* in this case, the map will contain metas of depth
                         [info.cst_depth+1], even though they might not
                         exist already *)
                      info.cst_depth >= depth
                    | _ -> false)
             in
             lit, needs_guard)
          l
      in
      (* if all cases go over the depth limit, then we must revert the
         choice of [parent] *)
      let all_need_guard = List.for_all snd lits in
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
          (fun (lit,needs_guard) ->
             match lit_guard, needs_guard with
               | None, true -> assert false
               | Some guard, true ->
                 (* depth limit and this literal are incompatible *)
                 [Clause.make [ Lit.neg lit; Lit.neg guard ]]
               | _ -> [])
          lits
      in
      cs_possible_depth @ cs_limit @ cs_choose @ cs_once

    (* build the disjunction [l] of cases for [info]. Might expand other
       objects, such as uninterpreted slices. *)
    let expand_cases
        (cst:cst)
        (ty:Ty.t)
        (info:cst_info)
        : term list * Clause.t list  =
      assert (info.cst_cases = Lazy_none);
      (* make a sub-constant with given type *)
      let mk_sub_cst ?slice ?exist_if ~parent ty_arg =
        let basename = Ty.mangle ty_arg in
        new_cst_ ?slice ?exist_if basename ty_arg ~parent
      in
      (* table of already built constants, by type *)
      let memo : (cst * cst_exist_conds) list Ty.Tbl.t = Ty.Tbl.create 16 in
      (* get or create a constant that has this type *)
      let get_or_create_cst
          ~(parent:cst) ~(used:cst list ref) ty_arg
          : cst * cst_exist_conds =
        let usable =
          Ty.Tbl.get_or ~or_:[] memo ty_arg
          |> List.filter
            (fun (c',_) -> not (List.exists (Typed_cst.equal c') !used))
        in
        match usable with
          | [] ->
            (* make a new constant and remember it *)
            let plist = ref [] in
            let cst = mk_sub_cst ~exist_if:plist ~parent ty_arg in
            Ty.Tbl.add_list memo ty_arg (cst,plist);
            used := cst :: !used; (* cannot use it in the same case *)
            cst, plist
          | (cst,plist) :: _ ->
            (* [cst] has the proper type, and is not used yet *)
            used := cst :: !used;
            cst, plist
      in
      (* expand constant depending on its type *)
      let by_ty, other_clauses = match Ty.view ty with
        | Atomic (_, Data cstors) ->
          (* datatype: refine by picking the head constructor *)
          info.cst_complete <- true;
          List.map
            (fun (lazy c) ->
               let rec case = lazy (
                 let ty_args, _ = Typed_cst.ty c |> Ty.unfold in
                 (* elements of [memo] already used when generating the
                    arguments of this particular case,
                    so we do not use a constant twice *)
                 let used = ref [] in
                 let args =
                   List.map
                     (fun ty_arg ->
                        let c, plist =
                          get_or_create_cst ty_arg ~parent:cst ~used
                        in
                        let cond = lazy (Lit.cst_choice cst (Lazy.force case)) in
                        plist := cond :: !plist;
                        Term.const c)
                     ty_args
                 in
                 Term.app_cst c args
               ) in
               Lazy.force case)
            cstors, []
        | Atomic (_, Uninterpreted uty_root) ->
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
          info.cst_complete <- false;
          let case1 = Term.const c_head in
          let case2 =
            let cond = lazy (Lit.uty_choice_nonempty uty) in
            let plist = ref [cond] in
            (* [cst = cst'], but [cst'] is deeper and belongs to the next slice *)
            let cst' = mk_sub_cst ty ~slice:uty_tail ~exist_if:plist ~parent:cst in
            Term.const cst'
          in
          (* additional clause to specify that [is_empty uty_tail => cst = case1] *)
          let c_not_empty =
            [Lit.neg (Lit.uty_choice_empty uty_tail); Lit.cst_choice cst case1]
            |> Clause.make
          in
          [case1; case2], c_not_empty :: cs
        | Arrow (ty_arg, ty_ret) ->
          (* synthesize a function [fun x:ty_arg. body]
             where [body] will destruct [x] depending on its type *)
          let the_param = Term.db (DB.make 0 ty_arg) in
          let rec body = lazy (
            (* only one parent in any case *)
            let exist_if = ref [lazy (Lit.cst_choice cst (Lazy.force fun_))] in
            match Ty.view ty_arg with
            | Prop ->
              (* make a test on [the_param] *)
              let then_ = mk_sub_cst ty_ret ~parent:cst ~exist_if |> Term.const in
              let else_ = mk_sub_cst ty_ret ~parent:cst ~exist_if |> Term.const in
              Term.if_ the_param then_ else_
            | Atomic (_, Data cstors) ->
              (* match without recursion on some parameter *)
              let m =
                cstors
                |> List.map
                  (fun (lazy cstor) ->
                     let ty_cstor_args, _ =
                       Typed_cst.ty cstor |> Ty.unfold
                     in
                     let n_ty_args = List.length ty_cstor_args in
                     (* build a function over the cstor arguments *)
                     let ty_sub_f = Ty.arrow_l ty_cstor_args ty_ret in
                     let sub_f = mk_sub_cst ty_sub_f ~parent:cst ~exist_if in
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
                let sub = mk_sub_cst ty_ret ~parent:cst ~exist_if in
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
          and fun_ =
            lazy (Term.fun_ ty_arg (Lazy.force body))
          in
          [Lazy.force fun_], []
        | Prop ->
          (* simply try true/false *)
          [Term.true_; Term.false_], []
      in
      (* build clauses *)
      let case_clauses = clauses_of_cases cst by_ty info.cst_depth in
      by_ty, List.rev_append other_clauses case_clauses
  end

  let pp_dep_full out = function
    | Dep_cst c ->
      let i = match Typed_cst.as_undefined c with
        | None -> assert false
        | Some (_,_,i,_) -> i
      in
      let nf = match i.cst_cur_case with
        | None -> Term.const c
        | Some (_, t') -> t'
      in
      Format.fprintf out
        "(@[%a@ nf:%a@ :expanded %B@])"
        Typed_cst.pp c Term.pp nf
        (match Typed_cst.as_undefined c with
          | None -> assert false
          | Some (_,_,i,_) -> i.cst_cases <> Lazy_none)
    | Dep_uty uty ->
      Format.fprintf out
        "(@[%a@ :expanded %B@])"
        pp_uty uty (uty.uty_pair<>Lazy_none)
    | Dep_reg (i,ty) ->
      Format.fprintf out "(@[reg %d@ ty: %a@])" i Ty.pp ty

  (* from explanation [e1, e2, ..., en] build the guard
         [e1 & e2 & ... & en => …], that is, the clause
         [not e1 | not e2 | ... | not en] *)
  let clause_guard_of_exp_ (e:explanation): Lit.t list =
    Explanation.to_list e
    |> List.map Lit.neg (* this is a guard! *)
    |> CCList.sort_uniq ~cmp:Lit.compare

  module Memo_utils : sig
    val find_register : 'a registers -> int -> 'a
    (** find the content of this register, or fails *)

    val subst : term registers -> term -> term
    (** Substitute registers in this term *)

    val is_value : term -> bool
    (** is the term a "value" (i.e. head symbol is cstor/true/false/dom_elt) *)
  end = struct
    let find_register (r:'a registers) (i:int): 'a =
      try IntMap.find i r
      with Not_found -> errorf "cannot find register %d" i

    let rec subst regs t = match t.term_cell with
      | Reg (i,_) ->
        begin match IntMap.get i regs with
          | None -> t
          | Some t' -> t'
        end
      | _ ->
        Term.map () t
          ~bind:(fun () _ -> ())
          ~f:(fun _ t' -> subst regs t')

    let is_value t = match t.term_cell with
      | True
      | False -> true
      | _ ->
        CCOpt.is_some (Term.as_cstor_app t) ||
        CCOpt.is_some (Term.as_domain_elt t)
  end

  (** {2 Reduction to Normal Form} *)
  module Reduce = struct
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

    (* set the normal form of [t], propagate to watchers *)
    let set_nf_ t new_t (e:explanation) : unit =
      if Term.equal t new_t then ()
      else (
        Backtrack.push_set_nf_ t;
        t.term_nf <- Some (new_t, e);
        Log.debugf 5
          (fun k->k
              "(@[<hv1>set_nf@ @[%a@]@ @[%a@]@ :explanation @[<hv>%a@]@])"
              Term.pp t Term.pp new_t Explanation.pp e);
      )

    let get_nf t : explanation * term =
      match t.term_nf with
        | None -> Explanation.empty, t
        | Some (new_t,e) -> e, new_t

    (* FIXME: remove *)
    let as_uninterpreted_dom_elt (t:term): ID.t option =
      match t.term_cell with
        | Const {cst_kind=Cst_uninterpreted_dom_elt _; cst_id; _} -> Some cst_id
        | _ -> None

    (* compute the normal form of this term. We know at least one of its
       subterm(s) has been reduced *)
    let rec compute_nf (t:term) : explanation * term =
      (* follow the "normal form" pointer *)
      match t.term_nf with
        | Some (t', e) ->
          let exp, nf = compute_nf_add e t' in
          (* path compression here *)
          if not (Term.equal t' nf)
          then set_nf_ t nf exp;
          exp, nf
        | None -> compute_nf_noncached t

    and compute_nf_noncached t =
      assert (t.term_nf = None);
      match t.term_cell with
        | DB _
        | Reg _ -> Explanation.empty, t
        | True | False ->
          Explanation.empty, t (* always trivial *)
        | Const c ->
          begin match c.cst_kind with
            | Cst_defined (_, rhs, _) ->
              (* expand defined constants *)
              compute_nf (Lazy.force rhs)
            | Cst_undef (_, {cst_cur_case=Some (e,new_t); _}, _) ->
              (* c := new_t, we can reduce *)
              compute_nf_add e new_t
            | Cst_undef _ | Cst_uninterpreted_dom_elt _ | Cst_cstor _ ->
              Explanation.empty, t
          end
        | Fun _ -> Explanation.empty, t (* no eval under lambda *)
        | Mu body ->
          (* [mu x. body] becomes [body[x := mu x. body]] *)
          let env = DB_env.singleton t in
          Explanation.empty, Term.eval_db env body
        | Quant (q,uty,body) ->
          begin match uty.uty_status with
            | None -> Explanation.empty, t
            | Some (e, status) ->
              let c_head, uty_tail = match uty.uty_pair with
                | Lazy_none -> assert false
                | Lazy_some tup -> tup
              in
              let t1() =
                Term.eval_db (DB_env.singleton (Term.const c_head)) body
              in
              let t2() =
                Term.quant q uty_tail body
              in
              begin match q, status with
                | Forall, Uty_empty -> e, Term.true_
                | Exists, Uty_empty -> e, Term.false_
                | Forall, Uty_nonempty ->
                  (* [uty[n:] = a_n : uty[n+1:]], so the
                     [forall uty[n:] p] becomes [p a_n && forall uty[n+1:] p] *)
                  let t' = Term.and_l [t1(); t2()] in
                  compute_nf_add e t'
                | Exists, Uty_nonempty ->
                  (* converse of the forall case, it becomes a "or" *)
                  let t' = Term.or_l [t1(); t2()] in
                  compute_nf_add e t'
              end
          end
        | Builtin b ->
          (* try boolean reductions *)
          let e, t' = compute_builtin ~old:t b in
          set_nf_ t t' e;
          e, t'
        | If (a,b,c) ->
          let e_a, a' = compute_nf a in
          let default() =
            if a==a' then t else Term.if_ a' b c
          in
          let e_branch, t' = match a'.term_cell with
            | True -> compute_nf b
            | False -> compute_nf c
            | _ -> Explanation.empty, default()
          in
          (* merge evidence from [a]'s normal form and [b/c]'s
             normal form *)
          let e = Explanation.append e_a e_branch in
          set_nf_ t t' e;
          e, t'
        | Match (u, m) ->
          let e_u, u' = compute_nf u in
          let default() =
            if u==u' then t else Term.match_ u' m
          in
          let e_branch, t' = match Term.as_cstor_app u' with
            | Some (c, _, l) ->
              begin match ID.Map.get (Typed_cst.id c) m with
                | Some (tys, rhs) ->
                  if List.length tys = List.length l
                  then (
                    (* evaluate arguments *)
                    let env = DB_env.push_l l DB_env.empty in
                    (* replace in [rhs] *)
                    let rhs = Term.eval_db env rhs in
                    (* evaluate new [rhs] *)
                    compute_nf rhs
                  )
                  else Explanation.empty, default()
                | None ->
                  Format.printf "term %a@ cstor %a@." Term.pp u' Typed_cst.pp c;
                  assert false
              end
            | None -> Explanation.empty, default()
          in
          let e = Explanation.append e_u e_branch in
          set_nf_ t t' e;
          e, t'
        | Switch (u, m) ->
          let e_u, u' = compute_nf u in
          begin match as_uninterpreted_dom_elt u' with
            | Some u_id ->
              (* do a lookup for this value! *)
              let rhs =
                match ID.Tbl.get m.switch_tbl u_id with
                  | Some rhs -> rhs
                  | None ->
                    (* add an entry, by generating a new RHS *)
                    let rhs = m.switch_make_new () in
                    ID.Tbl.add m.switch_tbl u_id rhs;
                    rhs
              in
              (* continue evaluation *)
              compute_nf_add e_u rhs
            | None ->
              (* block again *)
              let t' = if u==u' then t else Term.switch u' m in
              e_u, t'
          end
        | App ({term_cell=Const {cst_kind=Cst_cstor _; _}; _}, _) ->
          Explanation.empty, t (* do not reduce under cstors *)
        | App ({term_cell=
                  Const
                    {cst_kind=
                       Cst_defined (ty, _, Cst_memoizable tbl);_}; _}, l)
          when List.length l = List.length (Ty.unfold ty |> fst) ->
          assert (tbl.memo_arity > 0);
          (* fully applied memoizable function: transfer to a memoized call *)
          let t' = memo_call_init tbl l in
          compute_nf t'
        | App (f, l) ->
          let e_f, f' = compute_nf f in
          (* now beta-reduce if needed *)
          let e_reduce, new_t =
            compute_nf_app DB_env.empty Explanation.empty f' l
          in
          (* merge explanations *)
          let e = Explanation.append e_reduce e_f in
          set_nf_ t new_t e;
          e, new_t
        | Memo_call m ->
          compute_nf_memo_call m

    (* apply [f] to [l], until no beta-redex is found *)
    and compute_nf_app env e f l = match f.term_cell, l with
      | Const {cst_kind=Cst_defined (_, lazy def_f, _); _}, l ->
        (* reduce [f l] into [def_f l] when [f := def_f] *)
        compute_nf_app env e def_f l
      | Fun (_ty, body), arg :: other_args ->
        (* beta-reduce *)
        assert (Ty.equal _ty arg.term_ty);
        let new_env = DB_env.push arg env in
        (* apply [body] to [other_args] *)
        compute_nf_app new_env e body other_args
      | _ ->
        (* cannot reduce, unless [f] reduces to something else. *)
        let e_f, f' = compute_nf (Term.eval_db env f) in
        let exp = Explanation.append e e_f in
        if Term.equal f f'
        then (
          (* no more reduction *)
          let t' = Term.app f' l in
          exp, t'
        ) else (
          (* try it again *)
          compute_nf_app DB_env.empty exp f' l
        )

    (* compute nf of [t], append [e] to the explanation *)
    and compute_nf_add (e : explanation) (t:term) : explanation * term =
      let e', t' = compute_nf t in
      Explanation.append e e', t'

    (* compute the builtin, assuming its components are
       already reduced *)
    and compute_builtin ~(old:term) (bu:builtin): explanation * term = match bu with
      | B_not a ->
        let e_a, a' = compute_nf a in
        begin match a'.term_cell with
          | True -> e_a, Term.false_
          | False -> e_a, Term.true_
          | _ ->
            let t' = if a==a' then old else Term.not_ a' in
            e_a, t'
        end
      | B_or (a,b) ->
        (* [a or b] becomes [not (not a and not b)] *)
        let a' = Term.not_ a in
        let b' = Term.not_ b in
        compute_nf (Term.not_ (Term.and_par a' b' a' b'))
      | B_imply (a,b) ->
        (* [a => b] becomes [not [a and not b]] *)
        let b' = Term.not_ b in
        compute_nf (Term.not_ (Term.and_par a b' a b'))
      | B_eq (a,b) when Ty.is_prop a.term_ty ->
        let e_a, a' = compute_nf a in
        let e_b, b' = compute_nf b in
        let e_ab = Explanation.append e_a e_b in
        begin match a'.term_cell, b'.term_cell with
          | True, True
          | False, False -> e_ab, Term.true_
          | True, False
          | False, True -> e_ab, Term.false_
          | _ when Term.equal a' b' -> e_ab, Term.true_
          | _ ->
            let t' =
              if a==a' && b==b' then old else Term.eq a' b'
            in
            e_ab, t'
        end
      | B_and (a,b,c,d) ->
        (* evaluate [c] and [d], but only provide some explanation
           once their conjunction reduces to [true] or [false].
           In case of [false], discard the explanation of the other component.

           We first compute only [c], in case it is [False]. *)
        let e_a, c' = compute_nf a in
        begin match c'.term_cell with
          | False ->
            e_a, Term.false_
          | _ ->
            let e_b, d' = compute_nf b in
            begin match c'.term_cell, d'.term_cell with
              | _, False ->
                e_b, Term.false_
              | True, True ->
                let e_ab = Explanation.append e_a e_b in
                e_ab, Term.true_
              | _ ->
                let t' =
                  if c==c' && d==d' then old else Term.and_par a b c' d'
                in
                (* keep the explanations for when the value is true/false *)
                Explanation.empty, t'
            end
        end
      | B_eq (a,b) ->
        let e_a, a' = compute_nf a in
        let e_b, b' = compute_nf b in
        let e_ab = Explanation.append e_a e_b in
        let default() =
          if a==a' && b==b' then old else Term.eq a' b'
        in
        if Term.equal a' b'
        then e_ab, Term.true_ (* syntactic *)
        else begin match Term.as_cstor_app a', Term.as_cstor_app b' with
          | Some (c1,ty1,l1), Some (c2,_,l2) ->
            if not (Typed_cst.equal c1 c2)
            then
              (* [c1 ... = c2 ...] --> false, as distinct constructors
                 can never be equal *)
              e_ab, Term.false_
            else if Typed_cst.equal c1 c2
                 && List.length l1 = List.length l2
                 && List.length l1 = List.length (fst (Ty.unfold ty1))
            then (
              (* same constructor, fully applied -> injectivity:
                 arguments are pairwise equal.
                 We need to evaluate the arguments further (e.g.
                 if they start with constructors) *)
              List.map2 Term.eq l1 l2
              |> Term.and_l
              |> compute_nf_add e_ab
            )
            else e_ab, default()
          | Some (_, _, l), None when cycle_check_l ~sub:b' l ->
            (* acyclicity rule *)
            e_ab, Term.false_
          | None, Some (_, _, l) when cycle_check_l ~sub:a' l ->
            e_ab, Term.false_
          | _ ->
            begin match Term.as_domain_elt a', Term.as_domain_elt b' with
              | Some (c1,ty1), Some (c2,ty2) ->
                (* domain elements: they are all distinct *)
                assert (Ty.equal ty1 ty2);
                if Typed_cst.equal c1 c2
                then e_ab, Term.true_
                else e_ab, Term.false_
              | _ -> e_ab, default()
            end
        end

    (* compute and memoize *)
    and compute_nf_memo_call (m:memo_call): explanation * term =
      (* try and see whether the given register evaluates to a concrete value.
           @return the new memo_call (possibly updated with new registers)
           and [Some symbolic_value], or [None] *)
      let as_value (m:memo_call) (r:int) : memo_call * memo_symbolic_value option =
        let t_concrete = Memo_utils.find_register m.mc_concrete_terms r in
        let e_concrete, nf_concrete = compute_nf t_concrete in
        (* add explanation now *)
        let m =
          if Explanation.is_empty e_concrete &&
             Term.equal t_concrete nf_concrete
          then m (* same old *)
          else
            {m with
               mc_explanation=Explanation.append e_concrete m.mc_explanation;
               mc_concrete_terms=IntMap.add r nf_concrete m.mc_concrete_terms;
            } |> mk_memo_call
        in
        begin match nf_concrete.term_cell with
          | True ->
            let v = Memo_true in
            assert (m.mc_deps=[]);
            m, Some v
          | False ->
            let v = Memo_false in
            assert (m.mc_deps=[]);
            m, Some v
          | _ ->
            begin match
                Term.as_cstor_app nf_concrete,
                Term.as_domain_elt nf_concrete
              with
                | Some _, Some _ -> assert false
                | Some (cstor, ty, args), None ->
                  (* allocate new registers for the arguments *)
                  let (_,concrete_regs), sub_regs =
                    CCList.fold_map
                      (fun (n,c_regs) arg ->
                         let reg = n, arg.term_ty in
                         (n+1, IntMap.add n arg c_regs), reg)
                      (m.mc_dt.mc_dt_offset, m.mc_concrete_terms) args
                  in
                  let v = Memo_cstor (cstor, ty, sub_regs) in
                  let m = {m with mc_concrete_terms=concrete_regs;} in
                  m, Some v
                | None, Some (dom_elt,_) ->
                  let v = Memo_dom_elt dom_elt in
                  m, Some v
                | None, None ->
                  (* not a value yet, something blocks *)
                  assert (m.mc_deps<>[]);
                  m, None
            end
        end
      (* substitute [reg] with [by] in [t], and reduce. Typically used
         during traversal of decision tree *)
      and apply_reg ~reg ~by t =
        let t' = Memo_utils.subst (IntMap.singleton reg by) t in
        let e, nf = compute_nf t' in
        assert (Explanation.is_empty e);
        nf
      in
      (* main traversal of the memo decision tree *)
      let rec aux (m:memo_call): explanation * term =
        Log.debugf 5
          (fun k->k "(@[compute_nf_memo_call@ %a@])" Term.pp_mc m);
        match m.mc_dt.mc_dt_cell with
          | Memo_fail -> aux_fail m
          | Memo_yield -> aux_yield m
          | Memo_match (reg, map) ->
            aux_match m reg map
          | Memo_if (reg, then_, else_) ->
            aux_if m reg then_ else_

      and aux_yield m =
        assert (m.mc_dt.mc_dt_cell = Memo_yield);
        (* return the normal form, with concrete values replacing registers *)
        let lazy term = m.mc_dt.mc_dt_term in
        let nf_concrete = Memo_utils.subst m.mc_concrete_terms term in
        Log.debugf 5
          (fun k->k "(@[memo: yield %a@ expl: %a@])"
              Term.pp nf_concrete Explanation.pp m.mc_explanation);
        m.mc_explanation, nf_concrete

      and aux_if m (i,_) then_ else_ = match as_value m i with
        | m, Some Memo_true ->
          {m with mc_dt=then_} |> mk_memo_call |> aux
        | m, Some Memo_false ->
          {m with mc_dt=else_} |> mk_memo_call |> aux
        | _, Some _ -> assert false (* typing *)
        | m, None ->
          (* blocked, for now *)
          Explanation.empty, Term.memo_call m

      and aux_match m (i,_) dt_map = match as_value m i with
        | m, Some (Memo_cstor (cstor, _, sub_regs)) ->
          (* follow corresponding branch *)
          begin match ID.Map.get cstor.cst_id dt_map with
            | Some (sub_regs', sub_dt) ->
              assert (CCList.equal eq_reg sub_regs sub_regs');
              {m with mc_dt=sub_dt} |> mk_memo_call |> aux
            | None ->
              errorf
                "decision tree on reg %d@ does not have branch for cstor %a"
                i ID.pp cstor.cst_id
          end
        | _, Some _ -> assert false (* typing *)
        | m, None ->
          (* blocked, for now *)
          Explanation.empty, Term.memo_call m

      (* in case of failure *)
      and aux_fail m =
        assert (m.mc_dt.mc_dt_cell = Memo_fail);
        (* see where symbolic computation blocks *)
        let lazy nf_symb = m.mc_dt.mc_dt_term in
        assert (Term.equal (snd (compute_nf nf_symb)) nf_symb);
        begin match nf_symb.term_deps with
          | [] ->
            (* reached a normal form! *)
            assert (Memo_utils.is_value nf_symb);
            m.mc_dt.mc_dt_cell <- Memo_yield;
            aux_yield m
          | Dep_reg ((r_idx,_) as r) :: _ ->
            (* evaluation has not reached a value yet, because of
               register [r1], corresponding to some concrete term *)
            begin match as_value m r_idx with
              | m, Some v ->
                let set_cell new_cell =
                  (* remove "fail", replace with new decision *)
                  Log.debugf 5
                    (fun k->k "(@[<hv1>memo_set_cell@ %a@ %a@])"
                        Term.pp_mc m Term.pp_mc_dt {m.mc_dt with mc_dt_cell=new_cell});
                  assert (m.mc_dt.mc_dt_cell = Memo_fail);
                  m.mc_dt.mc_dt_cell <- new_cell;
                in
                (* register does not block any longer. proceed! *)
                begin match v with
                  | Memo_true | Memo_false ->
                    (* decision tree node is a if/then/else *)
                    let then_ = {
                      mc_dt_term=lazy
                        (apply_reg ~reg:r_idx ~by:Term.true_ nf_symb);
                      mc_dt_offset=m.mc_dt.mc_dt_offset;
                      mc_dt_cell=Memo_fail;
                    } and else_ = {
                      mc_dt_term=lazy
                        (apply_reg ~reg:r_idx ~by:Term.false_ nf_symb);
                      mc_dt_offset=m.mc_dt.mc_dt_offset;
                      mc_dt_cell=Memo_fail;
                    } in
                    set_cell (Memo_if (r, then_, else_));
                    let sub_tree =
                      if v=Memo_true then then_ else else_
                    in
                    {m with mc_dt=sub_tree} |> mk_memo_call |> aux
                  | Memo_cstor (cstor, ty, sub_regs) ->
                    let _, ty_ret = Ty.unfold ty in
                    (* make a shallow match node *)
                    let dt_map = match ty_ret.ty_cell with
                      | Atomic (_, Data cstors) ->
                        Sequence.of_list cstors
                        |> Sequence.map
                          (fun (lazy cstor) ->
                             let ty_args, _ =
                               Ty.unfold (Typed_cst.ty cstor)
                             in
                             (* allocate sub-registers *)
                             let new_offset, sub_regs =
                               CCList.fold_map
                                 (fun n ty_arg -> n+1, (n, ty_arg))
                                 m.mc_dt.mc_dt_offset ty_args
                             in
                             let symb_term =
                               Term.app_cst cstor (List.map Term.reg sub_regs)
                             in
                             let sub = {
                               mc_dt_offset=new_offset;
                               mc_dt_term=lazy (
                                 apply_reg nf_symb ~reg:r_idx ~by:symb_term);
                               mc_dt_cell=Memo_fail;
                             } in
                             cstor.cst_id, (sub_regs, sub))
                        |> ID.Map.of_seq
                      | _ -> assert false
                    in
                    (* which of the branches shall we follow? *)
                    let sub_dt =
                      try
                        let sub_regs', dt = ID.Map.find cstor.cst_id dt_map in
                        assert (CCList.equal eq_reg sub_regs sub_regs');
                        dt
                      with Not_found ->
                        errorf "wrong constructor %a" ID.pp cstor.cst_id
                    in
                    set_cell (Memo_match (r, dt_map));
                    {m with mc_dt=sub_dt} |> mk_memo_call |> aux
                  | Memo_dom_elt _ ->
                    assert false (* TODO: extensible switch table in memo_dt *)
                end
              | m, None ->
                (* the concrete term is blocked *)
                Explanation.empty, Term.memo_call m
            end
          | dep :: _ ->
            Log.debugf 1
              (fun k->k
                  "unexpected concrete dep %a in symbolic computation" pp_dep dep);
            assert false (* purely symbolic computation *)
        end
      in
      aux m

    (* call the memoized function *)
    and memo_call_init (f:memo_tbl) (args:term list): term =
      let n = f.memo_arity in
      assert (n > 0);
      assert (n = List.length args);
      (* reduce arguments to their current normal form, so that
         information on their dependencies is relevant *)
      let expl, args =
        CCList.fold_map compute_nf_add Explanation.empty args
      in
      (* put arguments into registers *)
      let regs =
        CCList.Idx.foldi
          (fun m i arg -> IntMap.add i arg m)
          IntMap.empty args
      in
      let mc = {
        mc_tbl=f;
        mc_deps=[]; (* fake *)
        mc_concrete_terms=regs;
        mc_dt=f.memo_dtree;
        mc_explanation=expl;
      } |> mk_memo_call
      in
      Term.memo_call mc

    (* smart constructor for [memo_call] *)
    and mk_memo_call (m:memo_call): memo_call =
      let lazy t = m.mc_dt.mc_dt_term in
      assert (
        let e_t, t_nf = compute_nf t in
        Term.equal t t_nf && Explanation.is_empty e_t);
      (* dependencies: the symbolic computation [t] might be blocked by
         some register(s). The actual dependencies come from the
         concrete terms contained in those registers. *)
      let deref_deps (d:term_dep): term_dep list = match d with
        | Dep_reg (i,_) ->
          let t = Memo_utils.find_register m.mc_concrete_terms i in
          t.term_deps
        | _ -> [d]
      in
      let deps = CCList.flat_map deref_deps t.term_deps in
      let mc = {
        m with
        mc_deps=deps;
      } in
      mc

    let compute_nf_lit (lit:lit): explanation * lit =
      match Lit.view lit with
        | Lit_fresh _
        | Lit_assign (_,_)
        | Lit_uty_empty _
          -> Explanation.empty, lit
        | Lit_atom t ->
          let e, t' = compute_nf t in
          e, Lit.atom ~sign:(Lit.sign lit) t'
  end

  (** {2 A literal asserted to SAT}

      We watch those literals depending on the set of constants
      that block their current normal form *)

  module Watched_lit : sig
    type t = private term

    val to_lit : t -> Lit.t
    val pp : t CCFormat.printer
    val watch : t -> unit
    val watch_term : term -> unit
    val update_watches_of : t -> unit
    val update_watches_of_term : term -> unit
    val is_watched : t -> bool
    val size : unit -> int
    val to_seq : t Sequence.t
  end = struct
    type t = term
    (* actually, the watched lit is [Lit.atom t], but we link
       [t] directly because this way we have direct access to its
       normal form *)

    let to_lit = Lit.atom ~sign:true
    let pp = Term.pp

    (* clause for [e => l] *)
    let clause_imply (l:lit) (e:explanation): Clause.t =
      let c = l :: clause_guard_of_exp_ e |> Clause.make in
      c

    let propagate_lit_ (l:t) (e:explanation): unit =
      let c = clause_imply (to_lit l) e in
      Log.debugf 4
        (fun k->k
            "(@[<hv1>@{<green>propagate_lit@}@ %a@ nf: %a@ clause: %a@])"
            pp l pp (snd (Reduce.compute_nf l)) Clause.pp c);
      incr stat_num_propagations;
      Clause.push_new c;
      ()

    (* expand the given constant so that, later, it will be
       assigned a value by the SAT solver *)
    let expand_cst (c:cst): unit =
      let ty, info = match c.cst_kind with
        | Cst_undef (ty,i,_) -> ty,i
        | Cst_defined _ | Cst_cstor _ | Cst_uninterpreted_dom_elt _ ->
          assert false
      in
      (* we should never have to expand a meta that is too deep *)
      let depth = info.cst_depth in
      assert (depth <= (Iterative_deepening.current_depth() :> int));
      (* check whether [c] is expanded *)
      begin match info.cst_cases with
        | Lazy_none ->
          (* [c] is blocking, not too deep, but not expanded *)
          let l, clauses = Expand.expand_cases c ty info in
          Log.debugf 2
            (fun k->k "(@[<1>expand_cst@ @[%a@]@ :into (@[%a@])@ :depth %d@])"
                Typed_cst.pp c (Utils.pp_list Term.pp) l depth);
          info.cst_cases <- Lazy_some l;
          incr stat_num_cst_expanded;
          Clause.push_new_l clauses
        | Lazy_some _ -> ()
      end

    let expand_uty (uty:ty_uninterpreted_slice): unit =
      (* we should never have to expand a type slice that is too deep *)
      let depth = uty.uty_offset in
      assert (depth <= (Iterative_deepening.current_depth() :> int));
      (* check whether [c] is expanded *)
      begin match uty.uty_pair with
        | Lazy_none ->
          (* [uty] is blocking, not too deep, but not expanded *)
          let c_head, uty_tail, clauses = Expand.expand_uninterpreted_slice uty in
          Log.debugf 2
            (fun k->k
                "(@[<1>expand_uty@ @[%a@]@ :into (@[%a ++@ %a@])@ :depth %d@])"
                pp_uty uty Typed_cst.pp c_head pp_uty uty_tail depth);
          uty.uty_pair <- Lazy_some (c_head, uty_tail);
          incr stat_num_uty_expanded;
          Clause.push_new_l clauses
        | Lazy_some _ -> ()
      end

    (* add [t] to the list of literals that watch the constant [c] *)
    let watch_cst_ (t:t)(c:cst) : unit =
      assert (Ty.is_prop t.term_ty);
      Log.debugf 2
        (fun k->k "(@[<1>watch_cst@ %a@ %a@])" Typed_cst.pp c Term.pp t);
      let _, info = match c.cst_kind with
        | Cst_undef (ty,i,_) -> ty,i
        | Cst_defined _ | Cst_cstor _ | Cst_uninterpreted_dom_elt _ ->
          assert false
      in
      Poly_set.add info.cst_watched t;
      expand_cst c;
      ()

    (* add [t] to the list of literals that watch this slice *)
    let watch_uty (t:t)(uty:ty_uninterpreted_slice) : unit =
      assert (Ty.is_prop t.term_ty);
      Log.debugf 2
        (fun k->k "(@[<1>watch_uty@ %a@ %a@])" pp_uty uty Term.pp t);
      Poly_set.add uty.uty_watched t;
      expand_uty uty;
      ()

    let watch_dep (t:t) (d:term_dep) : unit = match d with
      | Dep_cst c -> watch_cst_ t c
      | Dep_uty uty -> watch_uty t uty
      | Dep_reg _ -> assert false

    (* ensure that [t] is on the watchlist of all the
       constants it depends on;
       also ensure those constants are expanded *)
    let update_watches_of (t:t): unit =
      assert (Ty.is_prop t.term_ty);
      let e, new_t = Reduce.compute_nf t in
      (* if [new_t = true/false], propagate literal *)
      begin match new_t.term_cell with
        | True -> propagate_lit_ t e
        | False -> propagate_lit_ (Term.not_ t) e
        | _ ->
          (* partially evaluated literal: add [t] (not its
             temporary normal form) to the watch list of every
             blocking constant *)
          Log.debugf 4
            (fun k->k
                "(@[<1>update_watches@ %a@ @[<1>:normal_form@ %a@]@ \
                 :deps (@[%a@])@ :exp @[<hv>%a@]@])"
                Term.pp t Term.pp new_t
                (Utils.pp_list pp_dep) new_t.term_deps
                Explanation.pp e);
          List.iter (watch_dep t) new_t.term_deps;
      end;
      ()

    let update_watches_of_term = update_watches_of

    let watched_ : unit Term.Tbl.t = Term.Tbl.create 256

    let watch (lit:t) =
      let lit, _ = Term.abs lit in
      if not (Term.Tbl.mem watched_ lit) then (
        Log.debugf 3
          (fun k->k "(@[<1>@{<green>watch_lit@}@ %a@])" pp lit);
        Term.Tbl.add watched_ lit ();
        (* also ensure it is watched properly *)
        update_watches_of lit;
      )

    let watch_term = watch

    let is_watched (lit:t) : bool =
      let lit, _ = Term.abs lit in
      Term.Tbl.mem watched_ lit

    let to_seq = Term.Tbl.keys watched_

    let size () = Term.Tbl.length watched_
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
      (Watched_lit.size())

  (* TODO: find the proper code for "kill line" *)
  let flush_progress (): unit =
    Printf.printf "\r%-80d\r%!" 0

  (* the "theory" part: propagations *)
  module M_th :
    Msat.Theory_intf.S
    with type formula = M_expr.t
     and type proof = M_expr.proof
  = struct
    type formula = M_expr.t
    type proof = M_expr.proof

    type level = Backtrack.level

    let dummy = Backtrack.dummy_level

    (* increment and return level *)
    let current_level () =
      Backtrack.push_level ();
      Backtrack.cur_level ()

    let backtrack = Backtrack.backtrack

    exception Conflict of Clause.t

    (* push clauses from {!lemma_queue} into the slice *)
    let flush_new_clauses_into_slice slice =
      if Queue.is_empty Clause.conflicts then
        while not (Queue.is_empty Clause.lemma_queue) do
          let c = Queue.pop Clause.lemma_queue in
          Log.debugf 5 (fun k->k "(@[<2>push_lemma@ %a@])" Clause.pp c);
          let lits = Clause.lits c in
          slice.TI.push lits ();
        done
      else (
        let c = Queue.pop Clause.conflicts in
        Queue.clear Clause.conflicts;
        raise (Conflict c)
      )

    (* assert [c := new_t], or conflict *)
    let assert_choice (c:cst)(new_t:term) : unit =
      let _, _, info, _ = Typed_cst.as_undefined_exn c in
      begin match info.cst_cur_case with
        | None ->
          let e = Explanation.return (Lit.cst_choice c new_t) in
          Backtrack.push_set_cst_case_ info;
          info.cst_cur_case <- Some (e, new_t);
          (* TODO: only update if the current NF is blocked by [uty] *)
          Poly_set.iter Watched_lit.update_watches_of_term info.cst_watched
        | Some (_,new_t') ->
          Log.debugf 1
            (fun k->k "(@[<hv1>assert_choice %a@ :to %a@ :cur %a@])"
                Typed_cst.pp c Term.pp new_t Term.pp new_t');
          assert (Term.equal new_t new_t');
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
          (* TODO: only update if the current NF is blocked by [c] *)
          Poly_set.iter Watched_lit.update_watches_of_term uty.uty_watched
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
      let e, lit' = Reduce.compute_nf_lit lit in
      begin match Lit.view lit' with
        | Lit_fresh _ -> ()
        | Lit_atom {term_cell=True; _} -> ()
        | Lit_atom {term_cell=False; _} ->
          (* conflict! *)
          let c = Lit.neg lit :: clause_guard_of_exp_ e |> Clause.make in
          Clause.push_conflict c
        | Lit_atom _ -> ()
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
      try
        (* first, empty the tautology queue *)
        flush_new_clauses_into_slice slice;
        for i = start to start + slice.TI.length - 1 do
          let lit = slice.TI.get i in
          assume_lit lit;
        done;
        flush_new_clauses_into_slice slice;
        TI.Sat
      with Conflict conflict_clause ->
        Log.debugf 3
          (fun k->k "(@[<1>raise_inconsistent@ %a@])"
              Clause.pp conflict_clause);
        TI.Unsat (Clause.lits conflict_clause, ())

    (* TODO: move checking code from Main_loop here? *)
    let if_sat _slice = ()
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
      |> Sequence.iter Watched_lit.watch_term;
    incr stat_num_clause_push;
    M.assume [Clause.lits c]

  (** {2 Toplevel Goals}

      List of toplevel goals to satisfy
  *)

  module Top_goals: sig
    val push : term -> unit
    val to_seq : term Sequence.t
    val check: unit -> unit
  end = struct
    (* list of terms to fully evaluate *)
    let toplevel_goals_ : term list ref = ref []

    (* add [t] to the set of terms that must be evaluated *)
    let push (t:term): unit =
      toplevel_goals_ := t :: !toplevel_goals_;
      ()

    let to_seq k = List.iter k !toplevel_goals_

    (* check that this term fully evaluates to [true] *)
    let is_true_ (t:term): bool =
      let _, t' = Reduce.compute_nf t in
      assert (Term.equal t' (Reduce.get_nf t |> snd));
      match t'.term_cell with
        | True -> true
        | _ -> false

    let check () =
      if not (List.for_all is_true_ !toplevel_goals_)
      then (
        if Config.progress then flush_progress();
        Log.debugf 1
          (fun k->
             let pp_lit out l =
               let e, nf = Reduce.get_nf l in
               Format.fprintf out
                 "(@[<hv1>%a@ nf: %a@ exp: %a@ deps: (@[<hv>%a@])@])"
                 Term.pp l Term .pp nf Explanation.pp e
                 (Utils.pp_list pp_dep) nf.term_deps
             in
             k "(@[<hv1>status_watched_lit@ (@[<v>%a@])@])"
               (Utils.pp_list pp_lit) !toplevel_goals_);
        assert false;
      )
  end

  (** {2 Conversion} *)

  (* list of constants we are interested in *)
  let model_support_ : Typed_cst.t list ref = ref []

  let model_env_ : Ast.env ref = ref Ast.env_empty

  (* list of (uninterpreted) types we are interested in *)
  let model_utys : Ty.t list ref = ref []

  let add_cst_support_ (c:cst): unit =
    CCList.Ref.push model_support_ c

  let add_ty_support_ (ty:Ty.t): unit =
    CCList.Ref.push model_utys ty

  module Conv = struct
    (* for converting Ast.Ty into Ty *)
    let ty_tbl_ : Ty.t lazy_t ID.Tbl.t = ID.Tbl.create 16

    (* for converting constants *)
    let decl_ty_ : cst lazy_t ID.Tbl.t = ID.Tbl.create 16

    (* environment for variables *)
    type conv_env = (Ast.var * term option) list

    let rec conv_ty (ty:Ast.Ty.t): Ty.t = match ty with
      | Ast.Ty.Prop -> Ty.prop
      | Ast.Ty.Const id ->
        begin try ID.Tbl.find ty_tbl_ id |> Lazy.force
          with Not_found -> errorf "type %a not in ty_tbl" ID.pp id
        end
      | Ast.Ty.Arrow (a,b) -> Ty.arrow (conv_ty a) (conv_ty b)

    let rec conv_term
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
        let f = conv_term env f in
        let l = List.map (conv_term env) l in
        Term.app f l
      | Ast.Var v ->
        begin match
            CCList.find_idx (fun (v',_) -> Ast.Var.equal v v') env
          with
            | None -> errorf "could not find var `%a`" Ast.Var.pp v
            | Some (i,(_, None)) ->
              let ty = Ast.Var.ty v |> conv_ty in
              Term.db (DB.make i ty)
            | Some (_,(_,Some t)) -> t
        end
      | Ast.Fun (v,body) ->
        let body = conv_term ((v,None)::env) body in
        let ty = Ast.Var.ty v |> conv_ty in
        Term.fun_ ty body
      | Ast.Forall (v,body) ->
        let body = conv_term ((v,None)::env) body in
        let uty =
          let ty = Ast.Var.ty v |> conv_ty in
          match Ty.view ty with
            | Atomic (_, Uninterpreted uty) -> uty
            | _ -> errorf "forall: need to quantify on an uninterpreted type, not %a" Ty.pp ty
        in
        Term.forall uty body
      | Ast.Exists (v,body) ->
        let body = conv_term ((v,None)::env) body in
        let uty =
          let ty = Ast.Var.ty v |> conv_ty in
          match Ty.view ty with
            | Atomic (_, Uninterpreted uty) -> uty
            | _ -> errorf "exists: need to quantify on an uninterpreted type, not %a" Ty.pp ty
        in
        Term.exists uty body
      | Ast.Mu (v,body) ->
        let body = conv_term ((v,None)::env) body in
        Term.mu body
      | Ast.Match (u,m) ->
        let u = conv_term env u in
        let m =
          ID.Map.map
            (fun (vars,rhs) ->
               let env', tys =
                 CCList.fold_map
                   (fun env v -> (v,None)::env, Ast.Var.ty v |> conv_ty)
                   env vars
               in
               tys, conv_term env' rhs)
            m
        in
        Term.match_ u m
      | Ast.Switch _ ->
        errorf "cannot convert switch %a" Ast.pp_term t
      | Ast.Let (v,t,u) ->
        (* substitute on the fly *)
        let t = conv_term env t in
        conv_term ((v, Some t)::env) u
      | Ast.If (a,b,c) ->
        Term.if_ (conv_term env a)(conv_term env b) (conv_term env c)
      | Ast.Not t -> Term.not_ (conv_term env t)
      | Ast.Binop (op,a,b) ->
        let a = conv_term env a in
        let b = conv_term env b in
        begin match op with
          | Ast.And -> Term.and_ a b
          | Ast.Or -> Term.or_ a b
          | Ast.Imply -> Term.imply a b
          | Ast.Eq -> Term.eq a b
        end

    let add_statement st =
      Log.debugf 2
        (fun k->k "(@[add_statement@ @[%a@]@])" Ast.pp_statement st);
      model_env_ := Ast.env_add_statement !model_env_ st;
      match st with
        | Ast.Assert t ->
          let t = conv_term [] t in
          Top_goals.push t;
          push_clause (Clause.make [Lit.atom t])
        | Ast.Goal (vars, t) ->
          (* skolemize *)
          let env, consts =
            CCList.fold_map
              (fun env v ->
                 let ty = Ast.Var.ty v |> conv_ty in
                 let c = Typed_cst.make_undef (Ast.Var.id v) ty in
                 (v,Some (Term.const c)) :: env, c)
              []
              vars
          in
          (* model should contain values of [consts] *)
          List.iter add_cst_support_ consts;
          let t = conv_term env t in
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
              uty_watched=Poly_set.create 16 ~eq:term_equal_;
            } in
            Ty.atomic id (Uninterpreted ty0)
          ) in
          (* model should contain domain of [ty] *)
          add_ty_support_ (Lazy.force ty);
          ID.Tbl.add ty_tbl_ id ty
        | Ast.Decl (id, ty) ->
          assert (not (ID.Tbl.mem decl_ty_ id));
          let ty = conv_ty ty in
          let cst = Typed_cst.make_undef id ty in
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
                          Typed_cst.make_cstor id_c ty_c
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
               let rhs = lazy (conv_term [] rhs) in
               let ty_args, ty_ret = Ty.unfold ty in
               let memo_arity = List.length ty_args in
               let cst =
                 (* FIXME: also require that:
                    - closed function (no metas inside)
                    - does not depend on Cst_not_memoizable IDs
                    - some CLI "memoization" flag is true
                 *)
                 if memo_arity > 0 && Ty.is_prop ty_ret then (
                   (* create root memoization tree *)
                   let memo_dtree = {
                     mc_dt_cell=Memo_fail;
                     mc_dt_offset=memo_arity;
                     mc_dt_term=lazy (
                       let _, body = Term.unfold_fun (Lazy.force rhs) in
                       let regs =
                         List.mapi (fun i ty -> Term.reg (i,ty)) ty_args
                       in
                       Term.eval_db
                         (DB_env.push_l regs DB_env.empty)
                         body
                       |> Reduce.compute_nf |> snd
                     );
                   } in
                   let rec memo_tbl = lazy {
                     memo_fun=id;
                     memo_cst=cst;
                     memo_ty=ty;
                     memo_arity;
                     memo_dtree;
                   }
                   and cst = lazy (
                     let memo = Cst_memoizable (Lazy.force memo_tbl) in
                     Typed_cst.make_defined id ty rhs memo
                   ) in
                   cst
                 ) else (* not a function, memoizing makes no sense *)
                   lazy (Typed_cst.make_defined id ty rhs Cst_trivial)
               in
               ID.Tbl.add decl_ty_ id cst
            )
            l;
          (* force thunks *)
          List.iter
            (fun (id,_,_) ->
               let c = ID.Tbl.find decl_ty_ id |> Lazy.force in
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
        | Reg _ -> assert false (* not in concrete values *)
        | DB d ->
          begin match DB_env.get d env with
            | Some t' -> t'
            | None -> errorf "cannot find DB %a in env" Term.pp t
          end
        | Const cst -> A.const cst.cst_id (ty_to_ast t.term_ty)
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
            | B_and (a,b,_,_) -> A.and_ (aux env a) (aux env b)
            | B_or (a,b) -> A.or_ (aux env a) (aux env b)
            | B_eq (a,b) -> A.eq (aux env a) (aux env b)
            | B_imply (a,b) -> A.imply (aux env a) (aux env b)
          end
        | Memo_call _ ->
          (* we could convert [f top_args], but this should never happen *)
          errorf "cannot convert memo_call to Ast"
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
        | Reg _ -> assert false
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
          let m =
            { m with
                switch_tbl;
                switch_id=new_switch_id_();
            } in
          Term.switch (aux u) m
        | Quant (q,uty,body) -> Term.quant q uty (aux body)
        | Fun (ty,body) -> Term.fun_ ty (aux body)
        | Mu body -> Term.mu (aux body)
        | Builtin b -> Term.builtin (Term.map_builtin aux b)
        | Memo_call _ ->
          assert false (* not a proper value *)
    in
    aux t

  let rec find_domain_ (uty:ty_uninterpreted_slice): cst list =
    match uty.uty_status, uty.uty_pair with
      | None, _
      | _, Lazy_none -> assert false
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
        (fun (ty,dom) -> Conv.ty_to_ast ty, List.map Typed_cst.id dom)
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
    Format.fprintf out
      "(@[<hv1>stats@ \
       :num_expanded %d@ \
       :num_uty_expanded %d@ \
       :num_clause_push %d@ \
       :num_clause_tautology %d@ \
       :num_lits %d\
       :num_propagations %d@ \
       @])"
      !stat_num_cst_expanded
      !stat_num_uty_expanded
      !stat_num_clause_push
      !stat_num_clause_tautology
      (Watched_lit.size())
      !stat_num_propagations

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
      | M.Proof.Lemma () -> Format.fprintf out "(@[<1>lemma@ ()@])"
      | M.Proof.Resolution (p1, p2, _) ->
        Format.fprintf out "(@[<1>resolution@ %a@ %a@])"
          pp_step_res p1 pp_step_res p2
      | _ -> CCFormat.string out "<other>"
    in
    Format.fprintf out "(@[<v>";
    M.Proof.fold
      (fun () {M.Proof.conclusion; step } ->
         let conclusion = clause_of_mclause conclusion in
         Format.fprintf out "(@[<hv1>step@ %a@ @[<1>from:@ %a@]@])@,"
           Clause.pp conclusion pp_step step)
      () p;
    Format.fprintf out "@])";
    ()

  type proof_status =
    | PS_depth_limited of Lit.t
    | PS_complete
    | PS_incomplete

  let pp_proof_status out = function
    | PS_depth_limited lit ->
      Format.fprintf out "(@[depth_limited@ by: %a@])" Lit.pp lit
    | PS_complete -> CCFormat.string out "complete"
    | PS_incomplete -> CCFormat.string out "incomplete"

  (* check dependencies of the unsat-core:
     - if it depends on depth-limit, not UNSAT
     - if some constant has been refined incompletely, UNKNOWN
     - otherwise, truly UNSAT
  *)
  let proof_status depth_lit core: proof_status =
    let s = ref PS_complete in
    try
      clauses_of_unsat_core core
      |> Sequence.flat_map Clause.to_seq
      |> Sequence.iter
        (fun lit ->
           if Lit.equal depth_lit (Lit.abs lit)
           then (
             s := PS_depth_limited depth_lit;
             raise Exit
           ) else match Lit.view lit with
             | Lit_assign (c,_) ->
               begin match c.cst_kind with
                 | Cst_undef (_, i, _) when not i.cst_complete ->
                   s := PS_incomplete
                 | _ -> ()
               end
             | _ -> ()
        );
      !s
    with Exit ->
      !s

  let solve ?(on_exit=[]) ?(check=true) () =
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
            let core = p |> M.unsat_core in
            assert (Lit.equal (Lit.abs cur_lit) cur_lit);
            let status = proof_status cur_lit core in
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

