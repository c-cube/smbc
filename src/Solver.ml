(* This file is free software. See file "license" for more details. *)

let get_time : unit -> float =
  let start = Unix.gettimeofday() in
  fun () ->
    Unix.gettimeofday() -. start

module SI = Msat.Solver_intf

(** {1 Solver} *)

module type CONFIG = sig
  val max_depth: int

  val deepening_step : int option
  (** Increment between two successive max depths in iterative deepening *)

  val uniform_depth : bool
  (** Depth increases uniformly *)

  val quant_unfold_depth : int
  (** Initial depth for quantifier unfolding *)

  val eval_under_quant : bool
  (** Evaluate under quantifiers to see if the body is a value *)

  val progress: bool
  (** progress display progress bar *)

  val pp_hashcons: bool

  val dimacs_file : string option
  (** File for dumping the SAT problem *)

  val check_proof : bool
  (** Check proofs given by MSat? *)
end

(** {2 The Main Solver} *)

module Make(Config : CONFIG)(Dummy : sig end) = struct
  exception Error of string

  let () = Printexc.register_printer
      (function
        | Error msg -> Some ("internal error: " ^ msg)
        | _ -> None)

  let errorf msg = CCFormat.ksprintf msg ~f:(fun s -> raise (Error s))

  let stat_num_cst_expanded = ref 0
  let stat_num_uty_expanded = ref 0
  let stat_num_clause_push = ref 0
  let stat_num_clause_tautology = ref 0
  let stat_num_propagations = ref 0
  let stat_num_undefined = ref 0
  let stat_num_unif = ref 0

  (* did we perform at least one expansion on an unknown that is
     of a type that cannot support exhaustive expansion (e.g. functions)?
     If true, it means that "unsat" might be wrong, so we'll answer "unknown" *)
  let incomplete_expansion : bool ref = ref false

  (* for objects that are expanded on demand only *)
  type 'a lazily_expanded =
    | Lazy_some of 'a
    | Lazy_none

  type undefined_cause =
    | Undef_absolute (* only undefined functions such as projectors or tailcall *)
    | Undef_quant of int (* caused by bound on quantifier unrolling *)

  (* if not [None], it means that at least once in the current call
     to [solve()], a goal was reduced to [Undefined_value], meaning we lost
     precision.
     This means that we are not refutationnally complete, or that we
     have to increase unrolling depth of quantifiers. *)
  let has_met_undefined : undefined_cause option ref = ref None

  (* did we lose at least one model because some goal evaluated
     to [undefined] with an absolute cause (i.e. not because of
     quantification approximation) *)
  let has_lost_models : bool ref = ref false

  (* current level of depth unrolling *)
  let quant_unroll_depth : int option ref = ref None

  (* option with a special case for "Undefined_value" *)
  type 'a option_or_fail =
    | OF_some of 'a
    | OF_none
    | OF_undefined_value of undefined_cause

  (* main term cell *)
  type term = {
    mutable term_id: int; (* unique ID *)
    mutable term_ty: ty_h;
    mutable term_being_evaled: bool; (* true if currently being evaluated *)
    term_cell: term_cell;
    mutable term_nf: term_nf;
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
    | Const of cst
    | App of term * term list
    | Fun of ty_h * term
    | Mu of term
    | If of term * term * term
    | Select of select * term
    | Match of term * (ty_h list * term) ID.Map.t * (ID.Set.t * term) option
    | Switch of term * switch_cell (* function table *)
    | Quant of quant * quant_range * term
    (* quantification on finite types or datatypes *)
    | Builtin of builtin
    | Check_assign of cst * term (* check a literal *)
    | Check_empty_uty of ty_uninterpreted_slice (* check it's empty *)
    | Undefined_value of ty_h * undefined_cause
    (* Value that is not defined. On booleans it corresponds to
       the middle case of https://en.wikipedia.org/wiki/Three-valued_logic.
       The [ty] argument is needed for typing *)

  (* pointer to a term to its (current) normal form, updated during evaluation *)
  and term_nf =
    | NF_some of term * explanation
    | NF_none

  and db = int * ty_h

  and select = {
    select_name: ID.t; (* "name" of the selector *)
    select_cstor: cst;
    select_i: int; (* select the i-th argument *)
  }

  and quant =
    | Forall
    | Exists

  (* what can block evaluation of a term *)
  and term_dep =
    | Dep_cst of cst
    (* blocked by non-refined constant *)
    | Dep_uty of ty_uninterpreted_slice
    (* blocked because this type is not expanded enough *)
    | Dep_quant_depth

  and builtin =
    | B_not of term
    | B_eq of term * term
    | B_and of term * term * term * term (* parallel and *)
    | B_or of term * term
    | B_imply of term * term

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
    | E_or of explanation * explanation (* disjunction! *)

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
    | Lit_quant_unroll of int

  and cst = {
    cst_id: ID.t;
    cst_ty: ty_h;
    cst_kind: cst_kind;
  }

  and cst_kind =
    | Cst_undef of cst_info * ty_uninterpreted_slice option
    | Cst_cstor
    | Cst_uninterpreted_dom_elt of ty_uninterpreted (* uninterpreted domain constant *)
    | Cst_defined of term lazy_t

  and cst_info = {
    cst_depth: int;
    (* refinement depth, used for iterative deepening *)
    cst_parent: cst option;
    (* if const was created as a parameter to some cases of some other constant *)
    mutable cst_exist_conds: cond_list;
    (* disjunction of possible conditions for cst to exist/be relevant *)
    mutable cst_cases: term list lazily_expanded;
    (* cover set (lazily evaluated) *)
    mutable cst_cur_case: (explanation * term) option;
    (* current choice of normal form *)
  }

  and cond_list = lit lazy_t list

  and 'a db_env = {
    db_st: 'a option list;
    db_size: int;
  }

  (* Hashconsed type *)
  and ty_h = {
    mutable ty_id: int;
    ty_cell: ty_cell;
  }

  and ty_def =
    | Uninterpreted of ty_uninterpreted (* uninterpreted type, with its domain *)
    | Data of cstor_list

  (* set of constructors *)
  and cstor_list = cst lazy_t list

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
  }

  and quant_range =
    | QR_unin of ty_uninterpreted_slice
    | QR_data of quant_data
    | QR_bool

  and quant_data = {
    q_data_ty: ty_h; (* type *)
    q_data_cstor: cstor_list; (* constructors *)
    q_data_depth: int; (* depth, for limiting *)
  }

  let pp_quant out = function
    | Forall -> CCFormat.string out "forall"
    | Exists -> CCFormat.string out "exists"

  let merge_undef_cause (a:undefined_cause)(b:undefined_cause) : undefined_cause =
    match a, b with
      | Undef_quant l1, Undef_quant l2 -> Undef_quant (max l1 l2)
      | Undef_quant l, _
      | _, Undef_quant l -> Undef_quant l
      | Undef_absolute, Undef_absolute -> Undef_absolute

  (* some toplevel term evaluated to [undefined] with cause [c] *)
  let add_top_undefined (c:undefined_cause): unit =
    begin match c with
      | Undef_absolute -> has_lost_models := true; (* precision lost *)
      | Undef_quant _ -> ()
    end;
    incr stat_num_undefined;
    has_met_undefined :=
      begin match !has_met_undefined with
        | None -> Some c
        | Some c' -> Some (merge_undef_cause c c')
      end

  module Ty = struct
    type t = ty_h

    let view t = t.ty_cell

    let equal a b = a.ty_id = b.ty_id
    let compare a b = CCInt.compare a.ty_id b.ty_id
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
          (Util.pp_list pp) args pp ret

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

  (** {2 Typed De Bruijn indices} *)
  module DB = struct
    type t = db
    let level = fst
    let ty = snd
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
  let term_cmp_ a b = CCInt.compare a.term_id b.term_id

  module Typed_cst = struct
    type t = cst

    let id t = t.cst_id
    let ty t = t.cst_ty

    let make cst_id ty cst_kind = {cst_id; cst_ty=ty; cst_kind}
    let make_cstor id ty =
      let _, ret = Ty.unfold ty in
      assert (Ty.is_data ret);
      make id ty Cst_cstor
    let make_defined id ty t = make id ty (Cst_defined t)
    let make_uty_dom_elt id ty uty = make id ty (Cst_uninterpreted_dom_elt uty)

    let depth (c:t): int = match c.cst_kind with
      | Cst_undef (i, _) -> i.cst_depth
      | _ -> assert false

    let make_undef ?parent ?(exist_if=[]) ?slice ~depth:cst_depth id ty =
      assert (CCOpt.for_all (fun p -> cst_depth > depth p) parent);
      (* undefined on an uninterpreted type always have a slice *)
      let slice = match slice, ty.ty_cell with
        | Some _ as s, _ -> s
        | None, Atomic (_, Uninterpreted uty) -> Some uty
        | None, _ -> None
      in
      let info =
        { cst_depth;
          cst_parent=parent;
          cst_exist_conds=exist_if;
          cst_cases=Lazy_none;
          cst_cur_case=None;
        }
      in
      make id ty (Cst_undef (info, slice))

    let as_undefined (c:t)
      : (t * Ty.t * cst_info * ty_uninterpreted_slice option) option =
      match c.cst_kind with
        | Cst_undef (i,slice) -> Some (c,c.cst_ty,i,slice)
        | Cst_defined _ | Cst_cstor | Cst_uninterpreted_dom_elt _ -> None

    let add_exists_if (i:cst_info) cond =
      i.cst_exist_conds <- cond :: i.cst_exist_conds

    let as_undefined_exn (c:t): t * Ty.t * cst_info * ty_uninterpreted_slice option=
      match c.cst_kind with
        | Cst_undef (i,slice) -> c,c.cst_ty,i,slice
        | Cst_defined _ | Cst_cstor | Cst_uninterpreted_dom_elt _ -> assert false

    let equal a b = ID.equal a.cst_id b.cst_id
    let compare a b = ID.compare a.cst_id b.cst_id
    let hash t = ID.hash t.cst_id
    let pp out a = ID.pp out a.cst_id
  end

  let cmp_uty a b =
    let c = Ty.compare (Lazy.force a.uty_self) (Lazy.force b.uty_self) in
    if c<>0 then c
    else CCInt.compare a.uty_offset b.uty_offset

  let equal_uty a b = cmp_uty a b = 0

  let hash_uty uty =
    Hash.combine3 104 (Ty.hash (Lazy.force uty.uty_self)) uty.uty_offset

  let cmp_lit a b =
    let c = CCBool.compare a.lit_sign b.lit_sign in
    if c<>0 then c
    else
      let int_of_cell_ = function
        | Lit_fresh _ -> 0
        | Lit_atom _ -> 1
        | Lit_assign _ -> 2
        | Lit_uty_empty _ -> 3
        | Lit_quant_unroll _ -> 4
      in
      match a.lit_view, b.lit_view with
        | Lit_fresh i1, Lit_fresh i2 -> ID.compare i1 i2
        | Lit_atom t1, Lit_atom t2 -> term_cmp_ t1 t2
        | Lit_assign (c1,t1), Lit_assign (c2,t2) ->
          CCOrd.(Typed_cst.compare c1 c2 <?> (term_cmp_, t1, t2))
        | Lit_uty_empty u1, Lit_uty_empty u2 -> cmp_uty u1 u2
        | Lit_quant_unroll l1, Lit_quant_unroll l2 -> CCInt.compare l1 l2
        | Lit_fresh _, _
        | Lit_atom _, _
        | Lit_assign _, _
        | Lit_uty_empty _, _
        | Lit_quant_unroll _, _
          -> CCInt.compare (int_of_cell_ a.lit_view) (int_of_cell_ b.lit_view)

  let hash_lit a =
    let sign = a.lit_sign in
    match a.lit_view with
      | Lit_fresh i -> Hash.combine3 1 (Hash.bool sign) (ID.hash i)
      | Lit_atom t -> Hash.combine3 2 (Hash.bool sign) (term_hash_ t)
      | Lit_assign (c,t) ->
        Hash.combine4 3 (Hash.bool sign) (Typed_cst.hash c) (term_hash_ t)
      | Lit_uty_empty uty -> Hash.combine3 4 (Hash.bool sign) (hash_uty uty)
      | Lit_quant_unroll l -> Hash.combine2 5 (Hash.int l)

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
    | Dep_quant_depth -> CCFormat.string out "(quant-depth)"

  let hash_q_range = function
    | QR_unin u -> hash_uty u
    | QR_data d -> Hash.combine2 (Hash.int d.q_data_depth) (Ty.hash d.q_data_ty)
    | QR_bool -> 30

  let equal_q_range r1 r2 = match r1, r2 with
    | QR_unin u1, QR_unin u2 -> equal_uty u1 u2
    | QR_data d1, QR_data d2 ->
      Ty.equal d1.q_data_ty d2.q_data_ty &&
      d1.q_data_depth = d2.q_data_depth
    | QR_bool, QR_bool -> true
    | QR_unin _, _
    | QR_data _, _
    | QR_bool, _
      -> false

  let pp_q_range out = function
    | QR_unin uty -> pp_uty out uty
    | QR_data q -> Format.fprintf out "%a[%d]" Ty.pp q.q_data_ty q.q_data_depth
    | QR_bool -> CCFormat.string out "bool"

  module Backtrack = struct
    type undo_op = unit -> unit
    type t = {
      ops: undo_op CCVector.vector;
      levels: int CCVector.vector;
    }

    (* the global stack *)
    let st_ : t = { ops=CCVector.create(); levels=CCVector.create() }

    let[@inline] cur_level () = CCVector.length st_.levels

    let backtrack (n:int): unit =
      let new_lvl = cur_level () - n in
      let offset = CCVector.get st_.levels new_lvl in
      while CCVector.length st_.ops > offset do
        let f = CCVector.pop_exn st_.ops in
        f ();
      done;
      CCVector.shrink st_.levels new_lvl;
      Log.debugf 2
        (fun k->k "@{<Yellow>** now at level %d (backtrack)@}" (cur_level()));
      ()

    let push_level () : unit =
      CCVector.push st_.levels (CCVector.length st_.ops);
      Log.debugf 2 (fun k->k "@{<Yellow>** now at level %d (push)@}" (cur_level()));
      ()

    let[@inline] push (f:undo_op) : unit =
      if not (CCVector.is_empty st_.levels) then (
        CCVector.push st_.ops f
      );
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
          | Const c ->
            Hash.combine2 4 (Typed_cst.hash c)
          | App (f,l) ->
            Hash.combine3 5 f.term_id (Hash.list sub_hash l)
          | Fun (ty, f) -> Hash.combine3 6 (Ty.hash ty) f.term_id
          | If (a,b,c) -> Hash.combine4 7 a.term_id b.term_id c.term_id
          | Match (u,m,default) ->
            let hash_case (tys,rhs) =
              Hash.combine2 (Hash.list Ty.hash tys) rhs.term_id
            and hash_default =
              function None -> 1 | Some (_,rhs) -> sub_hash rhs
            in
            let hash_m =
              Hash.seq (Hash.pair ID.hash hash_case) (ID.Map.to_seq m)
            in
            Hash.combine4 8 u.term_id hash_m (hash_default default)
          | Builtin (B_not a) -> Hash.combine2 20 a.term_id
          | Builtin (B_and (t1,t2,t3,t4)) ->
            Hash.list sub_hash [t1;t2;t3;t4]
          | Builtin (B_or (t1,t2)) -> Hash.combine3 22 t1.term_id t2.term_id
          | Builtin (B_imply (t1,t2)) -> Hash.combine3 23 t1.term_id t2.term_id
          | Builtin (B_eq (t1,t2)) -> Hash.combine3 24 t1.term_id t2.term_id
          | Mu sub -> Hash.combine sub_hash 30 sub
          | Switch (t, tbl) ->
            Hash.combine3 31 (sub_hash t) tbl.switch_id
          | Quant (q,range,bod) ->
            Hash.combine4 32 (Hash.poly q) (hash_q_range range) (sub_hash bod)
          | Check_assign (c,t) ->
            Hash.combine3 33 (Typed_cst.hash c) (sub_hash t)
          | Check_empty_uty uty ->
            Hash.combine2 34 (hash_uty uty)
          | Select (sel,t) ->
            Hash.combine4 35 (Typed_cst.hash sel.select_cstor)
              sel.select_i (sub_hash t)
          | Undefined_value (ty,_) -> Hash.combine2 36 (Ty.hash ty)

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
          | Match (u1, m1, d1), Match (u2, m2, d2) ->
            u1 == u2 &&
            ID.Map.for_all
              (fun k1 (_,rhs1) ->
                 try rhs1 == snd (ID.Map.find k1 m2)
                 with Not_found -> false)
              m1
            &&
            ID.Map.for_all (fun k2 _ -> ID.Map.mem k2 m1) m2
            &&
            CCOpt.equal (fun (_,t1)(_,t2) -> t1==t2) d1 d2
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
          | Select (s1,t1), Select(s2,t2) ->
            t1==t2 &&
            Typed_cst.equal s1.select_cstor s2.select_cstor &&
            s1.select_i = s2.select_i
          | Mu t1, Mu t2 -> t1==t2
          | Quant (q1,r1,bod1), Quant (q2,r2,bod2) ->
            q1=q2 && equal_q_range r1 r2 && bod1==bod2
          | Check_assign (c1,t1), Check_assign (c2,t2) ->
            Typed_cst.equal c1 c2 && term_equal_ t1 t2
          | Check_empty_uty u1, Check_empty_uty u2 ->
            equal_uty u1 u2
          | Undefined_value (ty1,c1), Undefined_value (ty2,c2) ->
            Ty.equal ty1 ty2 && c1=c2
          | True, _
          | False, _
          | DB _, _
          | Const _, _
          | App _, _
          | Fun _, _
          | If _, _
          | Match _, _
          | Builtin _, _
          | Select _, _
          | Mu _, _
          | Switch _, _
          | Quant _, _
          | Check_assign _, _
          | Check_empty_uty _, _
          | Undefined_value _, _
            -> false

        let set_id t i = t.term_id <- i
      end)

    let mk_bool_ (b:bool) : term =
      let t = {
        term_id= -1;
        term_being_evaled = false;
        term_ty=Ty.prop;
        term_cell=if b then True else False;
        term_nf=NF_none;
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
      | Term_dep_quant_depth

    type delayed_ty =
      | DTy_direct of ty_h
      | DTy_lazy of (unit -> ty_h)

    let cmp_term_dep_ a b =
      let to_int_ = function
        | Dep_cst _ -> 0
        | Dep_uty _ -> 1
        | Dep_quant_depth -> 2
      in
      match a, b with
        | Dep_cst c1, Dep_cst c2 -> Typed_cst.compare c1 c2
        | Dep_uty u1, Dep_uty u2 ->
          let (<?>) = CCOrd.(<?>) in
          Ty.compare (Lazy.force u1.uty_self) (Lazy.force u2.uty_self)
          <?> (CCInt.compare, u1.uty_offset, u2.uty_offset)
        | Dep_quant_depth, Dep_quant_depth -> 0
        | Dep_cst _, _
        | Dep_uty _, _
        | Dep_quant_depth, _
          -> CCInt.compare (to_int_ a) (to_int_ b)

    (* build a term. If it's new, add it to the watchlist
       of every member of [watching] *)
    let mk_term_ ~(deps:deps) cell ~(ty:delayed_ty) : term =
      let t = {
        term_id= -1;
        term_ty=Ty.prop; (* will be changed *)
        term_being_evaled=false;
        term_cell=cell;
        term_nf=NF_none;
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
          | Term_dep_quant_depth -> [Dep_quant_depth]
        in
        t'.term_deps <- deps
      );
      t'

    let db d =
      mk_term_ ~deps:Term_dep_none (DB d) ~ty:(DTy_direct (DB.ty d))

    let const c =
      let deps = match c.cst_kind with
        | Cst_undef _ -> Term_dep_cst c (* depends on evaluation! *)
        | Cst_defined _ | Cst_cstor | Cst_uninterpreted_dom_elt _ -> Term_dep_none
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

    let mu t =
      mk_term_ ~deps:Term_dep_none (Mu t) ~ty:(DTy_direct t.term_ty)

    (* TODO: check types *)

    let match_ u m ~default =
      (* propagate only from [u] *)
      let t =
        mk_term_ ~deps:(Term_dep_sub u) (Match (u,m,default))
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

    let select (sel:select) (t:term): term =
      let ty_ () =
        let ty_args, _ = Ty.unfold sel.select_cstor.cst_ty in
        assert (List.length ty_args > sel.select_i);
        List.nth ty_args sel.select_i
      in
      mk_term_ (Select (sel, t)) ~ty:(DTy_lazy ty_) ~deps:(Term_dep_sub t)

    let check_assign c t : term =
      mk_term_ (Check_assign (c, t))
        ~deps:(Term_dep_cst c) ~ty:(DTy_direct Ty.prop)

    let check_empty_uty (uty:ty_uninterpreted_slice): term =
      mk_term_ (Check_empty_uty uty)
        ~deps:(Term_dep_uty uty) ~ty:(DTy_direct Ty.prop)

    let undefined_value ty cause =
      mk_term_ (Undefined_value (ty,cause))
        ~deps:Term_dep_none ~ty:(DTy_direct ty)

    let undefined_value_prop = undefined_value Ty.prop

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
      | Undefined_value (_,c) -> undefined_value_prop c (* shortcut *)
      | Builtin (B_not t') -> t'
      | _ -> builtin_ ~deps:(Term_dep_sub t) (B_not t)

    (* might need to tranfer the negation from [t] to [sign] *)
    let abs t : t * bool = match t.term_cell with
      | False -> true_, false
      | Builtin (B_not t) -> t, false
      | _ -> t, true

    let quant q qr body =
      assert (Ty.is_prop body.term_ty);
      (* evaluation is blocked by the uninterpreted type *)
      let deps = match qr with
        | QR_unin uty -> Term_dep_uty uty
        | QR_data _ | QR_bool -> Term_dep_quant_depth
      in
      mk_term_ ~deps ~ty:(DTy_direct Ty.prop) (Quant (q,qr,body))

    let quant_uty q uty body = quant q (QR_unin uty) body

    let and_ a b =
      if a==b then a else builtin_ ~deps:(Term_dep_sub2 (a,b)) (B_and (a,b,a,b))
    let or_ a b =
      if a==b then a else builtin_ ~deps:(Term_dep_sub2 (a,b)) (B_or (a,b))
    let imply a b = builtin_ ~deps:(Term_dep_sub2 (a,b)) (B_imply (a,b))
    let eq a b =
      if a==b then true_ else builtin_ ~deps:(Term_dep_sub2 (a,b)) (B_eq (a,b))

    let and_par a b c d =
      builtin_ ~deps:(Term_dep_sub2 (c,d)) (B_and (a,b,c,d))

    (* "eager" and, evaluating [a] first *)
    let and_eager a b = if_ a b false_

    let rec and_eager_l = function
      | [] -> true_
      | [a] -> a
      | a :: tail -> and_eager a (and_eager_l tail)

    let rec and_l = function
      | [] -> true_
      | [t] -> t
      | a :: l -> and_ a (and_l l)

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

    let map_builtin f b =
      let (), b = fold_map_builtin (fun () t -> (), f t) () b in
      b

    let iter_builtin f b =
      let (), _ = fold_map_builtin (fun () t -> f t, t) () b in
      ()

    let builtin_to_seq b yield = match b with
      | B_not t -> yield t
      | B_or (a,b)
      | B_imply (a,b)
      | B_eq (a,b) -> yield a; yield b
      | B_and (a,b,c,d) -> yield a; yield b; yield c; yield d

    let equal = term_equal_
    let hash = term_hash_
    let compare a b = CCInt.compare a.term_id b.term_id

    module As_key = struct
      type t = term
      let equal = equal
      let hash = hash
    end

    module Tbl = CCHashtbl.Make(As_key)

    let to_seq_depth t (yield:t*int ->unit): unit =
      let rec aux k t =
        yield (t,k);
        match t.term_cell with
          | DB _ | Const _ | True | False -> ()
          | App (f,l) -> aux k f; List.iter (aux k) l
          | If (a,b,c) -> aux k a; aux k b; aux k c
          | Match (t, m, d) ->
            aux k t;
            ID.Map.iter (fun _ (tys,rhs) -> aux (k+List.length tys) rhs) m;
            CCOpt.iter (fun (_,t) -> aux k t) d;
          | Select (_,u)
          | Switch (u,_) -> aux k u (* ignore the table *)
          | Builtin b -> builtin_to_seq b (aux k)
          | Quant (_, _, body)
          | Mu body
          | Fun (_, body) -> aux (k+1) body
          | Undefined_value _
          | Check_assign _
          | Check_empty_uty _ -> ()
      in
      aux 0 t

    let to_seq t : t Iter.t = to_seq_depth t |> Iter.map fst

    (* return [Some] iff the term is an undefined constant *)
    let as_cst_undef (t:term):
      (cst * Ty.t * cst_info * ty_uninterpreted_slice option) option_or_fail
      =
      match t.term_cell with
        | Undefined_value (_,c) -> OF_undefined_value c
        | Const c ->
          begin match Typed_cst.as_undefined c with
            | Some res -> OF_some res
            | None -> OF_none
          end
        | _ -> OF_none

    (* return [Some (cstor,ty,args)] if the term is a constructor
       applied to some arguments *)
    let as_cstor_app (t:term): (cst * Ty.t * term list) option_or_fail =
      match t.term_cell with
        | Undefined_value (_,c) -> OF_undefined_value c
        | Const ({cst_kind=Cst_cstor; _} as c) -> OF_some (c,c.cst_ty,[])
        | App (f, l) ->
          begin match f.term_cell with
            | Const ({cst_kind=Cst_cstor; _} as c) -> OF_some (c,c.cst_ty,l)
            | _ -> OF_none
          end
        | _ -> OF_none

    let as_domain_elt (t:term): (cst * Ty.t * ty_uninterpreted_slice) option_or_fail =
      match t.term_cell with
        | Undefined_value (_,c) -> OF_undefined_value c
        | Const ({cst_kind=Cst_uninterpreted_dom_elt uty; _} as c) ->
          OF_some (c,c.cst_ty,uty)
        | _ -> OF_none

    (* typical view for unification/equality *)
    type unif_form =
      | Unif_cst of cst * Ty.t * cst_info * ty_uninterpreted_slice option
      | Unif_cstor of cst * Ty.t * term list
      | Unif_dom_elt  of cst * Ty.t * ty_uninterpreted_slice
      | Unif_undef of undefined_cause
      | Unif_none

    let as_unif (t:term): unif_form = match t.term_cell with
      | Undefined_value (_,c) -> Unif_undef c
      | Const ({cst_kind=Cst_uninterpreted_dom_elt uty; _} as c) ->
        Unif_dom_elt (c,c.cst_ty,uty)
      | Const ({cst_kind=Cst_undef (info,slice); _} as c) ->
        Unif_cst (c,c.cst_ty,info,slice)
      | Const ({cst_kind=Cst_cstor; _} as c) -> Unif_cstor (c,c.cst_ty,[])
      | App (f, l) ->
        begin match f.term_cell with
          | Const ({cst_kind=Cst_cstor; _} as c) -> Unif_cstor (c,c.cst_ty,l)
          | _ -> Unif_none
        end
      | _ -> Unif_none

    let fpf = Format.fprintf

    let pp_top ~ids out t =
      let rec pp out t =
        pp_rec out t;
        if Config.pp_hashcons then Format.fprintf out "/%d" t.term_id;
        ()
      and pp_rec out t = match t.term_cell with
        | True -> CCFormat.string out "true"
        | False -> CCFormat.string out "false"
        | DB d -> DB.pp out d
        | Const c ->
          if ids then Typed_cst.pp out c else ID.pp_name out c.cst_id
        | App (f,l) ->
          fpf out "(@[<1>%a@ %a@])" pp f (Util.pp_list pp) l
        | Fun (ty,f) ->
          fpf out "(@[fun %a@ %a@])" Ty.pp ty pp f
        | Quant (q,qr,f) ->
          fpf out "(@[%a %a@ %a@])" pp_quant q pp_q_range qr pp f
        | Mu sub -> fpf out "(@[mu@ %a@])" pp sub
        | If (a, b, c) ->
          fpf out "(@[if %a@ %a@ %a@])" pp a pp b pp c
        | Match (t,m, default) ->
          let pp_bind out (id,(_tys,rhs)) =
            fpf out "(@[<1>%a@ %a@])" ID.pp id pp rhs
          and pp_default out = function
            | None -> ()
            | Some (_,rhs) -> fpf out "@ :default %a" pp rhs
          in
          let print_map =
            CCFormat.(seq ~sep:(return "@ ")) pp_bind
          in
          fpf out "(@[match %a@ (@[<hv>%a@])%a@])"
            pp t print_map (ID.Map.to_seq m) pp_default default
        | Switch (t, m) ->
          let pp_case out (lhs,rhs) =
            fpf out "(@[<1>case@ %a@ %a@])" ID.pp lhs pp rhs
          in
          let print_map =
            CCFormat.(seq ~sep:(return "@ ")) pp_case
          in
          fpf out "(@[switch %a@ (@[<hv>%a@])@])"
            pp t print_map (ID.Tbl.to_seq m.switch_tbl)
        | Select (sel,u) ->
          fpf out "(@[select-%a-%d@ %a@])" ID.pp_name sel.select_cstor.cst_id
            sel.select_i pp u
        | Builtin (B_not t) -> fpf out "(@[<hv1>not@ %a@])" pp t
        | Builtin (B_and (_, _, a,b)) ->
          fpf out "(@[<hv1>and@ %a@ %a@])" pp a pp b
        | Builtin (B_or (a,b)) ->
          fpf out "(@[<hv1>or@ %a@ %a@])" pp a pp b
        | Builtin (B_imply (a,b)) ->
          fpf out "(@[<hv1>=>@ %a@ %a@])" pp a pp b
        | Builtin (B_eq (a,b)) ->
          fpf out "(@[<hv1>=@ %a@ %a@])" pp a pp b
        | Check_assign (c,t) ->
          fpf out "(@[<hv1>:=?@ %a@ %a@])" Typed_cst.pp c pp t
        | Check_empty_uty uty -> fpf out "(@[check_empty %a@])" pp_uty uty
        | Undefined_value (_, Undef_absolute) -> fpf out "(assert-false)"
        | Undefined_value (_, (Undef_quant l)) ->
          fpf out "(assert-false :reason-quant-unroll %d)" l
      in
      pp out t

    let pp = pp_top ~ids:true

    (* environment for evaluation: not-yet-evaluated terms *)
    type eval_env = term DB_env.t

    (* shift open De Bruijn indices by [k] *)
    let shift_db ?(depth=0) k (t:term) : term =
      if k=0 then t
      else (
        let rec aux depth t : term = match t.term_cell with
          | DB (level, ty) ->
            if level >= depth then db (DB.make (level+k) ty) else t
          | Const _ -> t
          | True
          | False -> t
          | Fun (ty, body) ->
            let body' = aux (depth+1) body in
            if body==body' then t else fun_ ty body'
          | Mu body ->
            let body' = aux (depth+1) body in
            if body==body' then t else mu body'
          | Quant (q, uty, body) ->
            let body' = aux (depth+1) body in
            if body==body' then t else quant q uty body'
          | Match (u, m, d) ->
            let u = aux depth u in
            let m =
              ID.Map.map
                (fun (tys,rhs) ->
                   tys, aux (depth + List.length tys) rhs)
                m
            in
            let d = CCOpt.map (fun (set,t) -> set, aux depth t) d in
            match_ u m ~default:d
          | Switch (u, m) ->
            let u = aux depth u in
            (* NOTE: [m] should not contain De Bruijn indices at all *)
            switch u m
          | Select (sel, u) -> select sel (aux depth u)
          | If (a,b,c) ->
            let a' = aux depth a in
            let b' = aux depth b in
            let c' = aux depth c in
            if a==a' && b==b' && c==c' then t else if_ a' b' c'
          | App (_,[]) -> assert false
          | App (f, l) ->
            let f' = aux depth f in
            let l' = aux_l depth l in
            if f==f' && CCList.equal (==) l l' then t else app f' l'
          | Builtin b -> builtin (map_builtin (aux depth) b)
          | Undefined_value _
          | Check_assign _
          | Check_empty_uty _
            -> t (* closed *)
        and aux_l d l =
          List.map (aux d) l
        in
        aux depth t
      )

    (* check well-typedness of DB indices. Call only on closed terms. *)
    let check_db t : unit =
      let fail_ u env =
        errorf "(@[check_db :in `%a`@ :sub %a@ :ty %a@ :env %a@])"
          pp t pp u Ty.pp u.term_ty
          CCFormat.(Dump.list @@ Dump.option @@ Ty.pp) env.db_st
      in
      let rec aux (env:Ty.t DB_env.t) t = match t.term_cell with
        | DB (n,nty) ->
          if n<0 || n >= DB_env.size env then fail_ t env;
          begin match DB_env.get (n,nty) env with
            | None -> fail_ t env
            | Some ty -> if not (Ty.equal ty t.term_ty) then fail_ t env
          end
        | Const _ | True | False -> ()
        | Fun (ty, body) -> aux (DB_env.push ty env) body
        | Mu body -> aux (DB_env.push t.term_ty env) body
        | Quant (_, QR_bool, body) -> aux (DB_env.push Ty.prop env) body
        | Quant (_, QR_unin u, body) ->
          aux (DB_env.push (Lazy.force u.uty_self) env) body
        | Quant (_, QR_data qr, body) -> aux (DB_env.push qr.q_data_ty env) body
        | Match (u, m, d) ->
          aux env u;
          ID.Map.iter
            (fun _ (tys,rhs) -> aux (DB_env.push_l tys env) rhs)
            m;
          CCOpt.iter (fun (_,t) -> aux env t) d;
        | Switch (u, m) ->
          aux env u;
          ID.Tbl.iter (fun _ rhs -> aux env rhs) m.switch_tbl
        | Select (_, u) -> aux env u
        | If (a,b,c) -> aux env a; aux env b; aux env c
        | App (_,[]) -> assert false
        | App (f, l) -> aux env f; List.iter (aux env) l
        | Builtin b -> iter_builtin (aux env) b
        | Undefined_value _
        | Check_assign _
        | Check_empty_uty _
          -> () (* closed *)
      in
      aux DB_env.empty t

    (* just evaluate the De Bruijn indices, and return
       the explanations used to evaluate subterms *)
    let eval_db ?shift_by:(shift=0) (env:eval_env) (t:term) : term =
      if DB_env.size env = 0 && shift=0 then t (* trivial *)
      else if DB_env.size env = 0 then shift_db shift t
      else (
        (* Format.printf "(@[<2>eval_db@ :term %a@ :env %a@])@."
           pp t CCFormat.(Dump.list @@ Dump.option @@ pp) env.db_st; *)
        let rec aux depth env t : term =
          (* Format.printf "(@[<2>eval_db_rec@ :term %a@ :depth %d :env %a@])@."
             pp t depth CCFormat.(Dump.list @@ Dump.option @@ pp) env.db_st; *)
          match t.term_cell with
            | DB d ->
              begin match DB_env.get d env with
                | None -> shift_db ~depth shift t
                | Some t' ->
                  assert (Ty.equal t.term_ty t'.term_ty);
                  shift_db depth t'
              end
            | Const _
            | True
            | False -> t
            | Fun (ty, body) ->
              let body' = aux (depth+1) (DB_env.push_none env) body in
              if body==body' then t else fun_ ty body'
            | Mu body ->
              let body' = aux (depth+1) (DB_env.push_none env) body in
              if body==body' then t else mu body'
            | Quant (q, uty, body) ->
              let body' = aux (depth+1) (DB_env.push_none env) body in
              if body==body' then t else quant q uty body'
            | Match (u, m, d) ->
              let u = aux depth env u in
              let m =
                ID.Map.map
                  (fun (tys,rhs) ->
                     tys, aux (depth+List.length tys) (DB_env.push_none_l tys env) rhs)
                  m
              and d =
                CCOpt.map (fun (set, t) -> set, aux depth env t) d
              in
              match_ u m ~default:d
            | Switch (u, m) ->
              let u = aux depth env u in
              (* NOTE: [m] should not contain De Bruijn indices at all *)
              switch u m
            | Select (sel, u) -> select sel (aux depth env u)
            | If (a,b,c) ->
              let a' = aux depth env a in
              let b' = aux depth env b in
              let c' = aux depth env c in
              if a==a' && b==b' && c==c' then t else if_ a' b' c'
            | App (_,[]) -> assert false
            | App (f, l) ->
              let f' = aux depth env f in
              let l' = aux_l depth env l in
              if f==f' && CCList.equal (==) l l' then t else app f' l'
            | Builtin b -> builtin (map_builtin (aux depth env) b)
            | Undefined_value _
            | Check_assign _
            | Check_empty_uty _
              -> t (* closed *)
        and aux_l d env l =
          List.map (aux d env) l
        in
        aux 0 env t
      )

    (* quantify on variable of given type *)
    let quant_ty ~depth q (ty_arg:Ty.t) (body:t): t = match Ty.view ty_arg with
      | Prop -> quant q QR_bool body
      | Atomic (_, Data cstors) ->
        let qr =
          QR_data {q_data_depth=depth; q_data_cstor=cstors; q_data_ty=ty_arg}
        in
        quant q qr body
      | Atomic (_, Uninterpreted uty) -> quant_uty q uty body
      | Arrow _ -> undefined_value_prop Undef_absolute (* TODO: improve on that? *)

    let quant_ty_l ~depth q ty_args body : t =
      List.fold_right (quant_ty ~depth q) ty_args body
  end

  let pp_lit out l =
    let pp_lit_view out = function
      | Lit_fresh i -> Format.fprintf out "#%a" ID.pp i
      | Lit_atom t -> Term.pp out t
      | Lit_assign (c,t) ->
        Format.fprintf out "(@[:= %a@ %a@])" Typed_cst.pp c Term.pp t
      | Lit_uty_empty u -> Format.fprintf out "(empty %a)" pp_uty u
      | Lit_quant_unroll l -> Format.fprintf out "(quant-unroll %d)" l
    in
    if l.lit_sign then pp_lit_view out l.lit_view
    else Format.fprintf out "(@[@<1>¬@ %a@])" pp_lit_view l.lit_view

  (** {2 Literals} *)
  module Lit : sig
    type t = lit
    val neg : t -> t
    val sign : t -> bool
    val view : t -> lit_view
    val as_atom : t -> (term * bool) option
    val fresh_with : ID.t -> t
    val dummy : t
    val atom : ?sign:bool -> term -> t
    val cst_choice : cst -> term -> t
    val uty_choice_empty : ty_uninterpreted_slice -> t
    val uty_choice_nonempty : ty_uninterpreted_slice -> t
    val quant_unroll : ?sign:bool -> int -> t
    val hash : t -> int
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val print : t CCFormat.printer
    val pp : t CCFormat.printer
    val norm : t -> t * SI.negated
    module Set : CCSet.S with type elt = t
  end = struct
    type t = lit

    let neg l = {l with lit_sign=not l.lit_sign}

    let sign t = t.lit_sign
    let view (t:t): lit_view = t.lit_view

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

    let cst_choice c t = make ~sign:true (Lit_assign (c, t))
    let uty_choice_empty uty = make ~sign:true (Lit_uty_empty uty)
    let uty_choice_nonempty uty : t = make ~sign:false (Lit_uty_empty uty)

    let quant_unroll ?(sign=true) d : t = make ~sign (Lit_quant_unroll d)

    let as_atom (lit:t) : (term * bool) option = match lit.lit_view with
      | Lit_atom t -> Some (t, lit.lit_sign)
      | _ -> None

    let hash = hash_lit
    let compare = cmp_lit
    let equal a b = compare a b = 0
    let pp = pp_lit
    let print = pp

    let norm l =
      if l.lit_sign then l, SI.Same_sign else neg l, SI.Negated

    module Set = CCSet.Make(struct type t = lit let compare=compare end)
  end

  module Explanation = struct
    type t = explanation
    let empty : t = E_empty
    let return e = E_leaf e
    let or_ a b = match a, b with
      | E_empty, _ -> b
      | _, E_empty -> a
      | _ -> E_or (a,b)
    let append s1 s2 = match s1, s2 with
      | E_empty, _ -> s2
      | _, E_empty -> s1
      | _ -> E_append (s1, s2)

    let to_lists e: lit list Iter.t =
      let open Iter.Infix in
      let rec aux acc = function
        | E_empty -> Iter.return acc
        | E_leaf x -> Iter.return (x::acc)
        | E_append (a,b) ->
          aux acc a >>= fun acc ->
          aux acc b
        | E_or (a,b) ->
          Iter.append (aux acc a)(aux acc b)
      in
      aux [] e

    let to_lists_uniq e =
      let f l = Lit.Set.of_list l |> Lit.Set.to_list in
      to_lists e |> Iter.map f

    let to_lists_uniq_l e =
      to_lists_uniq e |> Iter.to_rev_list

    let pp out e =
      let pp1 out l =
        Format.fprintf out "(@[%a@])"
          (Util.pp_list Lit.pp) l
      in
      match to_lists_uniq_l e with
        | [] -> assert false
        | [e] -> pp1 out e
        | l ->
          Format.fprintf out "(@[<hv2>or@ %a@])"
            (Util.pp_list pp1) l
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
    val to_seq : t -> Lit.t Iter.t
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
          (Util.pp_list Lit.pp) c.lits c.id

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

    let to_seq c = Iter.of_list c.lits
  end

  (** {2 Iterative Deepening} *)

  module Iterative_deepening : sig
    type t = private int

    type state =
      | At of t * Lit.t
      | Exhausted

    val reset : unit -> unit
    val current : unit -> state
    val current_depth : unit -> t
    val next : unit -> state
    val lit_of_depth : int -> Lit.t option
    val lit_max_smaller_than : int -> int * Lit.t
    (** maximal literal strictly smaller than the given depth *)

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
    let rec lit_of_depth d : Lit.t option =
      if d < step_ || (d mod step_ <> 0)
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
          prev_depth, Lit.atom Term.true_

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

  module Expand : sig
    val expand_cst : cst -> unit
    val expand_uty : ty_uninterpreted_slice -> unit
  end = struct
    (* make a fresh constant, with a unique name *)
    let new_cst_ =
      let n = ref 0 in
      fun ?slice ?exist_if ~parent ~depth name ty ->
        let id = ID.makef "?%s_%d" name !n in
        incr n;
        Typed_cst.make_undef ?slice ?exist_if ~parent ~depth id ty

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
          let c_head = Typed_cst.make_uty_dom_elt c_id ty uty in
          (* create the next slice *)
          let uty_tail = {
            uty_self=uty.uty_self;
            uty_parent=Some uty;
            uty_pair=Lazy_none;
            uty_offset=n+1;
            uty_status=None;
          } in
          Log.debugf 5
            (fun k->k "(@[expand-slice %a@ :into (@[%a,@ %a@])@])"
                pp_uty uty Typed_cst.pp c_head pp_uty uty_tail);
          (* memoize *)
          uty.uty_pair <- Lazy_some (c_head, uty_tail);
          (* emit clauses *)
          let clauses = clauses_of_uty uty in
          c_head, uty_tail, clauses
        | Lazy_some (hd,tl) ->
          hd, tl, [] (* already expanded *)

    let depth_of_term (t:term): int option =
      Term.to_seq t
      |> Iter.filter_map
        (fun sub -> match sub.term_cell with
           | Const {cst_kind=Cst_undef (info,_); _} -> Some info.cst_depth
           | Switch (_,{switch_cst={cst_kind=Cst_undef (info,_); _}; _}) ->
             (* in this case, the map will contain metas of depth
                [info.cst_depth+1], even though they might not
                exist already *)
             Some (info.cst_depth + 1)
           | _ -> None)
      |> Iter.max ~lt:(fun a b ->a<b)

    (* build clause(s) that explains that [c] must be one of its
       cases *)
    let clauses_of_cases (c:cst) (l:term list): Clause.t list =
      let info = match Typed_cst.as_undefined c with
        | None -> assert false
        | Some (_,_,info,_) -> info
      in
      (* disjunction of ways for [cst] to exist *)
      let guard_parent =
        List.map (fun (lazy lit) -> lit) info.cst_exist_conds
      in
      (* lits with the corresponding depth and specific guards, if any *)
      let lits =
        List.map
          (fun rhs ->
             let lit = Lit.cst_choice c rhs in
             let guard = match depth_of_term rhs with
               | None -> None
               | Some depth_rhs
                 when depth_rhs <= (Iterative_deepening.current_depth():>int) ->
                 None (* no need to guard *)
               | Some depth_rhs ->
                 let _, guard = Iterative_deepening.lit_max_smaller_than depth_rhs in
                 Some guard
             in
             lit, guard)
          l
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
          (fun (lit,guard_opt) ->
             match guard_opt with
               | Some guard ->
                 (* if [lit], then [not (depth <= max_depth_rhs-1)] *)
                 [Clause.make [ Lit.neg lit; Lit.neg guard ]]
               | _ -> [])
          lits
      in
      cs_limit @ cs_choose @ cs_once

    (* make a sub-constant with given type *)
    let mk_sub_cst ?slice ?exist_if ~parent ~depth ty_arg =
      let basename = Ty.mangle ty_arg in
      new_cst_ ?slice ?exist_if basename ty_arg ~parent ~depth

    type state = {
      cst: cst;
      info: cst_info;
      ty: Ty.t;
      memo: cst list Ty.Tbl.t;
      (* table of already built constants, by type *)
    }

    let mk_state cst ty info : state = {
      cst; info; ty;
      memo = Ty.Tbl.create 16;
    }

    (* get or create a constant that has this type *)
    let get_or_create_cst
        ~(st:state) ~(parent:cst) ~(used:cst list ref) ~depth ty_arg
      : cst * (lit lazy_t -> unit) =
      let usable =
        Ty.Tbl.get_or ~default:[] st.memo ty_arg
        |> List.filter
          (fun c' -> not (List.exists (Typed_cst.equal c') !used))
      in
      let cst = match usable with
        | [] ->
          (* make a new constant and remember it *)
          let cst = mk_sub_cst ~exist_if:[] ~parent ~depth ty_arg in
          Ty.Tbl.add_list st.memo ty_arg cst;
          used := cst :: !used; (* cannot use it in the same case *)
          cst
        | cst :: _ ->
          (* [cst] has the proper type, and is not used yet *)
          used := cst :: !used;
          cst
      in
      let _, _, info, _ = Typed_cst.as_undefined_exn cst in
      cst, (Typed_cst.add_exists_if info)

    (* expand [cst : data] where [data] has given [cstors] *)
    let expand_cases_data st cstors =
      (* datatype: refine by picking the head constructor *)
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
                    let depth =
                      if Config.uniform_depth
                      then st.info.cst_depth + 1
                      else
                        (* depth increases linearly in the number of arguments *)
                        st.info.cst_depth + List.length ty_args
                    in
                    assert (depth > st.info.cst_depth);
                    let c, add_exist_if =
                      get_or_create_cst ~st ty_arg ~parent:st.cst ~used ~depth
                    in
                    let cond = lazy (Lit.cst_choice st.cst (Lazy.force case)) in
                    add_exist_if cond; (* [cond] is sufficient for [c] to exist *)
                    Term.const c)
                 ty_args
             in
             Term.app_cst c args
           ) in
           Lazy.force case)
        cstors, []

    (* expand [cst : ty] when [ty] is an uninterpreted type *)
    let expand_cases_uninterpreted st : term list * Clause.t list =
      (* find the proper uninterpreted slice *)
      let uty = match st.cst.cst_ty, st.cst.cst_kind with
        | _, Cst_undef (_, Some u) -> u
        | {ty_cell=Atomic (_,Uninterpreted uty);_}, Cst_undef (_, _) -> uty
        | _ -> assert false
      in
      (* first, expand slice and the next slice itself *)
      let c_head, uty_tail, cs = expand_uninterpreted_slice uty in
      let _, _, cs' = expand_uninterpreted_slice uty_tail in
      (* two cases: either [c_head], or some new, deeper constant somewhere
         in the slice [uty_tail] *)
      let case1 = Term.const c_head in
      let case2 =
        let exist_if = [lazy (Lit.uty_choice_nonempty uty_tail)] in
        (* [cst = cst'], but [cst'] is deeper and belongs to the
           next slice [uty_tail].
           The case [cst = cst'] is only possible if [uty_tail] is non-empty. *)
        let depth = st.info.cst_depth+1 in
        let cst' =
          mk_sub_cst st.ty ~slice:uty_tail ~exist_if ~parent:st.cst ~depth
        in
        Term.const cst'
      in
      (* additional clause to specify that [is_empty uty_tail => cst = case1] *)
      let c_not_empty =
        [ Lit.neg (Lit.uty_choice_empty uty_tail);
          Lit.cst_choice st.cst case1;
        ]
        |> Clause.make
      in
      [case1; case2], c_not_empty :: List.rev_append cs cs'

    (* [deconstruct_ty arg ty_arg ty_ret ~fresh ~k] builds the [body:ty_ret]
       of a function [lambda arg:ty_arg. body] by "deconstructing" arg.

       - if [ty_arg = bool], [body = if arg then k [] ty_ret else k [] ty_ret]
       - if [ty_arg = datatype], [body = match arg with … | ci xi -> k xi … end]
       - if [ty_arg = a->b], we generate a decision tree based on applying
         the argument [g:a->b] to some metas [?a1, ?a2, …] and deconstructing
         [g ?a1, …] recursively.

       @param k [k ty_ret] is called to produce sub-terms of type [ty_ret],
         typically a new meta variable, in each "case" of the deconstruction.
       @param fresh [fresh ty] is called to obtain an unrelated meta-variable
       @param depth depth of meta variables that are created
    *)
    let deconstruct_ty
        (st:state)
        ~(depth:int)
        (arg:term)
        (ty_arg:Ty.t)
        (ty_ret:Ty.t)
        ~(fresh:depth:int -> Ty.t -> cst) =
      (* recursive function to deconstruct [ty_arg] and build a body
         of type [ty_ret]
         @param shift_by number of intermediate binders in the tree
      *)
      let rec aux
          ~(depth:int)
          ~(shift_by:int)
          (arg:term)
          (ty_arg:Ty.t)
          (ty_ret:Ty.t)
          ~(k:depth:int -> shift_by:int -> Ty.t -> term): term
        =
        let res = match Ty.view ty_arg with
          | Prop ->
            (* make a test on [the_param] *)
            let then_ = k ~shift_by ~depth ty_ret in
            let else_ = k ~shift_by ~depth ty_ret in
            Term.if_ arg then_ else_
          | Atomic (_, Data cstors) ->
            (* we cannot enumerate all functions on datatypes *)
            incomplete_expansion := true;
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
                   let sub_f =
                     k ~shift_by:(shift_by + n_ty_args) ~depth ty_sub_f
                   in
                   (* apply [sub_f] to the cstor's arguments *)
                   let sub_params =
                     List.mapi
                       (fun i ty_arg ->
                          let db_arg = DB.make (n_ty_args-i-1) ty_arg in
                          Term.db db_arg)
                       ty_cstor_args
                   in
                   let rhs = Term.app sub_f sub_params in
                   cstor.cst_id, (ty_cstor_args, rhs)
                )
              |> ID.Map.of_list
            in
            Term.match_ arg m ~default:None
          | Atomic (_, Uninterpreted _) ->
            (* by case. We make a flat table from values to new
               meta-variables of type [ty_ret] *)
            let switch_make_new () = k ~shift_by ~depth ty_ret in
            (* we cannot enumerate all functions on finite types *)
            incomplete_expansion := true;
            let m = {
              switch_tbl=ID.Tbl.create 16;
              switch_ty_arg=ty_arg;
              switch_ty_ret=ty_ret;
              switch_cst=st.cst;
              switch_id=new_switch_id_();
              switch_make_new;
            } in
            Term.switch arg m
          | Arrow (a,b)  ->
            (* support HO by creating [?x:a] and deconstructing [arg ?x],
               which is of the simpler type [b].
               The leaves of the deconstruction tree should have type
               [(a->b) -> c] so that we can apply [g] to several such [?x]. *)
            assert (Ty.equal arg.term_ty ty_arg);
            let x = fresh ~depth a in
            let old_shift_by = shift_by in
            let new_arg = Term.app arg [Term.const x] in (* type: b *)
            (* heavy penalty for HO synthesis *)
            let new_depth = depth + 1 + depth lsr 1 in
            (* recursive call to build the destruct tree *)
            aux ~depth:new_depth ~shift_by
              new_arg b ty_ret
              ~k:(fun ~depth ~shift_by ty' ->
                (* make a meta of type [(a -> b) -> ty'], instead of just [ty'],
                   and apply this meta to [arg] *)
                let x = k ~depth ~shift_by (Ty.arrow (Ty.arrow a b) ty') in
                assert (shift_by >= old_shift_by);
                let arg' = Term.shift_db (shift_by-old_shift_by) arg in
                Term.app x [arg'])
        in
        assert (Ty.equal ty_ret res.term_ty); (* sanity check *)
        res
      in
      aux ~depth ~shift_by:0 arg ty_arg ty_ret
        ~k:(fun ~depth ~shift_by:_ ty -> fresh ~depth ty |> Term.const)

    (* synthesize a function [fun x:ty_arg. body]
       where [body] will destruct [x] depending on its type,
       or [fun _:ty_arg. constant] *)
    let expand_cases_arrow st ty_arg ty_ret =
      let the_param = Term.db (DB.make 0 ty_arg) in
      let rec body = lazy (
        (* only one parent in any case *)
        let exist_if =
          [lazy (Lit.cst_choice st.cst (Lazy.force fun_destruct))]
        in
        let depth = st.info.cst_depth+1 in
        let fresh ~depth ty' =
          mk_sub_cst ty' ~depth ~parent:st.cst ~exist_if
        in
        deconstruct_ty st the_param ty_arg ty_ret ~depth ~fresh
      )
      and fun_destruct =
        lazy (Term.fun_ ty_arg (Lazy.force body))
      (* constant function that does not look at input *)
      and body_const = lazy (
        let exist_if = [lazy (Lit.cst_choice st.cst (Lazy.force fun_const))] in
        (* only one parent in any case *)
        let depth = st.info.cst_depth+1 in
        let c' = mk_sub_cst ty_ret ~depth ~parent:st.cst ~exist_if in
        Term.const c'
      )
      and fun_const =
        lazy (Term.fun_ ty_arg (Lazy.force body_const))
      in
      [Lazy.force fun_destruct; Lazy.force fun_const], []

    (* build the disjunction [l] of cases for [info]. Might expand other
       objects, such as uninterpreted slices. *)
    let expand_cases
        (cst:cst)
        (ty:Ty.t)
        (info:cst_info)
      : term list * Clause.t list  =
      assert (info.cst_cases = Lazy_none);
      (* expand constant depending on its type *)
      let st = mk_state cst ty info in
      let by_ty, other_clauses = match Ty.view ty with
        | Atomic (_, Data cstors) ->
          expand_cases_data st cstors
        | Atomic (_, Uninterpreted uty_root) ->
          assert (Ty.equal ty (Lazy.force uty_root.uty_self));
          expand_cases_uninterpreted st
        | Arrow (ty_arg, ty_ret) ->
          expand_cases_arrow st ty_arg ty_ret
        | Prop ->
          (* simply try true/false *)
          [Term.true_; Term.false_], []
      in
      (* build clauses *)
      let case_clauses = clauses_of_cases cst by_ty in
      by_ty, List.rev_append other_clauses case_clauses

    (* expand the given constant so that, later, it will be
       assigned a value by the SAT solver *)
    let expand_cst (c:cst): unit =
      let ty, info = match c.cst_kind with
        | Cst_undef (i,_) -> c.cst_ty,i
        | Cst_defined _ | Cst_cstor | Cst_uninterpreted_dom_elt _ ->
          assert false
      in
      let depth = info.cst_depth in
      (* check whether [c] is expanded *)
      begin match info.cst_cases with
        | Lazy_none ->
          (* [c] is blocking, not too deep, but not expanded *)
          let l, clauses = expand_cases c ty info in
          Log.debugf 2
            (fun k->k "(@[<1>expand_cst@ `@[%a:@,%a@]`@ :into (@[%a@])@ :depth %d@])"
                Typed_cst.pp c Ty.pp ty (Util.pp_list Term.pp) l depth);
          info.cst_cases <- Lazy_some l;
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
                pp_uty uty Typed_cst.pp c_head pp_uty uty_tail depth);
          uty.uty_pair <- Lazy_some (c_head, uty_tail);
          incr stat_num_uty_expanded;
          Clause.push_new_l clauses
        | Lazy_some _ -> ()
      end
  end

  (* for each explanation [e1, e2, ..., en] build the guard
         [e1 & e2 & ... & en => …], that is, the clause
         [not e1 | not e2 | ... | not en] *)
  let clause_guard_of_exp_ (e:explanation): Lit.t list Iter.t =
    let l = Explanation.to_lists e in
    Iter.map
      (fun e ->
         List.map Lit.neg e (* this is a guard! *)
         |> CCList.sort_uniq ~cmp:Lit.compare)
      l

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
              | OF_undefined_value _ | OF_none -> false
              | OF_some (_, _, l) -> List.exists aux l
          )
        end
      in
      List.exists aux l

    (* set the normal form of [t], propagate to watchers *)
    let set_nf_ t new_t (e:explanation) : unit =
      if Term.equal t new_t then ()
      else (
        let old_nf = t.term_nf in
        Backtrack.push (fun () -> t.term_nf <- old_nf);
        t.term_nf <- NF_some (new_t, e);
        Log.debugf 5
          (fun k->k
              "(@[<hv1>set_nf@ @[%a@]@ @[%a@]@ :explanation @[<hv>%a@]@])"
              Term.pp t Term.pp new_t Explanation.pp e);
      )

    let get_nf t : explanation * term =
      match t.term_nf with
        | NF_none -> Explanation.empty, t
        | NF_some (new_t,e) -> e, new_t

    (* compute the normal form of this term. We know at least one of its
       subterm(s) has been reduced *)
    let rec compute_nf (t:term) : explanation * term =
      (*Format.printf "(@[compute_nf %a@])@." Term.pp t;*)
      if t.term_being_evaled then (
        (* [t] is already being evaluated, this means there is
             an evaluation in the loop.
             We must approximate and return [Undefined_value] *)
        Explanation.empty, Term.undefined_value t.term_ty Undef_absolute
      ) else (
        (* follow the "normal form" pointer *)
        match t.term_nf with
          | NF_some (t', e) ->
            t.term_being_evaled <- true;
            let exp, nf = compute_nf_add e t' in
            (* path compression here *)
            if not (Term.equal t' nf) then (
              assert (not (Term.equal t nf));
              set_nf_ t nf exp;
            );
            t.term_being_evaled <- false;
            exp, nf
          | NF_none ->
            t.term_being_evaled <- true;
            let res = compute_nf_noncached t in
            t.term_being_evaled <- false;
            res
      )

    and compute_nf_noncached t =
      assert (t.term_nf = NF_none);
      match t.term_cell with
        | DB _ -> Explanation.empty, t
        | True | False ->
          Explanation.empty, t (* always trivial *)
        | Const c ->
          begin match c.cst_kind with
            | Cst_defined rhs ->
              (* expand defined constants *)
              compute_nf (Lazy.force rhs)
            | Cst_undef ({cst_cur_case=Some (e,new_t); _}, _) ->
              (* c := new_t, we can reduce *)
              compute_nf_add e new_t
            | Cst_undef _ | Cst_uninterpreted_dom_elt _ | Cst_cstor ->
              Explanation.empty, t
          end
        | Fun _ -> Explanation.empty, t (* no eval under lambda *)
        | Mu body ->
          (* [mu x. body] becomes [body[x := mu x. body]] *)
          let env = DB_env.singleton t in
          Explanation.empty, Term.eval_db env body
        | Quant (q,QR_bool,body) ->
          let b_true = Term.eval_db (DB_env.singleton Term.true_) body in
          let b_false = Term.eval_db (DB_env.singleton Term.false_) body in
          begin match q with
            | Forall -> compute_nf (Term.and_ b_true b_false)
            | Exists -> compute_nf (Term.or_ b_true b_false)
          end
        | Quant (Forall, _, ({term_cell=(True|False); _} as bod)) ->
          Explanation.empty, bod (* optim: [forall x. bool --> bool] *)
        | Quant (q,QR_unin uty,body) ->
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
                Term.quant_uty q uty_tail body
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
        | Quant (q,QR_data d,body) ->
          (* first, try to evaluate body (might become true/false/undefined) *)
          let e_body, body_nf = compute_nf body in
          let body_is_value = match body_nf.term_cell with
            | True | False | Undefined_value (_,Undef_absolute) -> true
            | _ -> false
          in
          (* NOTE: we can simplify [exists x. true] and [forall x. false]
             because we assume there are no empty types. *)
          if body_is_value then (
            e_body, body_nf
          ) else if CCOpt.is_none !quant_unroll_depth then (
            Explanation.empty, t (* blocked for now *)
          ) else if d.q_data_depth >= CCOpt.get_exn !quant_unroll_depth then (
            (* just give up and return undefined, because of depth *)
            let depth = CCOpt.get_exn !quant_unroll_depth in
            let e = Explanation.return (Lit.quant_unroll depth) in
            let nf = Term.undefined_value_prop (Undef_quant depth) in
            set_nf_ t nf e;
            e, nf
          ) else (
            (* turn [forall x:nat. P[x]] into
               [p 0 && forall x:nat. P[s x]] *)
            let l =
              List.map
                (fun (lazy cstor) ->
                   let args, _ = Ty.unfold (Typed_cst.ty cstor) in
                   let n = List.length args in
                   let db_l =
                     List.mapi (fun i ty -> Term.db (n-i-1,ty)) args
                   in
                   (* replace [x] with [cstor args] in [body] *)
                   let arg = Term.app_cst cstor db_l in
                   (* need to shift open variables because we
                      remove 1 quantifier and add n quantifiers *)
                   let shift_by = if n>0 then n-1 else 0 in
                   let body' =
                     Term.eval_db ~shift_by (DB_env.singleton arg) body
                   in
                   (*Format.printf
                     "(@[eval_quant@ :old %a@ :arg %a@ :shift_by %d@ :body' %a@])@."
                     Term.pp t Term.pp arg n Term.pp body';*)
                   List.fold_right
                     (fun ty body ->
                        Term.quant_ty ~depth:(d.q_data_depth+1) q ty body)
                     args body')
                d.q_data_cstor
            in
            let new_t = match q with
              | Forall -> Term.and_l l
              | Exists -> Term.or_l l
            in
            let e, nf = compute_nf new_t in
            set_nf_ t nf e;
            e, nf
          )
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
            | Undefined_value (_,c) ->
              (* [if fail _ _ ---> fail] *)
              compute_nf (Term.undefined_value t.term_ty c)
            | _ -> Explanation.empty, default()
          in
          (* merge evidence from [a]'s normal form and [b/c]'s
             normal form *)
          let e = Explanation.append e_a e_branch in
          set_nf_ t t' e;
          e, t'
        | Match (u, m, d) ->
          let e_u, u' = compute_nf u in
          let default() =
            if u==u' then t else Term.match_ u' m ~default:d
          in
          let e_branch, t' = match Term.as_cstor_app u' with
            | OF_some (c, _, l) ->
              begin match ID.Map.find (Typed_cst.id c) m with
                | tys, rhs ->
                  if List.length tys = List.length l
                  then (
                    (* evaluate arguments *)
                    let env = DB_env.push_l l DB_env.empty in
                    (* replace in [rhs] *)
                    let rhs = Term.eval_db env rhs in
                    (* evaluate new [rhs] *)
                    compute_nf rhs
                  ) else (
                    Explanation.empty, Term.match_ u' m ~default:d
                  )
                | exception Not_found ->
                  begin match d with
                    | Some (_,rhs) -> compute_nf rhs
                    | None -> assert false
                  end
              end
            | OF_undefined_value c ->
              (* [match fail with _ end ---> fail] *)
              compute_nf (Term.undefined_value t.term_ty c)
            | OF_none ->
              Explanation.empty, default()
          in
          let e = Explanation.append e_u e_branch in
          set_nf_ t t' e;
          e, t'
        | Select (sel, u) ->
          let e_u, u' = compute_nf u in
          let default() =
            if u==u' then t else Term.select sel u'
          in
          let e_branch, t' = match Term.as_cstor_app u' with
            | OF_some (c, _, l) ->
              if Typed_cst.equal c sel.select_cstor then (
                (* same cstor, take [i]-th argument and reduce *)
                assert (List.length l > sel.select_i);
                let arg = List.nth l sel.select_i in
                compute_nf arg
              ) else (
                (* not defined in this model *)
                Explanation.empty, Term.undefined_value t.term_ty Undef_absolute
              )
            | OF_undefined_value c ->
              (* [select fail _ ---> fail] *)
              Explanation.empty, Term.undefined_value t.term_ty c
            | OF_none ->
              Explanation.empty, default() (* does not reduce *)
          in
          let e = Explanation.append e_u e_branch in
          set_nf_ t t' e;
          e, t'
        | Switch (u, m) ->
          let e_u, u' = compute_nf u in
          begin match Term.as_domain_elt u' with
            | OF_some (cst,_,_) ->
              let u_id = cst.cst_id in
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
            | OF_undefined_value c ->
              (* [switch fail _ ---> fail] *)
              compute_nf (Term.undefined_value t.term_ty c)
            | OF_none ->
              (* block again *)
              let t' = if u==u' then t else Term.switch u' m in
              e_u, t'
          end
        | App ({term_cell=Const {cst_kind=Cst_cstor; _}; _}, _) ->
          Explanation.empty, t (* do not reduce under cstors *)
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
        | Check_assign (c, case) ->
          begin match c.cst_kind with
            | Cst_undef ({cst_cur_case=None;_}, _) ->
              Explanation.empty, t
            | Cst_undef (({cst_cur_case=Some (_,case');_} as info), _) ->
              assert (match info.cst_cases with
                | Lazy_some l -> List.memq case l | Lazy_none -> false);
              (* NOTE: instead of saying [c=c10 --> false] because [c:=c1],
                 or because [c:=c2], etc. we can cut more search space by
                 explaining it by [not (c=c10)]  *)
              let lit = Lit.cst_choice c case in
              if Term.equal case case'
              then Explanation.return lit, Term.true_
              else Explanation.return (Lit.neg lit), Term.false_
            | Cst_uninterpreted_dom_elt _
            | Cst_cstor | Cst_defined _ ->
              assert false
          end
        | Check_empty_uty uty ->
          begin match uty.uty_status with
            | None -> Explanation.empty, t
            | Some (e, Uty_empty) -> e, Term.true_
            | Some (e, Uty_nonempty) -> e, Term.false_
          end
        | Undefined_value _ ->
          Explanation.empty, t (* already a normal form *)

    (* apply [f] to [l], until no beta-redex is found *)
    and compute_nf_app env e f l = match f.term_cell, l with
      | Undefined_value (_,c), _ ->
        (* applying [fail] just fails *)
        let ty = (Term.app f l).term_ty in
        compute_nf (Term.undefined_value ty c)
      | Const {cst_kind=Cst_defined (lazy def_f); _}, l ->
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
        let e_f, f' = Term.eval_db env f |> compute_nf in
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
          | Undefined_value _ -> e_a, a' (* [not fail ---> fail] *)
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
          | Undefined_value (_,c1), Undefined_value (_,c2) ->
            Explanation.or_ e_a e_b, Term.undefined_value_prop (merge_undef_cause c1 c2)
          | Undefined_value (_,c), _ -> e_a, Term.undefined_value_prop c
          | _, Undefined_value (_,c) -> e_b, Term.undefined_value_prop c
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
           once their conjunction reduces to [true] or [false]. *)
        let e_a, c' = compute_nf a in
        let e_b, d' = compute_nf b in
        begin match c'.term_cell, d'.term_cell with
          | False, False ->
            (* combine explanations here, 2 conflicts at the same time *)
            Explanation.or_ e_a e_b, Term.false_
          | False, _ ->
            e_a, Term.false_
          | _, False ->
            e_b, Term.false_
          | True, True ->
            let e_ab = Explanation.append e_a e_b in
            e_ab, Term.true_
          | Undefined_value (_,c1), Undefined_value (_,c2) ->
            Explanation.or_ e_a e_b, Term.undefined_value_prop (merge_undef_cause c1 c2)
          | Undefined_value (_,c), _ -> e_a, Term.undefined_value_prop c
          | _, Undefined_value (_,c) -> e_b, Term.undefined_value_prop c
          | _ ->
            let t' =
              if c==c' && d==d' then old else Term.and_par a b c' d'
            in
            (* keep the explanations for when the value is true/false *)
            Explanation.empty, t'
        end
      | B_eq (a,b) ->
        assert (not (Ty.is_prop a.term_ty));
        let e_a, a' = compute_nf a in
        let e_b, b' = compute_nf b in
        let e_ab = Explanation.append e_a e_b in
        let default() =
          if a==a' && b==b' then old else Term.eq a' b'
        in
        (* check first for failures, then try to unify *)
        begin match Term.as_unif a', Term.as_unif b' with
          | Term.Unif_undef c1, Term.Unif_undef c2 ->
            Explanation.or_ e_a e_b, Term.undefined_value_prop (merge_undef_cause c1 c2)
          | Term.Unif_undef c, _ -> e_a, Term.undefined_value_prop c
          | _, Term.Unif_undef c -> e_b, Term.undefined_value_prop c
          | _ when Term.equal a' b' ->
            e_ab, Term.true_ (* physical equality *)
          | Term.Unif_cstor (c1,ty1,l1), Term.Unif_cstor (c2,_,l2) ->
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
          | Term.Unif_cstor (_, _, l), _ when cycle_check_l ~sub:b' l ->
            (* acyclicity rule *)
            e_ab, Term.false_
          | _, Term.Unif_cstor (_, _, l) when cycle_check_l ~sub:a' l ->
            e_ab, Term.false_
          | Term.Unif_dom_elt (c1,ty1,_), Term.Unif_dom_elt (c2,ty2,_) ->
            (* domain elements: they are all distinct *)
            assert (Ty.equal ty1 ty2);
            if Typed_cst.equal c1 c2
            then e_ab, Term.true_
            else e_ab, Term.false_
          | Term.Unif_cstor (cstor, _, args), Term.Unif_cst (c, _, info, _)
          | Term.Unif_cst (c, _, info, _), Term.Unif_cstor (cstor, _, args) ->
            (* expand right now, so we can get a list of cases *)
            Expand.expand_cst c;
            begin match info.cst_cases with
              | Lazy_none -> assert false
              | Lazy_some cases ->
                (* unification: use the literal [c := case] for
                   the [case in cases] that matches [cstor].
                   Reduce to [:= c case & case.i=args.i] *)
                let case,sub_metas =
                  CCList.find_map
                    (fun t -> match Term.as_cstor_app t with
                       | OF_some (cstor', _, sub_metas) ->
                         if Typed_cst.equal cstor cstor'
                         then Some (t,sub_metas)
                         else None
                       | OF_undefined_value _ | OF_none -> assert false)
                    cases
                  |> (function | Some x->x | None -> assert false)
                in
                assert (List.length sub_metas = List.length args);
                let check_case = Term.check_assign c case in
                let check_subs =
                  List.map2 Term.eq sub_metas args |> Term.and_l
                in
                incr stat_num_unif;
                (* eager "and", as a "if" *)
                compute_nf_add e_ab
                  (Term.if_ check_case check_subs Term.false_)
            end
          | Term.Unif_dom_elt (dom_elt,_, uty_dom_elt), Term.Unif_cst (c0, _, _, c_slice0)
          | Term.Unif_cst (c0, _, _, c_slice0), Term.Unif_dom_elt (dom_elt,_,uty_dom_elt) ->
            let dom_elt_offset = uty_dom_elt.uty_offset in
            (* we know that [uty] is expanded deep enough that [dom_elt]
               exists, so we can simply reduce [?c = dom_elt_n] into
               [¬empty(uty[0:]) & .. & ¬empty(uty[n:]) & ?c := dom_elt_n] *)
            let traverse e_c c uty =
              Expand.expand_cst c;
              Expand.expand_uty uty;
              match uty.uty_pair with
                | Lazy_none -> assert false
                | Lazy_some _ when dom_elt_offset < uty.uty_offset ->
                  (* [c] is too deep in [uty], it cannot be equal to [dom_elt]
                     [dom_elt] is not in the slice of [c]. *)
                  Explanation.empty, Term.false_
                | Lazy_some (dom_elt', uty') ->
                  Expand.expand_cst c;
                  let check_uty_not_empty = Term.check_empty_uty uty |> Term.not_ in
                  (* FIXME:
                     in the case [c := c'] we also need to check eagerly
                     that [c'] lives in a non-empty type.
                     Otherwise: assume [a != b, tau={tau0}, a := tau0],
                     we would conclude [b=b' != tau0] before checking that
                     there is a value for [b']
                     NOTE: it would be nice to be SURE that [c] has a
                       concret value, in addition to its type not
                       being empty! *)
                  if Typed_cst.equal dom_elt dom_elt'
                  then (
                    (* [c] belongs in [uty[n:]], check assignment *)
                    incr stat_num_unif;
                    Term.and_eager check_uty_not_empty
                      (Term.check_assign c (Term.const dom_elt))
                    |> compute_nf_add e_c
                  ) else (
                    (* [c] belongs in [uty[k:]] with [k<n], so to be
                       equal to [dom_elt] it must not be [uty_k] *)
                    assert (dom_elt_offset > uty.uty_offset);
                    Expand.expand_cst c;
                    begin match c.cst_kind with
                      | Cst_undef ({cst_cases=Lazy_some cases; _},Some _) ->
                        (* [c=dom_elt' OR c=c'] *)
                        let c' = match cases with
                          | [a;b] ->
                            begin match Term.as_cst_undef a, Term.as_cst_undef b with
                              | OF_some (c',_,_,_), _ | _, OF_some (c',_,_,_) -> c'
                              | _ -> assert false
                            end
                          | _ -> assert false
                        in
                        assert (c != c');
                        (* [c = dom_elt -->
                            not-empty(uty) && c=c' && not-empty(uty')],
                           with [c' in uty'] *)
                        Term.and_eager_l
                          [ check_uty_not_empty;
                            Term.not_ (Term.check_empty_uty uty');
                            Term.and_
                              (Term.check_assign c (Term.const c'))
                              (Term.eq (Term.const c') (Term.const dom_elt));
                          ]
                        |> compute_nf_add e_c
                      | _ -> assert false
                    end
                  )
            in
            let uty0 = match c_slice0 with
              | None -> assert false
              | Some c->c
            in
            traverse e_ab c0 uty0
          | _ -> e_ab, default()
        end

    let compute_nf_lit (lit:lit): explanation * lit =
      match Lit.view lit with
        | Lit_fresh _
        | Lit_assign (_,_)
        | Lit_uty_empty _
        | Lit_quant_unroll _
          -> Explanation.empty, lit
        | Lit_atom t ->
          let e, t' = compute_nf t in
          e, Lit.atom ~sign:(Lit.sign lit) t'
  end

  (** {2 A literal asserted to SAT}

      A set of terms that must be evaluated (and their value, propagated)
      in the current partial model. *)

  module Top_terms : sig
    val add : term -> unit
    val size : unit -> int
    val update_all : unit -> unit (** update all top terms *)
  end = struct

    let to_lit term = Lit.atom ~sign:true term
    let pp out term = Term.pp out term

    (* clauses for [e => l] *)
    let clause_imply (l:lit) (e:explanation): Clause.t Iter.t =
      clause_guard_of_exp_ e
      |> Iter.map
        (fun guard -> l :: guard |> Clause.make)

    let propagate_lit_ (l:term) (e:explanation): unit =
      let cs = clause_imply (to_lit l) e |> Iter.to_rev_list in
      Log.debugf 4
        (fun k->k
            "(@[<hv1>@{<green>propagate_lit@}@ %a@ nf: %a@ clauses: (@[%a@])@])"
            pp l pp (snd (Reduce.compute_nf l)) (Util.pp_list Clause.pp) cs);
      incr stat_num_propagations;
      Clause.push_new_l cs;
      ()

    let trigger_conflict (e:explanation): unit =
      let cs =
        clause_guard_of_exp_ e
        |> Iter.map Clause.make
        |> Iter.to_rev_list
      in
      Log.debugf 4
        (fun k->k
            "(@[<hv1>@{<green>conflict@}@ clauses: (@[%a@])@])"
            (Util.pp_list Clause.pp) cs);
      incr stat_num_propagations;
      Clause.push_new_l cs;
      ()

    let expand_cst_ (t:term)(c:cst) : unit =
      assert (Ty.is_prop t.term_ty);
      Log.debugf 3
        (fun k->k "(@[<1>expand_cst@ %a@ :because-of %a@])" Typed_cst.pp c Term.pp t);
      Expand.expand_cst c;
      ()

    let expand_uty_ (t:term)(uty:ty_uninterpreted_slice) : unit =
      assert (Ty.is_prop t.term_ty);
      Log.debugf 2
        (fun k->k "(@[<1>expand_uty@ %a@ %a@])" pp_uty uty Term.pp t);
      Expand.expand_uty uty;
      ()

    let expand_dep (t:term) (d:term_dep) : unit = match d with
      | Dep_cst c -> expand_cst_ t c
      | Dep_uty uty -> expand_uty_ t uty
      | Dep_quant_depth -> ()

    (* evaluate [t] in current partial model, and expand the constants
       that block it *)
    let update (t:term): unit =
      assert (Ty.is_prop t.term_ty);
      let e, new_t = Reduce.compute_nf t in
      Log.debugf 5
        (fun k->k "(@[update@ :term %a@ :nf %a@ :exp %a@])"
            Term.pp t Term.pp new_t Explanation.pp e);
      (* if [new_t = true/false], propagate literal *)
      begin match new_t.term_cell with
        | True -> propagate_lit_ t e
        | False -> propagate_lit_ (Term.not_ t) e
        | Undefined_value (_,c) ->
          (* there is no chance that this goal evaluates to a boolean anymore,
             we must try something else *)
          add_top_undefined c;
          trigger_conflict e
        | _ ->
          Log.debugf 4
            (fun k->k
                "(@[<1>update@ %a@ @[<1>:normal_form@ %a@]@ \
                 :deps (@[%a@])@ :exp @[<hv>%a@]@])"
                Term.pp t Term.pp new_t
                (Util.pp_list pp_dep) new_t.term_deps
                Explanation.pp e);
          List.iter (expand_dep t) new_t.term_deps;
      end;
      ()

    (* NOTE: we use a list because it's lightweight, fast to iterate
       on, and we only add elements in it at the beginning *)
    let top_ : term list ref = ref []

    let mem_top_ (t:term): bool =
      List.exists (Term.equal t) !top_

    let add (t:term) =
      let lit, _ = Term.abs t in
      if not (mem_top_ lit) then (
        Log.debugf 3
          (fun k->k "(@[<1>@{<green>Top_terms.add@}@ %a@])" pp lit);
        top_ := lit :: !top_;
        (* also ensure it is watched properly *)
        update lit;
      )

    let size () = List.length !top_

    (* is the dependency updated, i.e. decided by the SAT solver? *)
    let dep_updated (d:term_dep): bool = match d with
      | Dep_cst {cst_kind=Cst_undef (i, _); _} ->
        CCOpt.is_some i.cst_cur_case
      | Dep_cst _ -> assert false
      | Dep_uty uty ->
        CCOpt.is_some uty.uty_status
      | Dep_quant_depth -> CCOpt.is_some !quant_unroll_depth

    (* if [t] needs updating, then update it *)
    let update_maybe (t:term): unit =
      (* check if there are reasons to (re-)evaluate this term *)
      let _, nf = Reduce.get_nf t in
      let should_update = List.exists dep_updated nf.term_deps in
      if should_update then (
        update t;
      )

    let update_all () = List.iter update_maybe !top_
  end

  (** {2 Sat Solver} *)

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
    val push : term -> unit
    val check: unit -> unit
  end = struct
    (* list of terms to fully evaluate *)
    let toplevel_goals_ : term list ref = ref []

    (* add [t] to the set of terms that must be evaluated *)
    let push (t:term): unit =
      toplevel_goals_ := t :: !toplevel_goals_;
      ()

    (* check that this term fully evaluates to [true] *)
    let is_true_ (t:term): bool =
      let _, t' = Reduce.compute_nf t in
      match t'.term_cell with
        | True -> true
        | _ -> false

    let check () =
      if not (List.for_all is_true_ !toplevel_goals_)
      then (
        if Config.progress then flush_progress();
        Log.debugf 1
          (fun k->
             let pp_dep out = function
               | Dep_cst c ->
                 let _, nf = Reduce.get_nf (Term.const c) in
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
               | Dep_quant_depth ->
                 Format.fprintf out "(@quand-depth@ :current %a@])"
                   CCFormat.Dump.(option int) !quant_unroll_depth
             in
             let pp_lit out l =
               let e, nf = Reduce.get_nf l in
               Format.fprintf out
                 "(@[<hv1>%a@ nf: %a@ exp: %a@ deps: (@[<hv>%a@])@])"
                 Term.pp l Term .pp nf Explanation.pp e
                 (Util.pp_list pp_dep) nf.term_deps
             in
             k "(@[<hv1>status_watched_lit@ (@[<v>%a@])@])"
               (Util.pp_list pp_lit) !toplevel_goals_);
        assert false;
      )
  end

  (* the "theory" part: propagations *)
  module M_th : sig
    val set_active: bool -> unit
    include Msat.PLUGIN_CDCL_T
      with module Formula = Lit
       and type proof = unit
       and type t = unit
  end = struct
    module Formula = Lit
    type t = unit (* TODO make it less stateful *)
    type proof = unit

    (* if true, perform theory propagation; otherwise do nothing *)
    let active = ref true
    let set_active b = active := b

    let push_level = Backtrack.push_level
    let pop_levels () n = Backtrack.backtrack n

    (* push clauses from {!lemma_queue} into the slice *)
    let flush_new_clauses_into_slice slice =
      while not (Queue.is_empty Clause.lemma_queue) do
        let c = Queue.pop Clause.lemma_queue in
        Log.debugf 5 (fun k->k "(@[<2>push_lemma@ %a@])" Clause.pp c);
        let lits = Clause.lits c in
        slice.SI.acts_add_clause ~keep:true lits ();
      done

    (* assert [c := new_t] (which is, [lit]), or conflict *)
    let assert_choice ~lit (c:cst)(new_t:term) : unit =
      let _, _, info, _ = Typed_cst.as_undefined_exn c in
      begin match info.cst_cur_case with
        | None ->
          let e = Explanation.return lit in
          Backtrack.push (fun () -> info.cst_cur_case <- None);
          info.cst_cur_case <- Some (e, new_t);
        | Some (_,new_t') ->
          Log.debugf 1
            (fun k->k "(@[<hv1>assert_choice %a@ :to %a@ :cur %a@])"
                Typed_cst.pp c Term.pp new_t Term.pp new_t');
          assert (Term.equal new_t new_t');
      end

    let assert_uty
        ~lit
        (uty:ty_uninterpreted_slice)
        (status:ty_uninterpreted_status)
      : unit =
      Log.debugf 2
        (fun k->k "(@[<1>@{<green>assume_uty@}@ @[%a@] %a@])"
            pp_uty uty pp_uty_status status);
      begin match uty.uty_status with
        | None ->
          let e = Explanation.return lit in
          Backtrack.push (fun () -> uty.uty_status <- None);
          uty.uty_status <- Some (e, status);
        | Some (_, ((Uty_empty | Uty_nonempty) as s)) ->
          Log.debugf 1
            (fun k->k "(@[<hv1>assert_uty %a@ :to %a@ :cur %a@])"
                pp_uty uty pp_uty_status status pp_uty_status s);
          assert (s = status)
      end

    (* signal to the SAT solver that [lit --e--> false] *)
    let trigger_conflict (lit:lit) (e:explanation): unit =
      let cs =
        clause_guard_of_exp_ e
        |> Iter.map
          (fun guard -> Lit.neg lit :: guard |> Clause.make)
      in
      Iter.iter Clause.push_new cs

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
          (* conflict, the goal reduces to [false]! *)
          trigger_conflict lit e
        | Lit_atom {term_cell=Undefined_value (ty,c); _} ->
          (* the literal will never be a boolean, we must try
             something else *)
          assert (Ty.equal Ty.prop ty);
          add_top_undefined c;
          trigger_conflict lit e
        | Lit_quant_unroll l when Lit.sign lit ->
          (* locally assume quantifier depth *)
          assert (CCOpt.is_none !quant_unroll_depth);
          Backtrack.push (fun () -> quant_unroll_depth := None);
          quant_unroll_depth := Some l;
        | Lit_atom _ | Lit_quant_unroll _ -> ()
        | Lit_assign(c, t) ->
          if Lit.sign lit then assert_choice ~lit c t
        | Lit_uty_empty uty ->
          let status = if Lit.sign lit then Uty_empty else Uty_nonempty in
          assert_uty ~lit uty status
      end

    (* propagation from the bool solver *)
    let partial_check (_:t) acts =
      (* do the propagations in a local frame *)
      if Config.progress then print_progress();
      (* first, empty the tautology queue *)
      flush_new_clauses_into_slice acts;
      acts.SI.acts_iter_assumptions
        (function
        | SI.Lit lit -> assume_lit lit
        | SI.Assign (_, _) -> ());
      if !active then (
        Top_terms.update_all ();
      );
      flush_new_clauses_into_slice acts;
      ()

    let final_check _ _acts =
      Log.debugf 3 (fun k->k "(final-check)");
      ()
  end

  module M = Msat.Make_cdcl_t(M_th)
  let msat = M.create ~size:`Big ()

  (* push one clause into [M], in the current level (not a lemma but
     an axiom) *)
  let push_clause (c:Clause.t): unit =
    Log.debugf 2 (fun k->k "(@[<1>push_clause@ @[%a@]@])" Clause.pp c);
    (* reduce to normal form the literals, ensure they
         are added to the proper constant watchlist(s) *)
    begin
      Clause.to_seq c
      |> Iter.filter_map Lit.as_atom
      |> Iter.map fst
      |> Iter.iter Top_terms.add
    end;
    incr stat_num_clause_push;
    M.assume msat [Clause.lits c] ()

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
    type conv_env = {
      let_bound: (term * int) ID.Map.t; (* let-bound variables, to be replaced. int=depth at binding position *)
      bound: (int * Ty.t) ID.Map.t; (* set of bound variables. int=depth at binding position *)
      depth: int;
    }

    let empty_env : conv_env =
      {let_bound=ID.Map.empty; bound=ID.Map.empty; depth=0}

    let rec conv_ty (ty:Ast.Ty.t): Ty.t = match ty with
      | Ast.Ty.Prop -> Ty.prop
      | Ast.Ty.Const id ->
        begin try ID.Tbl.find ty_tbl_ id |> Lazy.force
          with Not_found -> errorf "type %a not in ty_tbl" ID.pp id
        end
      | Ast.Ty.Arrow (a,b) -> Ty.arrow (conv_ty a) (conv_ty b)

    let add_bound env v =
      let ty = Ast.Var.ty v |> conv_ty in
      { env with
          depth=env.depth+1;
          bound=ID.Map.add (Ast.Var.id v) (env.depth,ty) env.bound; }

    (* add [v := t] to bindings. Depth is not incremented
       (there will be no binders) *)
    let add_let_bound env v t =
      { env with
          let_bound=ID.Map.add (Ast.Var.id v) (t,env.depth) env.let_bound }

    let find_env env v =
      let id = Ast.Var.id v in
      ID.Map.get id env.let_bound, ID.Map.get id env.bound

    let rec conv_term_rec
        (env: conv_env)
        (t:Ast.term): term = match Ast.term_view t with
      | Ast.Bool true -> Term.true_
      | Ast.Bool false -> Term.false_
      | Ast.Unknown _ -> assert false
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
            (* replace [v] by [t'], but need to shift [t'] by the number
               of levels added between binding point
               and call point (here). *)
            assert (env.depth >= depth_t');
            let t' = Term.shift_db (env.depth - depth_t') t' in
            t'
          | None, Some (n,db_ty) ->
            (* some bound variable *)
            let ty = Ast.Var.ty v |> conv_ty in
            let level = env.depth - n - 1 in
            if not (Ty.equal ty db_ty) then (
              errorf "(@[type error :var %a@ :index %d@ type %a / %a@])"
                Ast.Var.pp v level Ty.pp ty Ty.pp db_ty
            );
            Term.db (DB.make level ty)
          | None, None ->
            errorf "(@[could not find var `%a`@])" Ast.Var.pp v
        end
      | Ast.Bind (Ast.Fun,v,body) ->
        let env' = add_bound env v in
        let body = conv_term_rec env' body in
        let ty = Ast.Var.ty v |> conv_ty in
        Term.fun_ ty body
      | Ast.Select (sel, u) ->
        let u = conv_term_rec env u in
        let sel =
          let select_cstor = match ID.Tbl.get decl_ty_ sel.Ast.select_cstor with
            | Some (lazy c) ->
              assert (c.cst_kind = Cst_cstor);
              c
            | _ -> assert false
          in
          { select_name=Lazy.force sel.Ast.select_name;
            select_cstor; select_i=sel.Ast.select_i }
        in
        Term.select sel u
      | Ast.Bind((Ast.Forall | Ast.Exists) as q,v,body) ->
        let env' = add_bound env v in
        let body = conv_term_rec env' body in
        let q = if q=Ast.Forall then Forall else Exists in
        let ty = Ast.Var.ty v |> conv_ty in
        Term.quant_ty ~depth:0 q ty body
      | Ast.Bind (Ast.Mu,v,body) ->
        let env' = add_bound env v in
        let body = conv_term_rec env' body in
        Term.mu body
      | Ast.Match (u,m,default) ->
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
                 |> Iter.exists
                   (fun (t,k) -> match t.term_cell with
                      | DB db ->
                        DB.level db < n_vars + k (* [k]: number of intermediate binders *)
                      | _ -> false)
               in
               if depends_on_vars then any_rhs_depends_vars := true;
               tys, rhs)
            m
        and default =
          CCOpt.map (fun (set,t) -> set, conv_term_rec env t) default
        in
        (* optim: check whether all branches return the same term, that
           does not depend on matched variables *)
        (* TODO: do the closedness check during conversion, above *)
        let rhs_l =
          ID.Map.values m
          |> Iter.map snd
          |> Iter.append (default |> CCOpt.map snd |> Iter.of_opt)
          |> Iter.sort_uniq ~cmp:Term.compare
          |> Iter.to_rev_list
        in
        begin match rhs_l with
          | [x] when not (!any_rhs_depends_vars) ->
            (* every branch yields the same [x], which does not depend
               on the argument: remove the match and return [x] instead *)
            x
          | _ ->
            let u = conv_term_rec env u in
            Term.match_ u m ~default
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
          | Ast.Eq ->
            let args, _ = Ty.unfold a.term_ty in
            begin match args with
              | [] -> Term.eq a b (* normal equality *)
              | _::_ ->
                (* equality on functions: becomes a forall *)
                let n = List.length args in
                let db_l = List.mapi (fun i ty -> Term.db (n-i-1,ty)) args in
                let body =
                  Term.eq
                    (Term.app (Term.shift_db n a) db_l)
                    (Term.app (Term.shift_db n b) db_l)
                in
                Term.quant_ty_l ~depth:0 Forall args body
            end
        end
      | Ast.Undefined_value ->
        Term.undefined_value (conv_ty t.Ast.ty) Undef_absolute
      | Ast.Asserting (t, g) ->
        (* [t asserting g] becomes [if g t fail] *)
        let t = conv_term_rec env t in
        let g = conv_term_rec env g in
        Term.if_ g t (Term.undefined_value t.term_ty Undef_absolute)

    let conv_term ?(env=empty_env) t =
      let u = conv_term_rec env t in
      Log.debugf 2
        (fun k->k "(@[conv_term@ @[%a@]@ yields: %a@])" Ast.pp_term t Term.pp u);
      Term.check_db u; (* ensure DB indices are fine *)
      u

    (* simple prefix skolemization: if [t = exists x1...xn. u],
       declare [x1...xn] as new unknowns (not to be in the final model)
       and return [u] instead, as well as an environment
       that maps [x_i] to their corresponding new unknowns *)
    let skolemize t : conv_env * Ast.term =
      let rec aux env t = match Ast.term_view t with
        | Ast.Bind (Ast.Exists, v, u) ->
          let ty = conv_ty (Ast.Var.ty v) in
          let c_id = ID.makef "?%s" (Ast.Var.id v |> ID.to_string) in
          let c = Typed_cst.make_undef ~depth:0 c_id ty in
          let env = add_let_bound env v (Term.const c) in
          aux env u
        | _ -> env, t
      in
      aux empty_env t

    let is_prove_ = ref false

    let add_statement st =
      Log.debugf 2
        (fun k->k "(@[add_statement@ @[%a@]@])" Ast.pp_statement st);
      model_env_ := Ast.env_add_statement !model_env_ st;
      match st with
        | Ast.Assert t ->
          let env, t = skolemize t in
          let t = conv_term ~env t in
          Top_goals.push t;
          push_clause (Clause.make [Lit.atom t])
        | Ast.Goal {prove;vars;body=t} ->
          is_prove_ := !is_prove_ || prove;
          (* skolemize *)
          let env, consts =
            CCList.fold_map
              (fun env v ->
                 let ty = Ast.Var.ty v |> conv_ty in
                 let c = Typed_cst.make_undef ~depth:0 (Ast.Var.id v) ty in
                 add_let_bound env v (Term.const c), c)
              empty_env
              vars
          in
          (* model should contain values of [consts] *)
          List.iter add_cst_support_ consts;
          let t = conv_term_rec env t in
          let t = if prove then Term.not_ t else t in
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
          let cst = Typed_cst.make_undef ~depth:0 id ty in
          add_cst_support_ cst; (* need it in model *)
          ID.Tbl.add decl_ty_ id (Lazy.from_val cst)
        | Ast.Data l ->
          (* declare the type, and all the constructors *)
          List.iter
            (fun {Ast.Ty.data_id; data_cstors} ->
               let ty = lazy (
                 let cstors =
                   ID.Map.to_seq data_cstors
                   |> Iter.map
                     (fun (id_c, ty_c) ->
                        let c = lazy (
                          let ty_c = conv_ty ty_c in
                          Typed_cst.make_cstor id_c ty_c
                        ) in
                        ID.Tbl.add decl_ty_ id_c c; (* declare *)
                        c)
                   |> Iter.to_rev_list
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
                 Typed_cst.make_defined id ty rhs
               ) in
               ID.Tbl.add decl_ty_ id cst)
            l;
          (* force thunks *)
          List.iter
            (fun (id,_,_) ->
               let c = ID.Tbl.find decl_ty_ id |> Lazy.force in
               begin match c.cst_kind with
                 | Cst_defined (lazy _) -> () (* also force definition *)
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
        | Const cst -> A.const cst.cst_id (ty_to_ast t.term_ty)
        | App (f,l) -> A.app (aux env f) (List.map (aux env) l)
        | Fun (ty,bod) ->
          with_var ty env
            ~f:(fun v env -> A.fun_ v (aux env bod))
        | Mu _ -> assert false
        | If (g,t,{term_cell=Undefined_value _;_}) ->
          A.asserting (aux env t) (aux env g)
        | If (a,b,c) -> A.if_ (aux env a)(aux env b) (aux env c)
        | Match (u,m,default) ->
          let u = aux env u in
          let m =
            ID.Map.map
              (fun (tys,rhs) ->
                 with_vars tys env ~f:(fun vars env -> vars, aux env rhs))
              m
          and default =
            CCOpt.map (fun (set,t) -> set, aux env t) default
          in
          A.match_ u m ~default
        | Select (sel, u) ->
          let u' = aux env u in
          let sel' = {
            Ast.
            select_name=Lazy.from_val sel.select_name;
            select_cstor=sel.select_cstor.cst_id;
            select_i=sel.select_i;
          }
          in
          Ast.select sel' u' (ty_to_ast t.term_ty)
        | Switch (u,m) ->
          let u = aux env u in
          let m =
            ID.Tbl.to_seq m.switch_tbl
            |> Iter.map (fun (c,rhs) -> c, aux env rhs)
            |> ID.Map.of_seq
          in
          A.switch u m
        | Quant (q,qr,bod) ->
          let ty = match qr with
            | QR_unin uty -> Lazy.force uty.uty_self
            | QR_bool -> Ty.prop
            | QR_data d -> d.q_data_ty
          in
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
        | Check_assign (c,t) ->
          aux env (Term.eq (Term.const c) t) (* becomes a mere equality *)
        | Check_empty_uty _ -> assert false
        | Undefined_value _ -> assert false
      in aux DB_env.empty t
  end

  let is_prove() = !Conv.is_prove_

  (** {2 Main} *)

  type unknown =
    | U_timeout
    | U_max_depth
    | U_incomplete
    | U_undefined_values

  let pp_unknown out = function
    | U_timeout -> CCFormat.string out "timeout"
    | U_max_depth -> CCFormat.string out "max_depth"
    | U_incomplete -> CCFormat.string out "incomplete"
    | U_undefined_values  -> CCFormat.string out "undefined_values"

  type model = Model.t

  type res =
    | Sat of model
    | Unsat (* TODO: proof *)
    | Unknown of unknown

  (* follow "normal form" pointers deeply in the term *)
  let deref_deep (doms:cst list Ty.Tbl.t) (t:term) : term =
    let rec aux t =
      let _, t = Reduce.compute_nf t in
      begin match t.term_cell with
        | True | False | DB _ -> t
        | Const c ->
          begin match c.cst_kind with
            | Cst_undef (_, Some {
                uty_status=Some (_, Uty_nonempty);
                uty_pair=Lazy_some(dom_elt,_); _}) ->
              (* unassigned unknown of some non-empty slice of
                 an uninterpreted type:
                 assign it to the first element of its slice.
                 This should introduce no conflict: any conflict would have
                 blocked evaluation of at least one goal earlier *)
              Term.const dom_elt
            | _ -> t
          end
        | App (f,l) ->
          Term.app (aux f) (List.map aux l)
        | If (a,b,c) -> Term.if_ (aux a)(aux b)(aux c)
        | Match (u,m,d) ->
          let m = ID.Map.map (fun (tys,rhs) -> tys, aux rhs) m in
          let d = CCOpt.map (fun (s,t) -> s, aux t) d in
          Term.match_ (aux u) m ~default:d
        | Select (sel,u) -> Term.select sel (aux u)
        | Switch (u,m) ->
          let dom =
            try Ty.Tbl.find doms m.switch_ty_arg
            with Not_found ->
              errorf "could not find domain of type %a" Ty.pp m.switch_ty_arg
          in
          let switch_tbl=
            ID.Tbl.to_seq m.switch_tbl
            |> Iter.filter_map
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
              Typed_cst.make_undef ~depth:0
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
        | Undefined_value _ -> t
        | Check_assign _
        | Check_empty_uty _
          -> assert false
      end
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
      |> Iter.of_list
      |> Iter.map
        (fun ty -> match ty.ty_cell with
           | Atomic (_, Uninterpreted uty) -> ty, find_domain_ uty
           | _ -> assert false)
      |> Ty.Tbl.of_seq
    in
    (* compute values of meta variables *)
    let consts =
      !model_support_
      |> Iter.of_list
      |> Iter.map
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
      |> Iter.map
        (fun (ty,dom) ->
           let dom = match dom with
             | [] -> [ID.make (Printf.sprintf "$%s_0" (Ty.mangle ty))]
             | l -> List.map Typed_cst.id l
           in
           Conv.ty_to_ast ty, dom)
      |> Ast.Ty.Map.of_seq
    in
    Model.make ~env ~consts ~domains

  let model_check () =
    Log.debugf 1 (fun k->k "checking model…");
    Top_goals.check()

  let clause_of_mclause (c:M.Clause.t): Clause.t =
    M.Clause.atoms_l c |> List.map M.Atom.formula |> Clause.make

  let pp_stats out () : unit =
    Format.fprintf out
      "(@[<hv1>stats@ \
       :num_expanded %d@ \
       :num_uty_expanded %d@ \
       :num_clause_push %d@ \
       :num_clause_tautology %d@ \
       :num_lits %d@ \
       :num_propagations %d@ \
       :num_unif %d@ \
       :num_undefined %d@ \
       :has_lost_model %B\
       @])"
      !stat_num_cst_expanded
      !stat_num_uty_expanded
      !stat_num_clause_push
      !stat_num_clause_tautology
      (Top_terms.size())
      !stat_num_propagations
      !stat_num_unif
      !stat_num_undefined
      !has_lost_models

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
      | M.Proof.Hyper_res {M.Proof.hr_init=p1; hr_steps} ->
        Format.fprintf out "(@[<1>hyper-res@ %a@])"
          (CCFormat.list pp_step_res) (p1 :: List.map snd hr_steps)
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
    | PS_undefined_values
    | PS_incomplete
    | PS_unroll_quant

  let pp_proof_status out = function
    | PS_depth_limited lit ->
      Format.fprintf out "(@[depth_limited@ by: %a@])" Lit.pp lit
    | PS_complete -> CCFormat.string out "complete"
    | PS_undefined_values -> CCFormat.string out "undefined_values"
    | PS_incomplete -> CCFormat.string out "incomplete"
    | PS_unroll_quant -> CCFormat.string out "unroll-quant"

  (* precondition: solving under assumption [depth_lit] returned unsat *)
  let proof_status depth_lit quant_lit : proof_status =
    let sat_res =
      M_th.set_active false; (* no propagation, just check the boolean formula *)
      CCFun.finally
        ~h:(fun () -> M_th.set_active true)
        ~f:(fun () -> M.solve ~assumptions:[quant_lit] msat)
    in
    begin match sat_res with
      | M.Sat _ ->
        (* was unsat because of the assumption *)
        PS_depth_limited depth_lit
      | M.Unsat us ->
        (* really unsat, now we need to know if it involves some
           incomplete choices *)
        let p = us.SI.get_proof () in
        if Config.check_proof then M.Proof.check p;
        begin match !has_met_undefined with
          | Some Undef_absolute -> PS_undefined_values
          | Some (Undef_quant _) -> PS_unroll_quant
          | None ->
            if !has_lost_models then PS_undefined_values
            else if !incomplete_expansion then PS_incomplete
            else PS_complete
        end
    end

  let dump_dimacs () = match Config.dimacs_file with
    | None -> ()
    | Some file ->
      Log.debugf 2 (fun k->k "dump SAT problem into file `%s`" file);
      assert false
        (* TODO
      CCIO.with_out file
        (fun oc ->
           let out = Format.formatter_of_out_channel oc in
           Format.fprintf out "@[<v>%a@]@." M.export_dimacs ())
           *)

  let solve ?(on_exit=[]) ?(check=true) () =
    let on_exit = dump_dimacs :: on_exit in
    Msat.Log.set_debug_out Format.std_formatter;
    (* Msat.Log.set_debug 50; *)
    let module ID = Iterative_deepening in
    (* iterated deepening *)
    let rec iter state q_depth = match state with
      | ID.Exhausted ->
        do_on_exit ~on_exit;
        Unknown U_max_depth
      | ID.At (cur_depth, depth_lit) ->
        Log.debugf 2
          (fun k->k "@{<Yellow>start solving@} at depth %a, quant-depth %d"
              ID.pp cur_depth q_depth);
        (* restrict unfolding of quantifiers *)
        let q_lit = M.make_atom msat @@ Lit.quant_unroll q_depth in
        has_met_undefined := None; (* reset this *)
        match M.solve ~assumptions:[M.make_atom msat depth_lit; q_lit] msat with
          | M.Sat _ ->
            let m = compute_model_ () in
            Log.debugf 1
              (fun k->k "@{<Yellow>** found SAT@} at depth %a, quant-depth %d"
                  ID.pp cur_depth q_depth);
            do_on_exit ~on_exit;
            if check then model_check ();
            Sat m
          | M.Unsat us ->
            (* check if [max depth] literal involved in proof;
               - if yes, try next level
               - if not but some goal evaluated to [undefined] because of
                 quantifier unrolling limit, then try again with higher limit
               - if not but [has_met_undefined=true] or some expansion
                 was not exhaustive (e.g. functions), UNKNOWN
               - else, truly UNSAT
            *)
            let p = us.SI.get_proof () in
            Log.debugf 4 (fun k->k "proof: @[%a@]@." pp_proof p);
            if Config.check_proof then M.Proof.check p;
            let status = proof_status depth_lit q_lit in
            Log.debugf 1
              (fun k->k
                  "@{<Yellow>** found Unsat@} at depth %a, quand-depth %d;@ \
                   status: %a"
                  ID.pp cur_depth q_depth pp_proof_status status);
            begin match status with
              | PS_depth_limited _ ->
                (* negation of the previous limit *)
                push_clause (Clause.make [Lit.neg depth_lit]);
                iter (ID.next ()) q_depth (* deeper! *)
              | PS_undefined_values ->
                do_on_exit ~on_exit;
                Unknown U_undefined_values
              | PS_incomplete ->
                do_on_exit ~on_exit;
                Unknown U_incomplete
              | PS_unroll_quant ->
                (* increase quantifier unrolling depth *)
                let q_depth = q_depth + 1 in
                Log.debugf 1
                  (fun k->k "@{<Yellow>increase quantifier unroll depth@} :to %d"
                      q_depth);
                iter state q_depth
              | PS_complete ->
                do_on_exit ~on_exit;
                Unsat
            end
    in
    Top_terms.update_all ();
    ID.reset ();
    iter (ID.current ()) Config.quant_unfold_depth
end

