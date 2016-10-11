
(* This file is free software. See file "license" for more details. *)

let get_time : unit -> float =
  let start = Unix.gettimeofday() in
  fun () ->
    Unix.gettimeofday() -. start

module IArray = CCImmutArray

module FI = Msat.Formula_intf
module TI = Msat.Theory_intf
module SI = Msat.Solver_intf

let (~!) = Lazy.force

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
  let stat_num_unif = ref 0

  module Term_bits = CCBitField.Make(struct end)

  (* for objects that are expanded on demand only *)
  type 'a lazily_expanded =
    | Lazy_some of 'a
    | Lazy_none

  and db = int * ty_h

  (* main term cell.

     A term contains its own information about the equivalence class it
     belongs to. An equivalence class is represented by its "root" element,
     the representative. *)
  and term = {
    mutable term_id: int; (* unique ID *)
    mutable term_ty: ty_h;
    term_cell: term_cell;
    mutable term_bits: Term_bits.t; (* bitfield for various properties *)
    mutable term_parents: term Bag.t; (* parent terms of the whole equiv class *)
    mutable term_root: term; (* representative of congruence class *)
    mutable term_expl: (term * explanation) option;
    (* the rooted forest for explanations *)
    mutable term_nf: term_nf option; (* normal form? *)
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
    | Case of term * term ID.Map.t (* check head constructor *)
    | Builtin of builtin

  and builtin =
    | B_not of term
    | B_eq of term * term
    | B_and of term * term
    | B_or of term * term
    | B_imply of term * term

  (* Weak Head Normal Form *)
  and term_nf =
    | NF_cstor of data_cstor * term list
    | NF_bool of bool
    | NF_dom_elt of cst

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

  and cst = {
    cst_id: ID.t;
    cst_kind: cst_kind;
  }

  and cst_kind =
    | Cst_undef of ty_h * cst_info
    | Cst_cstor of data_cstor
    | Cst_proj of ty_h * data_cstor * int (* [cstor, argument position] *)
    | Cst_defined of ty_h * term lazy_t

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
  }

  (* this is a disjunction of sufficient conditions for the existence of
     some meta (cst). Each condition is a literal *)
  and cst_exist_conds = lit lazy_t list ref

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
    | Uninterpreted
    | Data of datatype (* set of constructors *)

  and datatype = {
    data_ty: ty_h; (* the type itself *)
    data_cstors: data_cstor lazy_t list;
  }

  (* a constructor *)
  and data_cstor = {
    cstor_ty: ty_h lazy_t;
    cstor_args: ty_h lazy_t IArray.t; (* argument types *)
    cstor_proj: cst lazy_t IArray.t; (* projectors *)
    cstor_cst: cst;
  }

  and ty_cell =
    | Prop
    | Atomic of ID.t * ty_def
    | Arrow of ty_h * ty_h

  module Ty : sig
    type t = ty_h
    val view : t -> ty_cell
    val equal : t -> t -> bool
    val compare : t -> t -> int
    val hash : t -> int

    val prop : t
    val atomic : ID.t -> ty_def -> t
    val arrow : t -> t -> t
    val arrow_l : t list -> t -> t

    val is_prop : t -> bool
    val is_data : t -> bool
    val unfold : t -> t list * t

    val pp : t CCFormat.printer
    val mangle : t -> string
    module Tbl : CCHashtbl.S with type key = t
  end = struct
    type t = ty_h

    let view t = t.ty_cell

    let equal a b = a.ty_id = b.ty_id
    let compare a b = CCOrd.int_ a.ty_id b.ty_id
    let hash a = a.ty_id

    module Tbl_cell = CCHashtbl.Make(struct
        type t = ty_cell
        let equal a b = match a, b with
          | Prop, Prop -> true
          | Atomic (i1,_), Atomic (i2,_) -> ID.equal i1 i2
          | Arrow (a1,b1), Arrow (a2,b2) ->
            equal a1 a2 && equal b1 b2
          | Prop, _
          | Atomic _, _
          | Arrow _, _ -> false

        let hash t = match t with
          | Prop -> 1
          | Atomic (i,_) -> Hash.combine2 2 (ID.hash i)
          | Arrow (a,b) -> Hash.combine3 3 (hash a) (hash b)
      end)

    (* build a type *)
    let make_ : ty_cell -> t =
      let tbl : t Tbl_cell.t = Tbl_cell.create 128 in
      let n = ref 0 in
      fun c ->
        try Tbl_cell.find tbl c
        with Not_found ->
          let ty_id = !n in
          incr n;
          let ty = {ty_id; ty_cell=c;} in
          Tbl_cell.add tbl c ty;
          ty

    let prop = make_ Prop

    let atomic id def = make_ (Atomic (id,def))

    let arrow a b = make_ (Arrow (a,b))
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

  module Typed_cst : sig
    type t = cst
    val id : t -> ID.t
    val ty : t -> Ty.t
    val make_cstor : ID.t -> data_cstor -> t
    val make_defined : ID.t -> Ty.t -> term lazy_t -> t
    val make_undef :
      ?parent:cst -> ?exist_if:cst_exist_conds -> ID.t -> Ty.t -> t
    val depth : t -> int
    val equal : t -> t -> bool
    val compare : t -> t -> int
    val hash : t -> int
    val as_undefined : t -> (t * Ty.t * cst_info) option
    val as_undefined_exn : t -> t * Ty.t * cst_info
    val pp : t CCFormat.printer
    module Map : CCMap.S with type key = t
  end = struct
    type t = cst

    let id t = t.cst_id

    let ty_of_kind = function
      | Cst_defined (ty, _)
      | Cst_undef (ty, _)
      | Cst_proj (ty, _, _) -> ty
      | Cst_cstor cstor -> ~!(cstor.cstor_ty)

    let ty t = ty_of_kind t.cst_kind

    let make cst_id cst_kind = {cst_id; cst_kind}
    let make_cstor id cstor =
      let _, ret = Ty.unfold ~!(cstor.cstor_ty) in
      assert (Ty.is_data ret);
      make id (Cst_cstor cstor)
    let make_defined id ty t = make id (Cst_defined (ty, t))

    let make_undef ?parent ?exist_if id ty =
      let info =
        let cst_depth = match parent with
          | Some {cst_kind=Cst_undef (_, i); _} -> i.cst_depth + 1
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
        }
      in
      make id (Cst_undef (ty, info))

    let depth (c:t): int = match c.cst_kind with
      | Cst_undef (_, i) -> i.cst_depth
      | _ -> assert false

    let as_undefined (c:t) = match c.cst_kind with
      | Cst_undef (ty,i) -> Some (c,ty,i)
      | Cst_defined _ | Cst_cstor _ | Cst_proj _
        -> None

    let as_undefined_exn (c:t): t * Ty.t * cst_info =
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

  let cmp_lit a b =
    let c = CCOrd.bool_ a.lit_sign b.lit_sign in
    if c<>0 then c
    else
      let int_of_cell_ = function
        | Lit_fresh _ -> 0
        | Lit_atom _ -> 1
        | Lit_assign _ -> 2
      in
      match a.lit_view, b.lit_view with
        | Lit_fresh i1, Lit_fresh i2 -> ID.compare i1 i2
        | Lit_atom t1, Lit_atom t2 -> term_cmp_ t1 t2
        | Lit_assign (c1,t1), Lit_assign (c2,t2) ->
          CCOrd.(Typed_cst.compare c1 c2 <?> (term_cmp_, t1, t2))
        | Lit_fresh _, _
        | Lit_atom _, _
        | Lit_assign _, _
          -> CCOrd.int_ (int_of_cell_ a.lit_view) (int_of_cell_ b.lit_view)

  let hash_lit a =
    let sign = a.lit_sign in
    match a.lit_view with
      | Lit_fresh i -> Hash.combine3 1 (Hash.bool sign) (ID.hash i)
      | Lit_atom t -> Hash.combine3 2 (Hash.bool sign) (term_hash_ t)
      | Lit_assign (c,t) ->
        Hash.combine4 3 (Hash.bool sign) (Typed_cst.hash c) (term_hash_ t)

  module Backtrack : sig
    val dummy_level : level
    val cur_level : unit -> level
    val push_level : unit -> unit
    val backtrack : level -> unit
    val push_undo : (unit -> unit) -> unit
  end = struct
    type _level = level
    type level = _level

    let dummy_level = -1

    type stack_cell = unit -> unit (* "undo" operation *)
    type stack = stack_cell CCVector.vector

    (* the global stack *)
    let st_ : stack = CCVector.create()

    let backtrack (l:level): unit =
      Log.debugf 2
        (fun k->k "@{<Yellow>** now at level %d (backtrack)@}" l);
      while CCVector.length st_ > l do
        let f = CCVector.pop_exn st_ in
        f()
      done;
      ()

    let cur_level () = CCVector.length st_

    let push_level () : unit =
      let l = cur_level() in
      Log.debugf 2 (fun k->k "@{<Yellow>** now at level %d (push)@}" l);
      ()

    let push_undo f = CCVector.push st_ f
  end

  let new_switch_id_ =
    let n = ref 0 in
    fun () -> incr n; !n

  (* TODO: normalization of {!term_cell} for use in signatures? *)

  module Term_cell : sig
    type t = term_cell

    val equal : t -> t -> bool
    val hash : t -> int

    val true_ : t
    val false_ : t
    val db : DB.t -> t
    val const : cst -> t
    val app : term -> term list -> t
    val fun_ : Ty.t -> term -> t
    val mu : term -> t
    val case : term -> term ID.Map.t -> t
    val if_ : term -> term -> term -> t
    val builtin : builtin -> t
    val and_ : term -> term -> t
    val or_ : term -> term -> t
    val not_ : term -> t
    val imply : term -> term -> t
    val eq : term -> term -> t

    val ty : t -> Ty.t
    (** Compute the type of this term cell. Not totally free *)

    module Tbl : CCHashtbl.S with type key = t
  end = struct
    type t = term_cell
    let sub_hash (t:term): int = t.term_id

    let hash (t:term_cell) : int = match t with
      | True -> 1
      | False -> 2
      | DB d -> Hash.combine DB.hash 3 d
      | Const c ->
        Hash.combine2 4 (Typed_cst.hash c)
      | App (f,l) ->
        Hash.combine3 5 f.term_id (Hash.list sub_hash l)
      | Fun (ty, f) -> Hash.combine3 6 (Ty.hash ty) f.term_id
      | If (a,b,c) -> Hash.combine4 7 a.term_id b.term_id c.term_id
      | Case (u,m) ->
        let hash_m =
          Hash.seq (Hash.pair ID.hash sub_hash) (ID.Map.to_seq m)
        in
        Hash.combine3 8 u.term_id hash_m
      | Builtin (B_not a) -> Hash.combine2 20 a.term_id
      | Builtin (B_and (t1,t2)) -> Hash.combine3 21 t1.term_id t2.term_id
      | Builtin (B_or (t1,t2)) -> Hash.combine3 22 t1.term_id t2.term_id
      | Builtin (B_imply (t1,t2)) -> Hash.combine3 23 t1.term_id t2.term_id
      | Builtin (B_eq (t1,t2)) -> Hash.combine3 24 t1.term_id t2.term_id
      | Mu sub -> Hash.combine sub_hash 30 sub

    (* equality that relies on physical equality of subterms *)
    let equal a b = match a, b with
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
      | Case (u1, m1), Case (u2, m2) ->
        u1 == u2 &&
        ID.Map.for_all
          (fun k1 rhs1 ->
             try rhs1 == ID.Map.find k1 m2
             with Not_found -> false)
          m1
        &&
        ID.Map.for_all (fun k2 _ -> ID.Map.mem k2 m1) m2
      | Builtin b1, Builtin b2 ->
        begin match b1, b2 with
          | B_not a1, B_not a2 -> a1 == a2
          | B_and (a1,b1), B_and (a2,b2)
          | B_or (a1,b1), B_or (a2,b2)
          | B_eq (a1,b1), B_eq (a2,b2)
          | B_imply (a1,b1), B_imply (a2,b2) -> a1 == a2 && b1 == b2
          | B_not _, _ | B_and _, _ | B_eq _, _
          | B_or _, _ | B_imply _, _ -> false
        end
      | Mu t1, Mu t2 -> t1==t2
      | True, _
      | False, _
      | DB _, _
      | Const _, _
      | App _, _
      | Fun _, _
      | If _, _
      | Case _, _
      | Builtin _, _
      | Mu _, _
        -> false

    let true_ = True
    let false_ = False
    let db d = DB d
    let const c = Const c

    let app f l = match l with
      | [] -> f.term_cell
      | _ ->
        begin match f.term_cell with
          | App (f1, l1) ->
            let l' = l1 @ l in
            App (f1, l')
          | _ -> App (f,l)
        end

    let fun_ ty body = Fun (ty, body)
    let mu t = Mu t
    let case u m = Case (u,m)
    let if_ a b c =
      assert (Ty.equal b.term_ty c.term_ty);
      If (a,b,c)

    let builtin b =
      (* normalize a bit *)
      let b = match b with
        | B_eq (a,b) when a.term_id > b.term_id -> B_eq (b,a)
        | B_and (a,b) when a.term_id > b.term_id -> B_and (b,a)
        | B_or (a,b) when a.term_id > b.term_id -> B_or (b,a)
        | _ -> b
      in
      Builtin b

    let not_ t = match t.term_cell with
      | True -> False
      | False -> True
      | Builtin (B_not t') -> t'.term_cell
      | _ -> builtin (B_not t)

    let and_ a b = builtin (B_and (a,b))
    let or_ a b = builtin (B_or (a,b))
    let imply a b = builtin (B_imply (a,b))
    let eq a b = builtin (B_eq (a,b))

    (* type of an application *)
    let rec app_ty_ ty l : Ty.t = match Ty.view ty, l with
      | _, [] -> ty
      | Arrow (ty_a,ty_rest), a::tail ->
        assert (Ty.equal ty_a a.term_ty);
        app_ty_ ty_rest tail
      | (Prop | Atomic _), _::_ ->
        assert false

    let ty (t:t): Ty.t = match t with
      | True | False -> Ty.prop
      | DB d -> DB.ty d
      | Const c -> Typed_cst.ty c
      | App (f, l) -> app_ty_ f.term_ty l
      | If (_,b,_) -> b.term_ty
      | Case (_,m) ->
        let _, rhs = ID.Map.choose m in
        rhs.term_ty
      | Builtin _ -> Ty.prop
      | Mu t -> t.term_ty
      | Fun (ty,body) -> Ty.arrow ty body.term_ty

    module Tbl = CCHashtbl.Make(struct
        type t = term_cell
        let equal = equal
        let hash = hash
      end)
  end

  module Term : sig
    type t = term

    module Field_in_cc : Term_bits.FIELD with type value = bool
    module Field_expanded : Term_bits.FIELD with type value = bool

    val id : t -> int
    val ty : t -> Ty.t
    val equal : t -> t -> bool
    val compare : t -> t -> int
    val hash : t -> int

    val get : term_cell -> term option
    (** If term exists, return it *)

    val make : term_cell -> term

    val true_ : t
    val false_ : t
    val db : DB.t -> t
    val const : cst -> t
    val app : t -> t list -> t
    val app_cst : cst -> t list -> t
    val fun_ : Ty.t -> t -> t
    val fun_l : Ty.t list -> t -> t
    val mu : t -> t
    val case : t -> t ID.Map.t -> t
    val and_ : t -> t -> t
    val or_ : t -> t -> t
    val not_ : t -> t
    val imply : t -> t -> t
    val eq : t -> t -> t
    val neq : t -> t -> t
    val and_eager : t -> t -> t (* evaluate left argument first *)

    val and_l : t list -> t
    val or_l : t list -> t

    val abs : t -> t * bool

    val map_builtin : (t -> t) -> builtin -> builtin
    val builtin_to_seq : builtin -> t Sequence.t

    val to_seq : t -> t Sequence.t

    val pp : t CCFormat.printer

    (** {6 Views} *)

    val is_const : t -> bool

    (* return [Some] iff the term is an undefined constant *)
    val as_cst_undef : t -> (cst * Ty.t * cst_info) option

    val as_cstor_app : t -> (cst * data_cstor * t list) option

    (* typical view for unification/equality *)
    type unif_form =
      | Unif_cst of cst * Ty.t * cst_info
      | Unif_cstor of cst * data_cstor * term list
      | Unif_none

    val as_unif : t -> unif_form

    (** {6 Containers} *)

    module Tbl : CCHashtbl.S with type key = t
    module Map : CCMap.S with type key = t
  end = struct
    type t = term

    module Field_in_cc = (val (Term_bits.bool ~name:"in_cc" ()))
    module Field_expanded = (val (Term_bits.bool ~name:"expanded" ()))
    let () = Term_bits.freeze()

    let id t = t.term_id
    let ty t = t.term_ty

    let equal = term_equal_
    let hash = term_hash_
    let compare a b = CCOrd.int_ a.term_id b.term_id

    let (make, get : (term_cell -> term) * (term_cell -> term option)) =
      let tbl : term Term_cell.Tbl.t = Term_cell.Tbl.create 2048 in
      let n = ref 0 in
      let get c =
        Term_cell.Tbl.get tbl c
      and make c =
        try Term_cell.Tbl.find tbl c
        with Not_found ->
          let term_ty = Term_cell.ty c in
          let rec t = {
            term_id= !n;
            term_ty;
            term_parents=Bag.empty;
            term_bits=Term_bits.empty;
            term_root=t;
            term_expl=None;
            term_cell=c;
            term_nf=None;
          } in
          incr n;
          Term_cell.Tbl.add tbl c t;
          t
      in
      make, get

    let true_ = make True
    let false_ = make False

    let db d = make (DB d)

    let const c = make (Term_cell.const c)

    let app f l = match l with
      | [] -> f
      | _ -> make (Term_cell.app f l)

    let app_cst f l = app (const f) l

    let fun_ ty body = make (Term_cell.fun_ ty body)

    let fun_l = List.fold_right fun_

    let mu t = make (Term_cell.mu t)

    let case u m = make (Term_cell.case u m)

    let if_ a b c = make (Term_cell.if_ a b c)

    let not_ t = make (Term_cell.not_ t)

    let and_ a b = make (Term_cell.and_ a b)
    let or_ a b = make (Term_cell.or_ a b)
    let imply a b = make (Term_cell.imply a b)
    let eq a b = make (Term_cell.eq a b)
    let neq a b = not_ (eq a b)

    (* "eager" and, evaluating [a] first *)
    let and_eager a b = if_ a b false_

    (* might need to tranfer the negation from [t] to [sign] *)
    let abs t : t * bool = match t.term_cell with
      | False -> true_, false
      | Builtin (B_not t) -> t, false
      | _ -> t, true

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
        | B_and (a,b) ->
          let acc, a, b = fold_binary acc a b in
          acc, B_and (a,b)
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
      | B_and (a,b) -> yield a; yield b

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
          | DB _ | Const _ | True | False -> ()
          | App (f,l) -> aux f; List.iter aux l
          | If (a,b,c) -> aux a; aux b; aux c
          | Case (t, m) ->
            aux t;
            ID.Map.iter (fun _ rhs -> aux rhs) m
          | Builtin b -> builtin_to_seq b aux
          | Mu body
          | Fun (_, body) -> aux body
      in
      aux t

    (* return [Some] iff the term is an undefined constant *)
    let as_cst_undef (t:term): (cst * Ty.t * cst_info) option =
      match t.term_cell with
        | Const c -> Typed_cst.as_undefined c
        | _ -> None

    (* return [Some (cstor,ty,args)] if the term is a constructor
       applied to some arguments *)
    let as_cstor_app (t:term): (cst * data_cstor * term list) option =
      match t.term_cell with
        | Const ({cst_kind=Cst_cstor cstor; _} as c) -> Some (c,cstor,[])
        | App (f, l) ->
          begin match f.term_cell with
            | Const ({cst_kind=Cst_cstor cstor; _} as c) -> Some (c,cstor,l)
            | _ -> None
          end
        | _ -> None

    (* typical view for unification/equality *)
    type unif_form =
      | Unif_cst of cst * Ty.t * cst_info
      | Unif_cstor of cst * data_cstor * term list
      | Unif_none

    let as_unif (t:term): unif_form = match t.term_cell with
      | Const ({cst_kind=Cst_undef (ty,info); _} as c) ->
        Unif_cst (c,ty,info)
      | Const ({cst_kind=Cst_cstor cstor; _} as c) -> Unif_cstor (c,cstor,[])
      | App (f, l) ->
        begin match f.term_cell with
          | Const ({cst_kind=Cst_cstor ty; _} as c) -> Unif_cstor  (c,ty,l)
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
          fpf out "(@[<1>%a@ %a@])" pp f (Utils.pp_list pp) l
        | Fun (ty,f) ->
          fpf out "(@[fun %a@ %a@])" Ty.pp ty pp f
        | Mu sub -> fpf out "(@[mu@ %a@])" pp sub
        | If (a, b, c) ->
          fpf out "(@[if %a@ %a@ %a@])" pp a pp b pp c
        | Case (t,m) ->
          let pp_bind out (id,rhs) =
            fpf out "(@[<1>case %a@ %a@])" ID.pp id pp rhs
          in
          let print_map =
            CCFormat.seq ~start:"" ~stop:"" ~sep:" " pp_bind
          in
          fpf out "(@[match %a@ (@[<hv>%a@])@])"
            pp t print_map (ID.Map.to_seq m)
        | Builtin (B_not t) -> fpf out "(@[<hv1>not@ %a@])" pp t
        | Builtin (B_and (a,b)) ->
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
  end

  let pp_lit out l =
    let pp_lit_view out = function
      | Lit_fresh i -> Format.fprintf out "#%a" ID.pp i
      | Lit_atom t -> Term.pp out t
      | Lit_assign (c,t) ->
        Format.fprintf out "(@[:= %a@ %a@])" Typed_cst.pp c Term.pp t
    in
    if l.lit_sign then pp_lit_view out l.lit_view
    else Format.fprintf out "(@[@<1>¬@ %a@])" pp_lit_view l.lit_view

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
    val hash : t -> int
    val compare : t -> t -> int
    val equal : t -> t -> bool
    val print : t CCFormat.printer
    val pp : t CCFormat.printer
    val norm : t -> t * FI.negated
    module Set : CCSet.S with type elt = t
    module Tbl : CCHashtbl.S with type key = t
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
    module Tbl = CCHashtbl.Make(struct type t = lit let equal=equal let hash=hash end)
  end

  module Explanation : sig
    type t = explanation
    val empty : t
    val return : Lit.t -> t
    val append : t -> t -> t
    val cons : Lit.t -> t -> t
    val is_empty : t -> bool
  end = struct
    type t = explanation
    let empty : t = E_empty
    let return e = E_leaf e
    let append s1 s2 = match s1, s2 with
      | E_empty, _ -> s2
      | _, E_empty -> s1
      | _ -> E_append (s1, s2)
    let cons e s = append (return e) s

    let is_empty = function
      | E_empty -> true
      | E_leaf _ | E_append _ -> false (* by smart cstor *)
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

  (* TODO: remove, replace with "blocking atoms" (that block function
     calls that lead to recursive calls) *)

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

  (** {2 Congruence Closure} *)
  module CC : sig
    type repr = private term

    val equal : repr -> repr -> bool
    (** Are those equivalence classes the same? *)

    val find : term -> repr
    (** Current representative *)

    type update_res =
      | Sat
      | Unsat of repr * repr (* must merge those, but they are incompatible *)

    val union : repr -> repr -> Explanation.t -> update_res
    (** Merge the two equivalence classes *)

    val eval : repr -> term_nf option
    (** a WHNF, if any *)

    val eval_bool : repr -> bool option
    (** specialize {!eval} for propositions
        precond: the term is a boolean *)

    val explain : term -> term -> Explanation.t
    (** [explain t1 t2] returns a small explanation of why [t1=t2].
        precond: the terms have the same representative, ie [find t1 = find t2] *)

    val in_cc : term -> bool
    (** Is the term properly added to the congruence closure? *)

    val add_cc : term -> unit
    (** Add the term to the congruence closure.
        @raise Error if the current level is not 0 *)

    val add_cc_seq : term Sequence.t -> unit
    (** Add a sequence of terms to the congruence closure *)
  end = struct
    type repr = term

    let equal = Term.equal

    let is_root_ t = t.term_root == t
    let same_class_ (r1:repr)(r2:repr): bool = equal r1 r2
    let size_ (r:repr) = assert (is_root_ r); Bag.size r.term_parents

    (* check if [t] is in the congruence closure.
       Invariant: [in_cc t => in_cc u, forall u subterm t] *)
    let in_cc (t:term): bool = Term.Field_in_cc.get t.term_bits

    let signatures_tbl : repr Term_cell.Tbl.t = Term_cell.Tbl.create 2048
    (* map a signature to the corresponding equivalence class.
       A signature is a [term_cell] in which every immediate subterm
       that participates in the congruence/evaluation relation
       is normalized (i.e. is its own representative).
       The critical property is that all members of an equivalence class
       that have the same "shape" (including head symbol) have the same signature *)

    (* find representative *)
    let rec find t : repr =
      if t==t.term_root then t
      else (
        let old_root = t.term_root in
        let root = find old_root in
        (* path compression *)
        if root != old_root then (
          Backtrack.push_undo (fun () -> t.term_root <- old_root);
          t.term_root <- root;
        );
        root
      )

    let signature (t:term_cell): term_cell option = match t with
      | True | False | Const _ | DB _ | Fun _ | Mu _
        -> None
      | App (f, l) -> App (find f, List.map find l) |> CCOpt.return
      | If (a,b,c) -> If (find a, b, c) |> CCOpt.return
      | Case (t, m) -> Case (find t, m) |> CCOpt.return
      | Builtin b -> Builtin (Term.map_builtin find b) |> CCOpt.return

    (* find whether the given (parent) term corresponds to some signature
       in [signatures_] *)
    let find_by_signature (t:term_cell): repr option = match signature t with
      | None -> None
      | Some t' -> Term_cell.Tbl.get signatures_tbl t'

    let remove_signature (t:term_cell): unit = match signature t with
      | None -> ()
      | Some t' ->
        Term_cell.Tbl.remove signatures_tbl t'

    let add_signature (t:term_cell)(r:repr): unit = match signature t with
      | None -> ()
      | Some t' ->
        (* add, but only if not present already *)
        begin match Term_cell.Tbl.get signatures_tbl t' with
          | None ->
            Backtrack.push_undo (fun () -> Term_cell.Tbl.remove signatures_tbl t');
            Term_cell.Tbl.add signatures_tbl t' r;
          | Some r' -> assert (equal r r');
        end

    (* TODO: check-is-bool? or something like this? *)

    type update_res =
      | Sat
      | Unsat of repr * repr (* must merge those, but they are incompatible *)

    type update_state = {
      pending: term Queue.t;
      (* terms to check, maybe their new signature is in {!signatures_tbl} *)
      combine: (term * term * explanation) Queue.t;
      (* pairs of terms to merge *)
    }

    let st : update_state = {
      pending=Queue.create();
      combine=Queue.create();
    }

    let is_done_state (st:update_state): bool =
      Queue.is_empty st.pending &&
      Queue.is_empty st.combine

    let clear_state (st:update_state): unit =
      Queue.clear st.pending;
      Queue.clear st.combine;
      ()

    (* TODO:
         - make queues "pending" and "combine"
         - use "signature" to find whether a given term belongs to another class
         - use t.term_parents, check with signatures if those must be
           merged, and put them into combine
         - use Bad.append for merging the equiv. classes
         - deal with datatypes and evaluation rules
         - proof forest *)

    (* perform the congruence closure main algorithm *)
    let rec update (st:update_state): update_res =
      (* step 1: merge equivalence classes in [st.combine] *)
      while not (Queue.is_empty st.combine) do
        let a, b, e_ab = Queue.pop st.combine in
        let ra = find a in
        let rb = find b in
        if not (equal ra rb) then (
          assert (is_root_ ra);
          assert (is_root_ rb);
          (* TODO: datatype checks, inconsistency detection,
             injectivity, etc. if at least one of [(ra, rb)] has a non-null
             normal form *)
          (* invariant: [size ra <= size rb].
             we merge [ra] into [rb]. *)
          let ra, rb = if size_ ra > size_ rb then rb, ra else ra, rb in
          (* remove [ra.parents] from signature, put them into [st.pending] *)
          begin
            Bag.to_seq ra.term_parents
            |> Sequence.iter
              (fun parent ->
                 remove_signature parent.term_cell;
                 Queue.push parent st.pending)
          end;
          (* perform [union ra rb] *)
          begin
            let rb_old_parents = rb.term_parents in
            Backtrack.push_undo
              (fun () ->
                 ra.term_root <- ra;
                 rb.term_parents <- rb_old_parents);
            ra.term_root <- rb;
            rb.term_parents <- Bag.append rb_old_parents ra.term_parents;
          end;
          (* TODO: update proof forest (use [e_ab]?) *)
        )
      done;
      (* step 2 deal with pending (parent) terms whose equiv class
         might have changed *)
      let is_done = ref true in
      while not (Queue.is_empty st.pending) do
        let t = Queue.pop st.pending in
        match find_by_signature t.term_cell with
          | None ->
            (* add to the signature table *)
            add_signature t.term_cell (find t)
          | Some r ->
            (* must combine [t] with [r] *)
            (* TODO: get explanation right, e.g.
               by stating "congruence [list of subterms]" *)
            is_done := false;
            Queue.push (t, r, Explanation.empty) st.combine
      done;
      if !is_done
      then Sat
      else update st (* repeat *)

    let union (a:repr) (b:repr) (e:explanation): update_res =
      assert (is_root_ a);
      assert (is_root_ b);
      assert (is_done_state st);
      if not (same_class_ a b) then (
        Queue.push (a,b,e) st.combine; (* start by merging [a=b] *)
        update st
      ) else Sat

    let eval t =
      assert (is_root_ t);
      t.term_nf

    let eval_bool t = match eval t with
      | Some (NF_bool b) -> Some b
      | None -> None
      | Some (NF_cstor _ | NF_dom_elt _) -> assert false

    let explain a b =
      let r = find a in
      assert (find b == r);
      assert false (* TODO *)

    (* TODO: check that level=0, somehow *)

    let add_cc_seq (seq:term Sequence.t): unit =
      assert (is_done_state st);
      (* add [t] and the required subterms to the congruence closure *)
      let rec add_cc_pending (t:term): unit =
        if not (in_cc t) then (
          assert (is_root_ t);
          t.term_bits <- Term.Field_in_cc.set true t.term_bits;
          let add_sub sub =
            add_cc_pending sub;
            sub.term_parents <- t :: sub.term_parents
          in
          (* register sub-terms, add [t] to their parent list *)
          begin match t.term_cell with
            | True | False | Const _ | DB _ -> ()
            | App (f, l) ->
              add_sub f;
              List.iter add_sub l
            | Case (t, m) ->
              add_sub t;
              ID.Map.iter (fun _ rhs -> add_sub rhs) m
            | If (a,b,c) ->
              add_sub a;
              add_sub b;
              add_sub c
            | Mu _
            | Fun _ -> () (* not expanded yet *)
            | Builtin b -> Term.builtin_to_seq b add_sub
          end;
          Queue.push t st.pending
        )
      in
      seq add_cc_pending;
      (* now perform an update *)
      begin match update st with
        | Sat -> ()
        | Unsat _ -> assert false
      end

    let add_cc (t:term): unit = add_cc_seq (Sequence.return t)
  end

  (** {2 Case Expansion} *)

  let declare_defined_cst _ = ()

  module Expand : sig
    val expand_term : term -> unit
    (** Expand the term by making a case distinction, a boolean CNF,
        or nothing, depending on its type. Idempotent.
        precondition: [CC.in_cc t] *)
  end = struct
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

    (* TODO: revise the whole mechanism of depth guards *)

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
        | Atomic (_, Data data) ->
          (* datatype: refine by picking the head constructor *)
          info.cst_complete <- true;
          List.map
            (fun (lazy cstor)  ->
               let c = cstor.cstor_cst in
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
            data.data_cstors, []
        | Arrow (ty_arg, ty_ret) ->
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
          and fun_destruct =
            lazy (Term.fun_ ty_arg (Lazy.force body))
          (* constant function that does not look at input *)
          and body_const = lazy (
            let exist_if = ref [lazy (Lit.cst_choice cst (Lazy.force fun_const))] in
            (* only one parent in any case *)
            let c' = mk_sub_cst ty_ret ~parent:cst ~exist_if in
            Term.const c'
          )
          and fun_const =
            lazy (Term.fun_ ty_arg (Lazy.force body_const))
          in
          [Lazy.force fun_destruct; Lazy.force fun_const], []
        | Prop ->
          (* simply try true/false *)
          [Term.true_; Term.false_], []
      in
      (* build clauses *)
      let case_clauses = clauses_of_cases cst by_ty info.cst_depth in
      by_ty, List.rev_append other_clauses case_clauses

    (* expand the given constant so that, later, it will be
       assigned a value by the SAT solver *)
    let expand_cst (c:cst): unit =
      let ty, info = match c.cst_kind with
        | Cst_undef (ty,i,_) -> ty,i
        | Cst_defined _ | Cst_cstor _ | Cst_uninterpreted_dom_elt _ ->
          assert false
      in
      let depth = info.cst_depth in
      (* check whether [c] is expanded *)
      begin match info.cst_cases with
        | Lazy_none ->
          (* [c] is blocking, not too deep, but not expanded *)
          let l, clauses = expand_cases c ty info in
          Log.debugf 2
            (fun k->k "(@[<1>expand_cst@ @[%a@]@ :into (@[%a@])@ :depth %d@])"
                Typed_cst.pp c (Utils.pp_list Term.pp) l depth);
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
  let clause_guard_of_exp_ (e:explanation): Lit.t list Sequence.t =
    let l = Explanation.to_lists e in
    Sequence.map
      (fun e ->
         List.map Lit.neg e (* this is a guard! *)
         |> CCList.sort_uniq ~cmp:Lit.compare)
      l

  (** {2 Reduction to Normal Form} *)
  module Reduce = struct
    (* environment for evaluation: not-yet-evaluated terms *)
    type eval_env = term DB_env.t

    (* TODO: add a cache to {!eval_db}? *)

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
          | Const _ -> t
          | True
          | False -> t
          | Fun (ty, body) ->
            let body' = aux (DB_env.push_none env) body in
            if body==body' then t else Term.fun_ ty body'
          | Mu body ->
            let body' = aux (DB_env.push_none env) body in
            if body==body' then t else Term.mu body'
          | Quant (q, uty, body) ->
            let body' = aux (DB_env.push_none env) body in
            if body==body' then t else Term.quant q uty body'
          | Match (u, m) ->
            let u = aux env u in
            let m =
              ID.Map.map
                (fun (tys,rhs) ->
                   tys, aux (DB_env.push_none_l tys env) rhs)
                m
            in
            Term.match_ u m
          | Switch (u, m) ->
            let u = aux env u in
            (* NOTE: [m] should not contain De Bruijn indices at all *)
            Term.switch u m
          | If (a,b,c) ->
            let a' = aux env a in
            let b' = aux env b in
            let c' = aux env c in
            if a==a' && b==b' && c==c' then t else Term.if_ a' b' c'
          | App (_,[]) -> assert false
          | App (f, l) ->
            let f' = aux env f in
            let l' = aux_l env l in
            if f==f' && CCList.equal (==) l l' then t else Term.app f' l'
          | Builtin b -> Term.builtin (Term.map_builtin (aux env) b)
          | Check_assign _
          | Check_empty_uty _
            -> t (* closed *)
        and aux_l env l =
          List.map (aux env) l
        in
        aux env t
      )

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
        | DB _ -> Explanation.empty, t
        | True | False ->
          Explanation.empty, t (* always trivial *)
        | Const c ->
          begin match c.cst_kind with
            | Cst_defined (_, rhs) ->
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
          Explanation.empty, eval_db env body
        | Quant (q,uty,body) ->
          begin match uty.uty_status with
            | None -> Explanation.empty, t
            | Some (e, status) ->
              let c_head, uty_tail = match uty.uty_pair with
                | Lazy_none -> assert false
                | Lazy_some tup -> tup
              in
              let t1() =
                eval_db (DB_env.singleton (Term.const c_head)) body
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
              begin
                try
                  let tys, rhs = ID.Map.find (Typed_cst.id c) m in
                  if List.length tys = List.length l
                  then (
                    (* evaluate arguments *)
                    let env = DB_env.push_l l DB_env.empty in
                    (* replace in [rhs] *)
                    let rhs = eval_db env rhs in
                    (* evaluate new [rhs] *)
                    compute_nf rhs
                  )
                  else Explanation.empty, Term.match_ u' m
                with Not_found -> assert false
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
            | Cst_undef (_, {cst_cur_case=None;_}, _) ->
              Explanation.empty, t
            | Cst_undef (_, ({cst_cur_case=Some (_,case');_} as info), _) ->
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
            | Cst_cstor _ | Cst_defined _ ->
              assert false
          end
        | Check_empty_uty uty ->
          begin match uty.uty_status with
            | None -> Explanation.empty, t
            | Some (e, Uty_empty) -> e, Term.true_
            | Some (e, Uty_nonempty) -> e, Term.false_
          end

    (* apply [f] to [l], until no beta-redex is found *)
    and compute_nf_app env e f l = match f.term_cell, l with
      | Const {cst_kind=Cst_defined (_, lazy def_f); _}, l ->
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
        let e_f, f' = eval_db env f |> compute_nf in
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
           once their conjunction reduces to [true] or [false]. *)
        let e_a, c' = compute_nf a in
        let e_b, d' = compute_nf b in
        begin match c'.term_cell, d'.term_cell with
          | False, False ->
            (* combine explanations here *)
            Explanation.or_ e_a e_b, Term.false_
          | False, _ ->
            e_a, Term.false_
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
      | B_eq (a,b) ->
        assert (not (Ty.is_prop a.term_ty));
        let e_a, a' = compute_nf a in
        let e_b, b' = compute_nf b in
        let e_ab = Explanation.append e_a e_b in
        let default() =
          if a==a' && b==b' then old else Term.eq a' b'
        in
        if Term.equal a' b'
        then e_ab, Term.true_ (* syntactic *)
        else begin match Term.as_unif a', Term.as_unif b' with
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
                assert info.cst_complete;
                (* unification: use the literal [c := case] for
                   the [case in cases] that matches [cstor].
                   Reduce to [:= c case & case.i=args.i] *)
                let case,sub_metas =
                  CCList.find_map
                    (fun t -> match Term.as_cstor_app t with
                       | Some (cstor', _, sub_metas) ->
                         if Typed_cst.equal cstor cstor'
                         then Some (t,sub_metas)
                         else None
                       | None -> assert false)
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
          | Term.Unif_dom_elt (dom_elt,_, uty_dom_elt), Term.Unif_cst (c, _, _, _)
          | Term.Unif_cst (c, _, _, _), Term.Unif_dom_elt (dom_elt,_,uty_dom_elt) ->
            let dom_elt_offset = uty_dom_elt.uty_offset in
            (* we know that [uty] is expanded deep enough that [dom_elt]
               exists, so we can simply reduce [?c = dom_elt_n] into
               [¬empty(uty[0:]) & .. & ¬empty(uty[:n]) & ?c := dom_elt_n] *)
            let traverse e_c c uty = match uty.uty_pair with
              | Lazy_none ->
                (* we are too deep in [uty], cannot hold *)
                assert (dom_elt_offset < uty.uty_offset);
                Explanation.empty, Term.false_
              | Lazy_some _ when dom_elt_offset < uty.uty_offset ->
                (* we are too deep in [uty], cannot hold *)
                Explanation.empty, Term.false_
              | Lazy_some (dom_elt', _) ->
                Expand.expand_cst c;
                let check_uty = Term.check_empty_uty uty |> Term.not_ in
                if Typed_cst.equal dom_elt dom_elt'
                then (
                  incr stat_num_unif;
                  (* check assignment *)
                  Term.and_eager check_uty
                    (Term.check_assign c (Term.const dom_elt))
                  |> compute_nf_add e_c
                ) else (
                  begin match c.cst_kind with
                    | Cst_undef (_, {cst_cases=Lazy_some cases; _}, _) ->
                      (* [c=dom_elt' OR c=c'] *)
                      let c' = match cases with
                        | [a;b] ->
                          begin match Term.as_cst_undef a, Term.as_cst_undef b with
                            | Some (c',_,_,_), _ | _, Some (c',_,_,_) -> c'
                            | _ -> assert false
                          end
                        | _ -> assert false
                      in
                      assert (c != c');
                      Term.and_eager
                        check_uty
                        (Term.and_
                           (Term.check_assign c (Term.const c'))
                           (Term.eq (Term.const c') (Term.const dom_elt)))
                      |> compute_nf_add e_c
                    | Cst_undef (_, {cst_cases=Lazy_none; _}, _) ->
                      (* blocked: could not expand *)
                      e_c, Term.eq (Term.const c) (Term.const dom_elt)
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
          | _ -> e_ab, default()
        end

    let compute_nf_lit (lit:lit): explanation * lit =
      match Lit.view lit with
        | Lit_fresh _
        | Lit_assign (_,_)
        | Lit_uty_empty _ -> Explanation.empty, lit
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

    (* clauses for [e => l] *)
    let clause_imply (l:lit) (e:explanation): Clause.t Sequence.t =
      clause_guard_of_exp_ e
      |> Sequence.map
        (fun guard -> l :: guard |> Clause.make)

    let propagate_lit_ (l:t) (e:explanation): unit =
      let cs = clause_imply (to_lit l) e |> Sequence.to_rev_list in
      Log.debugf 4
        (fun k->k
            "(@[<hv1>@{<green>propagate_lit@}@ %a@ nf: %a@ clauses: (@[%a@])@])"
            pp l pp (snd (Reduce.compute_nf l)) (Utils.pp_list Clause.pp) cs);
      incr stat_num_propagations;
      Clause.push_new_l cs;
      ()

    (* add [t] to the list of literals that watch the constant [c] *)
    let watch_cst_ (t:t)(c:cst) : unit =
      assert (Ty.is_prop t.term_ty);
      Log.debugf 2
        (fun k->k "(@[<1>watch_cst@ %a@ %a@])" Typed_cst.pp c Term.pp t);
      Expand.expand_cst c;
      ()

    (* add [t] to the list of literals that watch this slice *)
    let watch_uty (t:t)(uty:ty_uninterpreted_slice) : unit =
      assert (Ty.is_prop t.term_ty);
      Log.debugf 2
        (fun k->k "(@[<1>watch_uty@ %a@ %a@])" pp_uty uty Term.pp t);
      Expand.expand_uty uty;
      ()

    let watch_dep (t:t) (d:term_dep) : unit = match d with
      | Dep_cst c -> watch_cst_ t c
      | Dep_uty uty -> watch_uty t uty

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
             in
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
          let cs =
            clause_guard_of_exp_ e
            |> Sequence.map
              (fun guard -> Lit.neg lit :: guard |> Clause.make)
          in
          Sequence.iter Clause.push_new cs
        | Lit_atom _ -> ()
        | Lit_assign(c, t) ->
          if Lit.sign lit then assert_choice c t
        | Lit_uty_empty uty ->
          let status = if Lit.sign lit then Uty_empty else Uty_nonempty in
          assert_uty uty status
      end

    (* is the dependency updated, i.e. decided by the SAT solver? *)
    let dep_updated (d:term_dep): bool = match d with
      | Dep_cst {cst_kind=Cst_undef (_, i, _); _} ->
        CCOpt.is_some i.cst_cur_case
      | Dep_cst _ -> assert false
      | Dep_uty uty ->
        CCOpt.is_some uty.uty_status

    (* for each term in [terms], update its watches, iff one of its dependencies
       is set *)
    let update_terms (terms:term Sequence.t): unit =
      Sequence.iter
        (fun t ->
           let _, nf = Reduce.get_nf t in
           if List.exists dep_updated nf.term_deps
           then Watched_lit.update_watches_of_term t)
        terms

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
        update_terms Top_goals.to_seq;
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
               let cst = lazy (
                 Typed_cst.make_defined id ty rhs
               ) in
               ID.Tbl.add decl_ty_ id cst)
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
        | Check_assign _
        | Check_empty_uty _
          -> assert false
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

  (* print all terms reachable from watched literals *)
  let pp_term_graph out () =
    Term.pp_dot out (Watched_lit.to_seq :> term Sequence.t)

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
       @])"
      !stat_num_cst_expanded
      !stat_num_uty_expanded
      !stat_num_clause_push
      !stat_num_clause_tautology
      (Watched_lit.size())
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

