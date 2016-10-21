
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
    mutable term_class: term Bag.t; (* terms in the same equiv class *)
    mutable term_parents: term Bag.t; (* parent terms of the whole equiv class *)
    mutable term_root: term; (* representative of congruence class *)
    mutable term_expl: (term * cc_explanation) option;
      (* the rooted forest for explanations *)
    mutable term_cases_set: term_cases_set;
      (* abstract set of values this term can take *)
    mutable term_nf: (term_nf * term) option;
    (* normal form, if any? [Some (nf,t)] means that [repr = nf]
       because [repr = t], for explanation purpose *)
  }

  (* term shallow structure *)
  and term_cell =
    | True
    | False
    | DB of db (* de bruijn indice *)
    | App_cst of cst * term IArray.t (* full, first-order application *)
    | App_ho of term * term list (* every other application *)
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
    | NF_cstor of data_cstor * term IArray.t
    | NF_bool of bool

  and term_cases_set =
    | TC_none
    | TC_cstors of
        (* set of possible constructors *)
        data_cstor ID.Map.t *
        cc_explanation list

  (* atomic explanation in the congruence closure *)
  and cc_explanation =
    | CC_reduction (* by pure reduction, tautologically equal *)
    | CC_lit of lit (* because of this literal *)
    | CC_congruence of term * term (* same shape *)
    | CC_injectivity of term * term (* arguments of those constructors *)
    | CC_reduce_nf of term (* reduce because this has a normal form *)
    | CC_reduce_eq of term * term (* reduce because those are equal *)

  (* boolean literal *)
  and lit = {
    lit_view: lit_view;
    lit_sign: bool;
  }

  and lit_view =
    | Lit_fresh of ID.t (* fresh literals *)
    | Lit_atom of term
    | Lit_expanded of term (* expanded? used for recursive calls mostly *)

  and cst = {
    cst_id: ID.t;
    cst_kind: cst_kind;
  }

  and cst_kind =
    | Cst_undef of ty_h (* simple undefined constant *)
    | Cst_cstor of data_cstor lazy_t
    | Cst_proj of ty_h * data_cstor lazy_t * int (* [cstor, argument position] *)
    | Cst_test of ty_h * data_cstor lazy_t (* test if [cstor] *)
    | Cst_defined of ty_h * term lazy_t * cst_defined_info

  (* what kind of constant is that? *)
  and cst_defined_info =
    | Cst_recursive
    | Cst_non_recursive

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
    ty_card: ty_card lazy_t;
  }

  and ty_card =
    | Finite
    | Infinite

  and ty_def =
    | Uninterpreted
    | Data of datatype (* set of constructors *)

  and datatype = {
    data_cstors: data_cstor ID.Map.t lazy_t;
  }

  (* TODO: in cstor, add:
     - for each selector, a special "magic" term for undefined, in
       case the selector is ill-applied (Collapse 2)  *)

  (* a constructor *)
  and data_cstor = {
    cstor_ty: ty_h;
    cstor_args: ty_h IArray.t; (* argument types *)
    cstor_proj: cst IArray.t lazy_t; (* projectors *)
    cstor_test: cst lazy_t; (* tester *)
    cstor_cst: cst; (* the cstor itself *)
    cstor_card: ty_card; (* cardinality of the constructor('s args) *)
  }

  and ty_cell =
    | Prop
    | Atomic of ID.t * ty_def
    | Arrow of ty_h * ty_h

  (** {2 Type Cardinality} *)
  module Ty_card : sig
    type t = ty_card

    val (+) : t -> t -> t
    val ( * ) : t -> t -> t
    val ( ^ ) : t -> t -> t
    val finite : t
    val infinite : t

    val sum : t list -> t
    val product : t list -> t

    val equal : t -> t -> bool
    val compare : t -> t -> int
    val pp : t CCFormat.printer
  end = struct
    type t = ty_card

    let (+) a b = match a, b with Finite, Finite -> Finite | _ -> Infinite
    let ( * ) a b = match a, b with Finite, Finite -> Finite | _ -> Infinite
    let ( ^ ) a b = match a, b with Finite, Finite -> Finite | _ -> Infinite
    let finite = Finite
    let infinite = Infinite

    let sum = List.fold_left (+) Finite
    let product = List.fold_left ( * ) Finite

    let equal = (=)
    let compare = Pervasives.compare
    let pp out = function
      | Finite -> CCFormat.string out "finite"
      | Infinite -> CCFormat.string out "infinite"
  end

  module Ty : sig
    type t = ty_h
    val view : t -> ty_cell
    val equal : t -> t -> bool
    val compare : t -> t -> int
    val hash : t -> int

    val prop : t
    val atomic : ID.t -> ty_def -> card:ty_card lazy_t -> t
    val arrow : t -> t -> t
    val arrow_l : t list -> t -> t

    val is_prop : t -> bool
    val is_data : t -> bool
    val is_uninterpreted : t -> bool
    val is_arrow : t -> bool
    val unfold : t -> t list * t
    val unfold_n : t -> int * t

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
    let make_ : ty_cell -> card:ty_card lazy_t -> t =
      let tbl : t Tbl_cell.t = Tbl_cell.create 128 in
      let n = ref 0 in
      fun c ~card ->
        try Tbl_cell.find tbl c
        with Not_found ->
          let ty_id = !n in
          incr n;
          let ty = {ty_id; ty_cell=c; ty_card=card; } in
          Tbl_cell.add tbl c ty;
          ty

    let prop = make_ Prop ~card:(Lazy.from_val Finite)

    let atomic id def ~card = make_ (Atomic (id,def)) ~card

    let arrow a b =
      let card = lazy (Ty_card.(Lazy.force b.ty_card ^ Lazy.force a.ty_card)) in
      make_ (Arrow (a,b)) ~card

    let arrow_l = List.fold_right arrow

    let is_prop t =
      match t.ty_cell with | Prop -> true | _ -> false

    let is_data t =
      match t.ty_cell with | Atomic (_, Data _) -> true | _ -> false

    let is_uninterpreted t =
      match t.ty_cell with | Atomic (_, Uninterpreted) -> true | _ -> false

    let is_arrow t =
      match t.ty_cell with | Arrow _ -> true | _ -> false

    let unfold ty : t list * t =
      let rec aux acc ty = match ty.ty_cell with
        | Arrow (a,b) -> aux (a::acc) b
        | _ -> List.rev acc, ty
      in
      aux [] ty

    let unfold_n ty : int * t =
      let rec aux n ty = match ty.ty_cell with
        | Arrow (_,b) -> aux (n+1) b
        | _ -> n, ty
      in
      aux 0 ty

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

  module Cst : sig
    type t = cst
    val id : t -> ID.t
    val ty : t -> Ty.t
    val make_cstor : ID.t -> Ty.t -> data_cstor lazy_t -> t
    val make_proj : ID.t -> Ty.t -> data_cstor lazy_t -> int -> t
    val make_tester : ID.t -> Ty.t -> data_cstor lazy_t -> t
    val make_defined : ID.t -> Ty.t -> term lazy_t -> cst_defined_info -> t
    val make_undef : ID.t -> Ty.t -> t
    val arity : t -> int (* number of args *)
    val equal : t -> t -> bool
    val compare : t -> t -> int
    val hash : t -> int
    val as_undefined : t -> (t * Ty.t) option
    val as_undefined_exn : t -> t * Ty.t
    val is_finite_cstor : t -> bool
    val pp : t CCFormat.printer
    module Map : CCMap.S with type key = t
    module Tbl : CCHashtbl.S with type key = t
  end = struct
    type t = cst

    let id t = t.cst_id

    let ty_of_kind = function
      | Cst_defined (ty, _, _)
      | Cst_undef ty
      | Cst_test (ty, _)
      | Cst_proj (ty, _, _) -> ty
      | Cst_cstor (lazy cstor) -> cstor.cstor_ty

    let ty t = ty_of_kind t.cst_kind

    let arity t = fst (Ty.unfold_n (ty t))

    let make cst_id cst_kind = {cst_id; cst_kind}
    let make_cstor id ty cstor =
      let _, ret = Ty.unfold ty in
      assert (Ty.is_data ret);
      make id (Cst_cstor cstor)
    let make_proj id ty cstor i =
      make id (Cst_proj (ty, cstor, i))
    let make_tester id ty cstor =
      make id (Cst_test (ty, cstor))

    let make_defined id ty t info = make id (Cst_defined (ty, t, info))

    let make_undef id ty = make id (Cst_undef ty)

    let as_undefined (c:t) = match c.cst_kind with
      | Cst_undef ty -> Some (c,ty)
      | Cst_defined _ | Cst_cstor _ | Cst_proj _ | Cst_test _
        -> None

    let as_undefined_exn (c:t) = match as_undefined c with
      | Some tup -> tup
      | None -> assert false

    let is_finite_cstor c = match c.cst_kind with
      | Cst_cstor (lazy {cstor_card=Finite; _}) -> true
      | _ -> false

    let equal a b = ID.equal a.cst_id b.cst_id
    let compare a b = ID.compare a.cst_id b.cst_id
    let hash t = ID.hash t.cst_id
    let pp out a = ID.pp out a.cst_id

    module Map = CCMap.Make(struct
        type t = cst
        let compare = compare
      end)
    module Tbl = CCHashtbl.Make(struct
        type t = cst
        let equal = equal
        let hash = hash
      end)
  end

  let cmp_lit a b =
    let c = CCOrd.bool_ a.lit_sign b.lit_sign in
    if c<>0 then c
    else
      let int_of_cell_ = function
        | Lit_fresh _ -> 0
        | Lit_atom _ -> 1
        | Lit_expanded _ -> 2
      in
      match a.lit_view, b.lit_view with
        | Lit_fresh i1, Lit_fresh i2 -> ID.compare i1 i2
        | Lit_atom t1, Lit_atom t2 -> term_cmp_ t1 t2
        | Lit_expanded t1, Lit_expanded t2 -> term_cmp_ t1 t2
        | Lit_fresh _, _
        | Lit_atom _, _
        | Lit_expanded _, _
          -> CCOrd.int_ (int_of_cell_ a.lit_view) (int_of_cell_ b.lit_view)

  let cmp_nf a b =
    let toint = function NF_bool _ -> 0 | NF_cstor _ -> 1 in
    match a, b with
      | NF_bool b1, NF_bool b2 -> CCOrd.bool_ b1 b2
      | NF_cstor (c1,args1), NF_cstor (c2,args2) ->
        CCOrd.(Cst.compare c1.cstor_cst c2.cstor_cst
          <?> (IArray.compare term_cmp_, args1, args2))
      | NF_bool _, _
      | NF_cstor _, _ -> CCOrd.int_ (toint a)(toint b)

  let hash_lit a =
    let sign = a.lit_sign in
    match a.lit_view with
      | Lit_fresh i -> Hash.combine3 1 (Hash.bool sign) (ID.hash i)
      | Lit_atom t -> Hash.combine3 2 (Hash.bool sign) (term_hash_ t)
      | Lit_expanded t ->
        Hash.combine3 3 (Hash.bool sign) (term_hash_ t)

  let cmp_cc_expl a b =
    let toint = function
      | CC_congruence _ -> 0 | CC_lit _ -> 1
      | CC_reduction -> 2 | CC_injectivity _ -> 3
      | CC_reduce_nf _ -> 4 | CC_reduce_eq _ -> 5
    in
    match a, b with
      | CC_congruence (t1,t2), CC_congruence (u1,u2) ->
        CCOrd.(term_cmp_ t1 u1 <?> (term_cmp_, t2, u2))
      | CC_reduction, CC_reduction -> 0
      | CC_lit l1, CC_lit l2 -> cmp_lit l1 l2
      | CC_injectivity (t1,t2), CC_injectivity (u1,u2) ->
        CCOrd.(term_cmp_ t1 u1 <?> (term_cmp_, t2, u2))
      | CC_reduce_nf t1, CC_reduce_nf t2 ->
        term_cmp_ t1 t2
      | CC_reduce_eq (t1, u1), CC_reduce_eq (t2,u2) ->
        CCOrd.(term_cmp_ t1 t2 <?> (term_cmp_, u1, u2))
      | CC_congruence _, _ | CC_lit _, _ | CC_reduction, _
      | CC_injectivity _, _ | CC_reduce_nf _, _ | CC_reduce_eq _, _
        -> CCOrd.int_ (toint a)(toint b)

  module CC_expl_set = CCSet.Make(struct
      type t = cc_explanation
      let compare = cmp_cc_expl
    end)

  module Backtrack : sig
    val dummy_level : level
    val cur_level : unit -> level
    val push_level : unit -> unit
    val backtrack : level -> unit
    val backtrack_to_level_0 : unit -> unit
    val at_level_0 : unit -> bool
    val not_at_level_0 : unit -> bool
    val push_undo : (unit -> unit) -> unit
  end = struct
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

    let push_undo f = CCVector.push st_ f

    (* Are we current at level 0, or in the search tree?
       This helps because some operations are much cheaper to do at level 0 *)
    let at_level_0_ : bool ref = ref true
    let at_level_0 () = !at_level_0_
    let not_at_level_0 () = not !at_level_0_

    let level_0_ : level option ref = ref None

    let push_level () : unit =
      let l = cur_level() in
      Log.debugf 2 (fun k->k "@{<Yellow>** now at level %d (push)@}" l);
      if !at_level_0_ then (
        assert (!level_0_ = None);
        Log.debug 5 "not at level 0 anymore";
        push_undo
          (fun () ->
             Log.debug 5 "back to level 0";
             at_level_0_ := true;
             level_0_ := None);
        at_level_0_ := false;
        level_0_ := Some l;
      );
      ()

    let backtrack_to_level_0 () = match !level_0_ with
      | None -> ()
      | Some l -> backtrack l
  end

  (* TODO: normalization of {!term_cell} for use in signatures? *)

  module Term_cell : sig
    type t = term_cell

    val equal : t -> t -> bool
    val hash : t -> int

    val true_ : t
    val false_ : t
    val db : DB.t -> t
    val const : cst -> t
    val app_cst : cst -> term IArray.t -> t
    val app : term -> term list -> t
    val cstor_test : data_cstor -> term -> t
    val cstor_proj : data_cstor -> int -> term -> t
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
      | App_cst (f,l) ->
        Hash.combine3 4 (Cst.hash f) (Hash.iarray sub_hash l)
      | App_ho (f,l) ->
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
      | App_cst (f1, a1), App_cst (f2, a2) ->
        Cst.equal f1 f2 && IArray.equal (==) a1 a2
      | App_ho (f1, l1), App_ho (f2, l2) ->
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
      | App_cst _, _
      | App_ho _, _
      | Fun _, _
      | If _, _
      | Case _, _
      | Builtin _, _
      | Mu _, _
        -> false

    let true_ = True
    let false_ = False
    let db d = DB d

    let app f l = match l with
      | [] -> f.term_cell
      | _ ->
        begin match f.term_cell with
          | App_cst (f, a) when IArray.length a + List.length l = Cst.arity f ->
            (* [f] becomes fully applied *)
            App_cst (f, IArray.append a (IArray.of_list l))
          | App_ho (f1, l1) ->
            let l' = l1 @ l in
            App_ho (f1, l')
          | _ -> App_ho (f,l)
        end

    let app_cst f a = App_cst (f, a)
    let const c = App_cst (c, IArray.empty)

    let fun_ ty body = Fun (ty, body)
    let mu t = Mu t
    let case u m = Case (u,m)
    let if_ a b c =
      assert (Ty.equal b.term_ty c.term_ty);
      If (a,b,c)

    let cstor_test cstor t =
      app_cst (Lazy.force cstor.cstor_test) (IArray.singleton t)

    let cstor_proj cstor i t =
      let p = IArray.get (Lazy.force cstor.cstor_proj) i in
      app_cst p (IArray.singleton t)

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
      | App_ho (f, l) -> app_ty_ f.term_ty l
      | App_cst (f, a) ->
        let n_args, ret = Cst.ty f |> Ty.unfold_n in
        if n_args = IArray.length a
        then ret (* fully applied *)
        else (
          assert (IArray.length a < n_args);
          app_ty_ (Cst.ty f) (IArray.to_list a)
        )
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
    (** Term in congruence closure? *)

    module Field_expanded : Term_bits.FIELD with type value = bool
    (** Term is expanded? *)

    module Field_has_expansion_lit : Term_bits.FIELD with type value = bool
    (** Upon expansion, does this term have a special literal [Lit_expanded t]
        that should be asserted? *)

    module Field_is_lit : Term_bits.FIELD with type value = bool
    (** Is this term a boolean literal? *)

    module Field_is_split : Term_bits.FIELD with type value = bool
    (** Did we perform case split (Split 1) on this term?
        This is only relevant for terms whose type is a datatype. *)

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
    val app_cst : cst -> t IArray.t -> t
    val fun_ : Ty.t -> t -> t
    val fun_l : Ty.t list -> t -> t
    val mu : t -> t
    val if_: t -> t -> t -> t
    val case : t -> t ID.Map.t -> t
    val builtin : builtin -> t
    val and_ : t -> t -> t
    val or_ : t -> t -> t
    val not_ : t -> t
    val imply : t -> t -> t
    val eq : t -> t -> t
    val neq : t -> t -> t
    val and_eager : t -> t -> t (* evaluate left argument first *)

    val cstor_test : data_cstor -> term -> t
    val cstor_proj : data_cstor -> int -> term -> t

    val and_l : t list -> t
    val or_l : t list -> t

    val abs : t -> t * bool

    val map_builtin : (t -> t) -> builtin -> builtin
    val builtin_to_seq : builtin -> t Sequence.t

    val to_seq : t -> t Sequence.t

    val all_terms : t Sequence.t

    val pp : t CCFormat.printer

    (** {6 Views} *)

    val is_const : t -> bool

    (* return [Some] iff the term is an undefined constant *)
    val as_cst_undef : t -> (cst * Ty.t) option

    val as_cstor_app : t -> (cst * data_cstor * t IArray.t) option

    (** environment for evaluation: not-yet-evaluated terms *)
    type eval_env = t DB_env.t

    val eval_db : eval_env -> t -> t
    (** Evaluate the term in the given De Bruijn environment, and simplify it. *)

    (* typical view for unification/equality *)
    type unif_form =
      | Unif_cst of cst * Ty.t
      | Unif_cstor of cst * data_cstor * term IArray.t
      | Unif_none

    val as_unif : t -> unif_form

    (** {6 Containers} *)

    module Tbl : CCHashtbl.S with type key = t
    module Map : CCMap.S with type key = t
  end = struct
    type t = term

    module Field_in_cc = (val (Term_bits.bool ~name:"in_cc" ()))
    module Field_expanded = (val (Term_bits.bool ~name:"expanded" ()))
    module Field_has_expansion_lit = (val (Term_bits.bool ~name:"has_expansion_lit" ()))
    module Field_is_lit = (val (Term_bits.bool ~name:"is_lit" ()))
    module Field_is_split = (val (Term_bits.bool ~name:"is_split" ()))
    let () = Term_bits.freeze()

    let id t = t.term_id
    let ty t = t.term_ty

    let equal = term_equal_
    let hash = term_hash_
    let compare a b = CCOrd.int_ a.term_id b.term_id

    let (make, get, all_terms
        : (term_cell -> term) * (term_cell -> term option) * term Sequence.t) =
      let tbl : term Term_cell.Tbl.t = Term_cell.Tbl.create 2048 in
      let n = ref 0 in
      let get c =
        Term_cell.Tbl.get tbl c
      and make c =
        try Term_cell.Tbl.find tbl c
        with Not_found ->
          let term_ty = Term_cell.ty c in
          (* set of possibilities *)
          let term_cases_set = match Ty.view term_ty with
            | Atomic (_, Data data) ->
              TC_cstors (Lazy.force data.data_cstors, [])
            | _ -> TC_none
          in
          let rec t = {
            term_id= !n;
            term_ty;
            term_class=Bag.empty;
            term_parents=Bag.empty;
            term_bits=Term_bits.empty;
            term_root=t;
            term_expl=None;
            term_cell=c;
            term_cases_set;
            term_nf=None;
          } in
          incr n;
          (* set [class(t) = {t}] *)
          t.term_class <- Bag.return t;
          Term_cell.Tbl.add tbl c t;
          t
      and all_terms yield =
        Term_cell.Tbl.values tbl yield
      in
      make, get, all_terms

    (* boolean are special: we know already what normal form they have *)
    let mk_bool_ b =
      let t = make (if b then True else False) in
      t.term_nf <- Some (NF_bool b, t);
      t

    let true_ = mk_bool_ true
    let false_ = mk_bool_ false

    let db d = make (DB d)

    let app f l = match l with
      | [] -> f
      | _ -> make (Term_cell.app f l)

    let app_cst f a =
      let cell = Term_cell.app_cst f a in
      let t = make cell in
      (* update some fields *)
      if t.term_cell == cell && IArray.length a = Cst.arity f then (
        begin match f.cst_kind with
          | Cst_cstor (lazy cstor) when t.term_cell == cell ->
            (* by definition, a constructor term has itself as a normal form *)
            assert (t.term_nf = None);
            t.term_nf <- Some (NF_cstor (cstor, a), t);
            assert (t.term_cases_set <> TC_none);
            t.term_cases_set <- TC_cstors (ID.Map.singleton f.cst_id cstor, []);
          | _ -> ()
        end;
      );
      t

    let const c = app_cst c IArray.empty

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
    let builtin b = make (Term_cell.builtin b)

    (* "eager" and, evaluating [a] first *)
    let and_eager a b = if_ a b false_

    let cstor_test cstor t = make (Term_cell.cstor_test cstor t)
    let cstor_proj cstor i t = make (Term_cell.cstor_proj cstor i t)

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
      | App_cst (_, a) -> IArray.is_empty a
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
          | DB _ | True | False -> ()
          | App_cst (_,a) -> IArray.iter aux a
          | App_ho (f,l) -> aux f; List.iter aux l
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
    let as_cst_undef (t:term): (cst * Ty.t) option =
      match t.term_cell with
        | App_cst (c, a) when IArray.is_empty a ->
          Cst.as_undefined c
        | _ -> None

    (* return [Some (cstor,ty,args)] if the term is a constructor
       applied to some arguments *)
    let as_cstor_app (t:term): (cst * data_cstor * term IArray.t) option =
      match t.term_cell with
        | App_cst ({cst_kind=Cst_cstor (lazy cstor); _} as c, a) ->
          Some (c,cstor,a)
        | _ -> None

    (* typical view for unification/equality *)
    type unif_form =
      | Unif_cst of cst * Ty.t
      | Unif_cstor of cst * data_cstor * term IArray.t
      | Unif_none

    let as_unif (t:term): unif_form = match t.term_cell with
      | App_cst ({cst_kind=Cst_undef ty; _} as c, a) when IArray.is_empty a ->
        Unif_cst (c,ty)
      | App_cst ({cst_kind=Cst_cstor (lazy cstor); _} as c, a) ->
        Unif_cstor (c,cstor,a)
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
        | App_cst (c, a) when IArray.is_empty a ->
          pp_id out (Cst.id c)
        | App_cst (f,l) ->
          fpf out "(@[<1>%a@ %a@])" pp_id (Cst.id f) (Utils.pp_iarray pp) l
        | App_ho (f,l) ->
          fpf out "(@[<1>@@ %a@ %a@])" pp f (Utils.pp_list pp) l
        | Fun (ty,f) ->
          fpf out "(@[fun %a@ %a@])" Ty.pp ty pp f
        | Mu sub -> fpf out "(@[mu@ %a@])" pp sub
        | If (a, b, c) ->
          fpf out "(@[if %a@ %a@ %a@])" pp a pp b pp c
        | Case (t,m) ->
          let pp_bind out (id,rhs) =
            fpf out "(@[<1>case %a@ %a@])" pp_id id pp rhs
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
      and pp_id =
        if ids then ID.pp else ID.pp_name
      in
      pp out t

    let pp = pp_top ~ids:false

    type eval_env = term DB_env.t

    let eval_db (env:eval_env) (t:term) : term =
      let rec aux env t : term = match t.term_cell with
        | DB d ->
          begin match DB_env.get d env with
            | None -> t
            | Some t' -> t'
          end
        | True
        | False -> t
        | App_cst (_, a) when IArray.is_empty a -> t
        | App_cst (f, a) ->
          let a' = IArray.map (aux env) a in
          let a0 = IArray.get a' 0 in
          begin match f.cst_kind, a0.term_cell with
            | Cst_proj (_,lazy cstor,i),
              App_cst ({cst_kind=Cst_cstor (lazy cstor'); _}, a0_args)
              when Cst.equal cstor.cstor_cst cstor'.cstor_cst ->
              (* reduction: [proj-C-i (C t1...tn) --> ti] *)
              assert (IArray.length a0_args > i);
              aux env (IArray.get a0_args i)
            | Cst_test (_,lazy cstor),
              App_cst ({cst_kind=Cst_cstor (lazy cstor'); _}, _) ->
              (* reduction: [is-C (D t1...tn) -> C==D] *)
              if Cst.equal cstor.cstor_cst cstor'.cstor_cst
              then true_ else false_
            | _ ->
                 (* just replace *)
              if IArray.for_all2 (==) a a' then t else app_cst f a'
          end
        | Fun (ty, body) ->
          let body' = aux (DB_env.push_none env) body in
          if body==body' then t else fun_ ty body'
        | Mu body ->
          let body' = aux (DB_env.push_none env) body in
          if body==body' then t else mu body'
        | Case (u, m) ->
          let u' = aux env u in
          begin match u'.term_cell with
            | App_cst ({cst_kind=Cst_cstor (lazy cstor); _}, _) ->
              let cstor_id = cstor.cstor_cst.cst_id in
              begin match ID.Map.get cstor_id m with
                | None ->
                  errorf "could not find cstor %a@ in %a" ID.pp cstor_id pp t
                | Some rhs ->
                  aux env rhs
              end
            | _ ->
              let m' = ID.Map.map (aux env) m in
              case u' m'
          end
        | If (a,b,c) ->
          let a' = aux env a in
          (* normalize on the fly *)
          begin match a'.term_cell with
            | True -> aux env b
            | False -> aux env c
            | _ ->
              let b' = aux env b in
              let c' = aux env c in
              if a==a' && b==b' && c==c' then t else if_ a' b' c'
          end
        | App_ho (_,[]) -> assert false
        | App_ho (f, l) ->
          let f' = aux env f in
          let l' = aux_l env l in
          beta_reduce DB_env.empty f' l'
        | Builtin b -> builtin (map_builtin (aux env) b)
      and aux_l env l =
        List.map (aux env) l
      and beta_reduce env f l = match f.term_cell, l with
        | Fun (ty_arg, body), arg :: tail ->
          assert (Ty.equal ty_arg arg.term_ty);
          (* beta-reduction *)
          let new_env = DB_env.push arg env in
          beta_reduce new_env body tail
        | _ ->
          let f' = aux env f in
          if equal f f' then (
            app f' l (* done *)
          ) else (
            (* try to reduce again *)
            beta_reduce DB_env.empty f' l
          )
      in
      aux env t
  end

  let pp_term_nf out (nf:term_nf) = match nf with
    | NF_bool b -> Format.fprintf out "%B" b
    | NF_cstor (cstor, args) ->
      Format.fprintf out "(@[<hv2>%a @%a@])"
        Cst.pp cstor.cstor_cst (Utils.pp_iarray Term.pp) args

  let pp_lit out l =
    let pp_lit_view out = function
      | Lit_fresh i -> Format.fprintf out "#%a" ID.pp i
      | Lit_atom t -> Term.pp out t
      | Lit_expanded t -> Format.fprintf out "(@[<1>expanded@ %a@])" Term.pp t
    in
    if l.lit_sign then pp_lit_view out l.lit_view
    else Format.fprintf out "(@[@<1>¬@ %a@])" pp_lit_view l.lit_view

  let pp_cc_explanation out (e:cc_explanation) = match e with
    | CC_reduction -> CCFormat.string out "reduction"
    | CC_lit lit -> pp_lit out lit
    | CC_congruence (a,b) ->
      Format.fprintf out "(@[<hv1>congruence@ %a@ %a@])" Term.pp a Term.pp b
    | CC_injectivity (a,b) ->
      Format.fprintf out "(@[<hv1>injectivity@ %a@ %a@])" Term.pp a Term.pp b
    | CC_reduce_nf t ->
      Format.fprintf out "(@[<hv1>reduce_nf@ %a@])" Term.pp t
    | CC_reduce_eq (t, u) ->
      Format.fprintf out "(@[<hv1>reduce_eq@ %a@ %a@])" Term.pp t Term.pp u

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
    val cstor_test : data_cstor -> term -> t
    val eq : term -> term -> t
    val neq : term -> term -> t
    val expanded : term -> t
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
      t.term_bits <- Term.Field_is_lit.set true t.term_bits;
      let sign = if not sign' then not sign else sign in
      make ~sign (Lit_atom t)

    let eq a b = atom ~sign:true (Term.eq a b)
    let neq a b = atom ~sign:false (Term.eq a b)
    let expanded t = make ~sign:true (Lit_expanded t)

    let cstor_test cstor t = atom ~sign:true (Term.cstor_test cstor t)

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
        Format.fprintf out "[@[<hv>%a@]]/%d"
          (Utils.pp_list ~sep:"; " Lit.pp) c.lits c.id

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
        (* FIXME: maybe a special method to add such clauses, e.g. for "IF"
        | [a;b] when Lit.equal (Lit.neg a) b -> () (* trivial *)
           *)
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

  (** {2 Term Expansion}

      Some terms reduce to other terms (e.g., defined functions and constants);
      some other terms are boolean connectives whose semantics should be
      handled by the SAT solver.

      Expansion is the process of relating the term and its semantics. It
      is idempotent and works by adding equations to the congruence closure,
      and/or clauses to the  SAT solver *)

  (** Expansion requires to perform some actions to enforce the term's semantics *)
  module type EXPAND_ACTION = sig
    val add_eqn : term -> term -> unit
    val add_clause : Clause.t -> unit
    val add_clause_l : Clause.t list -> unit
    val delay_expansion : term -> unit
    (** Delay the expansion of this term to later *)
  end

  module Expand(A : EXPAND_ACTION) : sig
    type mode =
      | Force (* force expansion of the root term. *)
      | Safe (* do not expand potentially infinite terms *)

    val expand_term : mode:mode -> term -> unit
    (** Expand the term by making a case distinction, a boolean CNF,
        or nothing, depending on its type. Idempotent.
        Some terms, such as calls to recursive functions, will not be expanded
          by this function if [mode = Safe].
        precondition: [CC.in_cc t] *)
  end = struct
    type mode =
      | Force (* force expansion of the root term. *)
      | Safe (* do not expand potentially infinite terms *)

    type guard = Lit.Set.t
    (** Guards for a sub-term: the path conditions needed to reach
        this term *)

    let rec expand_term_rec ~mode ~(guard:guard) (t:term): unit =
      if not (Term.Field_expanded.get t.term_bits) then (
        let expanded = expand_term_real ~mode ~guard t in
        if expanded then (
          t.term_bits <- Term.Field_expanded.set true t.term_bits;
        ) else (
          assert (mode <> Force);
          (* delay expansion for now *)
          A.delay_expansion t;
          (* make a clause that forces expansion of the term if guard is
             satisfied *)
          let c =
            let g = Lit.Set.to_list guard |> List.map Lit.neg in
            Clause.make (Lit.expanded t :: g)
          in
          Log.debugf 5
            (fun k->k "(@[delay_expand %a@ guard: %a@])" Term.pp t Clause.pp c);
          A.add_clause c
        )
      )

    (* unconditional expansion, [mode] notwithstanding *)
    and expand_term_real ~mode ~guard t : bool =
      (* first, ensure booleans are split on properly *)
      if Ty.is_prop t.term_ty then (
        A.add_clause (Clause.make [Lit.atom t; Lit.atom ~sign:false t]);
      );
      begin match t.term_cell with
        | True | False | DB _ -> true
        | App_cst ({cst_kind=Cst_defined (ty, lazy rhs, kind); _}, a) ->
          assert (IArray.length a = fst (Ty.unfold_n ty));
          begin match mode, kind with
            | _ when IArray.is_empty a ->
              (* t := its definition *)
              A.add_eqn t rhs;
              true
            | _, Cst_non_recursive
            | Force, _ ->
              let body =
                Term.eval_db DB_env.empty (Term.app rhs (IArray.to_list a))
              in
              expand_term_safe ~guard body;
              (* [t = body] is now a reduction axiom *)
              A.add_eqn t body;
              true
            | Safe, Cst_recursive ->
              (* no expansion allowed here *)
              false
          end
        | App_cst _
        | App_ho _
        | Fun _ -> true
        | If (a,b,c) ->
          let g_a = Lit.atom a in
          (* force SAT solver to choose value of [g_a] *)
          A.add_clause ([g_a; Lit.neg g_a] |> Clause.make);
          (* expand subterms, with guard [a] or [not a] for the branches *)
          expand_term_safe ~guard a;
          expand_term_safe ~guard:(Lit.Set.add g_a guard) b;
          expand_term_safe ~guard:(Lit.Set.add (Lit.neg g_a) guard) c;
          true
        | Case (t, m) ->
          expand_term_safe ~guard t;
          (* now expand each branch of [m], under cstor [c],
             with the guard [is-c t] *)
          let data = match Ty.view t.term_ty with
            | Atomic (_, Data data) -> data
            | _ -> assert false
          in
          ID.Map.iter
            (fun c rhs ->
               let cstor =
                 try ID.Map.find c (Lazy.force data.data_cstors)
                 with Not_found -> assert false
               in
               let g_c = Lit.cstor_test cstor t in
               expand_term_safe ~guard:(Lit.Set.add g_c guard) rhs)
            m;
          true
        | Mu _ -> assert false (* TODO: [mu x. t[x] = t[x := mu x. t[x]]] *)
        | Builtin b ->
          let cs = match b with
            | B_not _ -> [] (* will just evaluate *)
            | B_and (a,b) ->
              expand_term_safe ~guard a;
              expand_term_safe ~guard b;
              [ [ Lit.atom ~sign:false a; Lit.atom ~sign:false b; Lit.atom t ];
                [ Lit.atom ~sign:false t; Lit.atom a];
                [ Lit.atom ~sign:false t; Lit.atom b];
              ] |> List.map Clause.make
            | B_or (a,b) ->
              expand_term_safe ~guard a;
              expand_term_safe ~guard b;
              [ [ Lit.atom a; Lit.atom b; Lit.atom ~sign:false t ];
                [ Lit.atom t; Lit.atom ~sign:false a];
                [ Lit.atom t; Lit.atom ~sign:false b];
              ] |> List.map Clause.make
            | B_imply _ -> assert false (* TODO *)
            | B_eq (a,b) ->
              expand_term_safe ~guard a;
              expand_term_safe ~guard b;
              if Ty.is_prop a.term_ty then (
                (* equivalence *)
                [ [ Lit.atom ~sign:false a; Lit.atom ~sign:false b; Lit.atom t ];
                  [ Lit.atom a; Lit.atom b; Lit.atom t ];
                  [ Lit.atom ~sign:false t; Lit.atom ~sign:false b; Lit.atom a];
                  [ Lit.atom ~sign:false t; Lit.atom ~sign:false a; Lit.atom b];
                ] |> List.map Clause.make
              ) else [] (* congruence closure's job *)
          in
          A.add_clause_l cs;
          true
      end

    and expand_term_safe ~guard t = expand_term_rec ~mode:Safe ~guard t

    (* expand term, if not already expanded *)
    let expand_term ~mode (t:term): unit =
      expand_term_rec ~mode ~guard:Lit.Set.empty t
  end

  (** {2 Set of Terms to Expand}

      Some terms are not expanded immediately (to ensure termination), but will
      have to be at some point. We track the set of such terms so we
      can expand them in a fair order. *)
  module Terms_to_expand : sig
    type t = private {
      term: term; (* the term (e.g. a function call) *)
      lit: Lit.t; (* the corresponding "expanded" lit *)
      timestamp: int; (* monotonically increasing ID *)
    }

    val to_seq : t Sequence.t
    (** All current terms to expand *)

    val add : term -> unit
    (** Add the following non-expanded term, to be processed.
        precondition: [not (Term.is_expanded t)] *)

    val find : term -> t option
    (** Find blocked term, if any *)

    val mem : term -> bool
    (** Is the term among the set of all terms to expand *)

    val remove : term -> unit
    (** This term has been expanded, remove it
        precondition: [Term.is_expanded t && mem t] *)

    val is_empty : unit -> bool
    (** Is there any work to do? *)
  end = struct
    type t = {
      term: term; (* the term (e.g. a function call) *)
      lit: Lit.t; (* the corresponding "expanded" lit *)
      timestamp: int;
    }

    let time : int ref = ref 0
    let all : t Term.Tbl.t = Term.Tbl.create 256

    let is_empty () = Term.Tbl.length all = 0

    let to_seq k = Term.Tbl.values all k

    let add t =
      assert (not (Term.Field_expanded.get t.term_bits));
      if not (Term.Tbl.mem all t) then (
        let entry = {
          term=t;
          lit=Lit.expanded t;
          timestamp= !time;
        } in
        incr time;
        Log.debugf 3
          (fun k->k "(@[add_to_expand@ %a@ time: %d@])" Term.pp t entry.timestamp);
        Term.Tbl.add all t entry;
      )

    let mem t = Term.Tbl.mem all t

    let find t = Term.Tbl.get all t

    let remove t =
      assert (Term.Field_expanded.get t.term_bits);
      Term.Tbl.remove all t
  end

  (** {2 Theories} *)

  module type THEORY_ACTION = sig
    type repr = private term

    val equal_repr : repr -> repr -> bool

    val find : term -> repr

    val all_classes : repr Sequence.t
    (** Caution, expensive. Traverse every congruence class *)

    val add_eqn : term -> term -> cc_explanation -> unit
    (** Assert [t = u] because [e] *)

    val propagate : lit -> cc_explanation list -> unit
    (** Propagate boolean clause. It must be a theory lemma, that is,
        a T-tautology *)

    val split : lit list -> cc_explanation list -> unit
    (** [split lits expl] forces the SAT solver to pick one of [lits],
        assuming [expl]. That is, [expl => lits] must be a tautology *)

    val unsat : cc_explanation list -> unit
    (** Signal a T-inconsistency using the given tautology that
        is currently violated *)
  end

  (* TODO: move "expand" to THEORY *)

  module type THEORY = sig
    val merge_nf : term -> term -> term_nf -> term_nf -> bool
    (** [merge_nf ra rb nf_a nf_b] is called when [ra, rb]
        are merged and [ra.nf = nf_a, rb.nf = nf_b].
        This function merges the two normal forms and checks if they are
        compatible, returning [true] if it is the case. *)

    val set_nf : term -> term_nf -> cc_explanation -> unit
    (** [set_nf t nf e] is called when a term [t] acquires the normal form [nf]
        because of explanation [e]. The theory can propagate literals,
        equations, etc. *)

    val is_evaluable : term -> bool
    (** Is the term (potentially) evaluable in the theory? *)

    val eval : term -> unit
    (** Evaluate given term *)

    val final_check: unit -> unit
    (** Check satisfiability of the whole theory, including the expensive
        tests. This {b MUST} call {!THEORY_ACTION.unsat} if the current model
        is not T-satisfiable. *)
  end

  type theory = (module THEORY)

  (** {2 Theory of booleans}

      Evaluation of boolean constructs, etc. *)

  module Bool(A : THEORY_ACTION) : THEORY = struct
    let merge_nf _ _ nf_a nf_b: bool = match nf_a, nf_b with
      | NF_bool v_a, NF_bool v_b -> v_a = v_b
      | _ -> true

    let set_nf t nf e: unit = match nf, t.term_cell with
      | NF_bool sign, Builtin (B_eq (a,b)) ->
        if sign then (
          A.add_eqn a b e;
        )
      | _ -> ()

    let is_evaluable t = match t.term_cell with
      | Builtin (B_not _) | If _ -> true
      | _ -> false

    let eval t = match t.term_cell with
      | If (a, b, c) ->
        let ra = (A.find a:>term) in
        begin match ra.term_nf with
          | Some (NF_bool true, _) ->
            A.add_eqn t b (CC_reduce_nf a)
          | Some (NF_bool false, _) ->
            A.add_eqn t c (CC_reduce_nf a)
          | Some (NF_cstor _, _) -> assert false
          | None -> ()
        end
      | Builtin (B_eq (a,b)) ->
        (* check if [find a = find b] *)
        let ra = A.find a in
        let rb = A.find b in
        if A.equal_repr ra rb then (
          A.add_eqn t Term.true_ (CC_reduce_eq (a, b))
        )
      | Builtin (B_not a) ->
        (* check if [a == true/false] *)
        let ra = (A.find a:>term) in
        begin match ra.term_nf with
          | Some (NF_bool true, _) ->
            A.add_eqn t Term.false_ (CC_reduce_nf a)
          | Some (NF_bool false, _) ->
            A.add_eqn t Term.true_ (CC_reduce_nf a)
          | Some _ -> assert false
          | None -> ()
        end
      | _ -> ()

    let final_check () = ()
  end

  (** {2 Theory of Datatypes} *)

  module Datatype(A : THEORY_ACTION) : THEORY = struct
    (* merge equiv classes:
       - injectivity rule on normal forms *)
    let merge_nf ra rb nf_a nf_b: bool =
      begin match nf_a, nf_b with
        | NF_cstor (c1, args1), NF_cstor (c2, args2) ->
          if Cst.equal c1.cstor_cst c2.cstor_cst then (
            (* unify arguments recursively, by injectivity *)
            assert (IArray.length args1 = IArray.length args2);
            IArray.iter2
              (fun sub1 sub2 ->
                 A.add_eqn sub1 sub2 (CC_injectivity (ra, rb)))
              args1 args2;
            true
          ) else false
        | _ -> true
      end

    type map_status =
      | Map_empty
      | Map_single of data_cstor
      | Map_other

    type labels = data_cstor ID.Map.t

    (* check if set of cstors is empty or unary *)
    let map_status (m: labels): map_status =
      if ID.Map.is_empty m then Map_empty
      else (
        let c, cstor = ID.Map.choose m in
        let m' = ID.Map.remove c m in
        if ID.Map.is_empty m'
        then Map_single cstor
        else Map_other
      )

    (* propagate [r = cstor], using Instantiation rules *)
    let propagate_cstor (r:A.repr) (cstor:data_cstor) (expl:cc_explanation list): unit =
      Log.debugf 5
        (fun k->k "(@[propagate_cstor@ %a@ %a: expl: (@[%a@])@])"
            Term.pp (r:>term) Cst.pp cstor.cstor_cst
            (Utils.pp_list pp_cc_explanation) expl);
      (* TODO: propagate, add_eqn with cstor term, but only
         if either:
         - cstor is finite
         - or some parent term of [r_u] is a selector.

         We need to create new constants for the arguments *)
      assert false

    (* perform (Split 2) if all the cstors of [m] (labels of [r]) are finite
       and (Split 1) was not applied on [r] *)
    let maybe_split (r:A.repr) (m: labels) (expl:cc_explanation list): unit =
      assert (ID.Map.cardinal m >= 2);
      if ID.Map.for_all (fun _ cstor -> Cst.is_finite_cstor cstor.cstor_cst) m
      && not (Term.Field_is_split.get (r:>term).term_bits)
      then (
        Log.debugf 5
          (fun k->k "(@[split_finite@ %a@ cstors: (@[<hv>%a@])@ expl: (@[%a@])@])"
              Term.pp (r:>term) (Utils.pp_list Cst.pp)
              (ID.Map.values m |> Sequence.map (fun c->c.cstor_cst) |> Sequence.to_list)
              (Utils.pp_list pp_cc_explanation) expl);
        let lits =
          ID.Map.values m
          |>
          Sequence.map
            (fun cstor -> Lit.cstor_test cstor (r:>term))
          |> Sequence.to_list
        in
        A.split lits expl
      )

    let set_nf t nf (e:cc_explanation): unit = match nf, t.term_cell with
      | NF_bool sign, App_cst ({cst_kind=Cst_test (_, lazy cstor); _}, args) ->
        (* update set of possible cstors for [A.find args.(0)]
           if [t = is-cstor args] is true/false *)
        assert (IArray.length args = 1);
        let u = IArray.get args 1 in
        let r_u = A.find u in
        let cstor_set, expl = match (r_u:>term).term_cases_set with
          | TC_cstors (m,e') -> m,e'
          | _ -> assert false
        in
        let new_expl = e::expl in
        let cstor_id = cstor.cstor_cst.cst_id in
        if sign then (
          if ID.Map.mem cstor_id cstor_set then (
            (* unit propagate now *)
            propagate_cstor r_u cstor new_expl
          ) else (
            A.unsat new_expl (* conflict: *)
          )
        ) else (
          (* remove [cstor] from the set *)
          if ID.Map.mem cstor_id cstor_set then (
            Log.debugf 5
              (fun k->k "(@[remove_cstor@ %a@ from %a@])" ID.pp cstor_id Term.pp u);
            let new_set = ID.Map.remove cstor_id cstor_set in
            begin match map_status new_set with
              | Map_empty ->
                A.unsat new_expl (* conflict *)
              | Map_single cstor' ->
                propagate_cstor r_u cstor' new_expl;
              | Map_other ->
                (* just update set of labels *)
                if Backtrack.not_at_level_0 () then (
                  let old_cases = (r_u:>term).term_cases_set in
                  Backtrack.push_undo (fun () -> (r_u:>term).term_cases_set <- old_cases);
                );
                (r_u:>term).term_cases_set <- TC_cstors (new_set, new_expl);
                maybe_split r_u new_set new_expl
            end
          )
        )
      | _ -> ()

    let eval t = match t.term_cell with
      | Case (u, m) ->
        let r_u = A.find u in
        begin match (r_u:>term).term_nf with
          | Some (NF_cstor (c, _), _) ->
            (* reduce to the proper branch *)
            let rhs =
              try ID.Map.find c.cstor_cst.cst_id m
              with Not_found -> assert false
            in
            A.add_eqn t rhs (CC_reduce_nf u);
          | Some (NF_bool _, _) -> assert false
          | None -> ()
        end
      | App_cst ({cst_kind=Cst_test(_,lazy cstor); _}, a) when IArray.length a=1 ->
        (* check if [a.(0)] has a constructor *)
        let arg = IArray.get a 0 in
        let r_a = A.find arg in
        begin match (r_a:>term).term_nf with
          | None -> ()
          | Some (NF_cstor (cstor', _), _) ->
            (* reduce to true/false depending on whether [cstor=cstor'] *)
            if Cst.equal cstor.cstor_cst cstor'.cstor_cst then (
              A.add_eqn t Term.true_ (CC_reduce_nf arg)
            ) else (
              A.add_eqn t Term.true_ (CC_reduce_nf arg)
            )
          | Some (NF_bool _, _) -> assert false
        end
      | App_cst ({cst_kind=Cst_proj(_,lazy cstor,i); _}, a) when IArray.length a=1 ->
        (* reduce if [a.(0)] has the proper constructor *)
        let arg = IArray.get a 0 in
        let r_a = A.find arg in
        begin match (r_a:>term).term_nf with
          | None -> ()
          | Some (NF_cstor (cstor', nf_cstor_args), _) ->
            (* [proj-C-i (C t1...tn) = ti] *)
            if Cst.equal cstor.cstor_cst cstor'.cstor_cst then (
              A.add_eqn t (IArray.get nf_cstor_args i) (CC_reduce_nf arg)
            )
          | Some (NF_bool _, _) -> assert false
        end
      | _ -> ()

    let is_evaluable t = match t.term_cell with
      | Case _ -> true
      | App_cst ({cst_kind=Cst_test(_,_); _}, a)
      | App_cst ({cst_kind=Cst_proj(_,_,_); _}, a) ->
        IArray.length a=1
      | _ -> false

    (* split every term that is not split yet, and to which some selectors
       are applied *)
    let split_rule () =
      let is_in_proj (r:A.repr): bool =
        Bag.to_seq (r:>term).term_parents
        |> Sequence.exists
          (fun parent -> match parent.term_cell with
             | App_cst ({cst_kind=Cst_proj _; _}, a) ->
               let res = IArray.length a = 1 in
               (* invariant: a.(0) == r should hold *)
               if res then assert(A.equal_repr r (IArray.get a 1 |> A.find));
               res
             | _ -> false)
      in
      begin
        Log.debug 3 "(data.split1)";
        A.all_classes
        |> Sequence.filter
          (fun (r:A.repr) ->
             (* keep only terms of data-type, never split, with at least
                two possible cases in their label, and that occur in
                at least one selector *)
             Format.printf "check %a@." Term.pp (r:>term);
             Ty.is_data (r:>term).term_ty
             &&
             begin match (r:>term).term_cases_set with
               | TC_cstors (m, _) -> ID.Map.cardinal m >= 2
               | _ -> assert false
             end
             &&
             not (Term.Field_is_split.get (r:>term).term_bits)
             &&
             is_in_proj r)
        |> Sequence.iter
          (fun r ->
             let r = (r:A.repr:>term) in
             Log.debugf 5 (fun k->k "(@[split_1@ term: %a@])" Term.pp r);
             (* unconditional split: consider all cstors *)
             let cstors = match r.term_ty.ty_cell with
               | Atomic (_, Data {data_cstors=lazy cstors;_}) -> cstors
               | _ -> assert false
             in
             let lits =
               ID.Map.values cstors
               |> Sequence.map (fun cstor -> Lit.cstor_test cstor r)
               |> Sequence.to_list
             in
             r.term_bits <- Term.Field_is_split.set true r.term_bits;
             A.split lits [])
      end

    (* TODO acyclicity rule
       could be done by traversing the set of terms, assigning a "level" to
       each equiv class. If level clash, find why, return conflict.
    *)

    let final_check (): unit =
      split_rule ();
      (* TODO: acyclicity *)
      ()
  end

  (** {2 Congruence Closure} *)

  module CC : sig
    type repr = private term

    val equal : repr -> repr -> bool
    (** Are those equivalence classes the same? *)

    val find : term -> repr
    (** Current representative *)

    val union : repr -> repr -> cc_explanation -> unit
    (** Merge the two equivalence classes *)

    val assert_lit : Lit.t -> unit
    (** Given a literal, assume it in the congruence closure and propagate
        its consequences *)

    val normal_form : term -> term_nf option
    (** Normal form of the term's congruence closure, if any *)

    val in_cc : term -> bool
    (** Is the term properly added to the congruence closure? *)

    val add_cc : term -> unit
    (** Add the term to the congruence closure.
        @raise Error if the current level is not 0 *)

    val expand_term : term -> unit
    (** Expand this term and add its expansion to the CC *)

    val add_cc_seq : term Sequence.t -> unit
    (** Add a sequence of terms to the congruence closure *)

    val add_toplevel_eq : term -> term -> unit
    (** Add [t = u] as a toplevel unconditional equation *)

    type lemma =
      | Propagate of Lit.t * cc_explanation list
      | Split of Lit.t list * cc_explanation list

    type result =
      | Sat of lemma list
      | Unsat of cc_explanation list
      (* list of direct explanations to the conflict. *)

    val check : unit -> result

    val final_check : unit -> result

    val explain_unfold: cc_explanation list -> Lit.Set.t
    (** Unfold those explanations into a complete set of
        literals implying them *)
  end = struct
    type repr = term

    let equal = Term.equal

    let is_root_ t = t.term_root == t
    let same_class_ (r1:repr)(r2:repr): bool = equal r1 r2
    let size_ (r:repr) = assert (is_root_ r); Bag.size r.term_parents

    (* check if [t] is in the congruence closure.
       Invariant: [in_cc t => in_cc u, forall u subterm t] *)
    let in_cc (t:term): bool = Term.Field_in_cc.get t.term_bits

    let signatures_tbl : term Term_cell.Tbl.t
      = Term_cell.Tbl.create 2048
    (* map a signature to the corresponding term in some equivalence class.
       A signature is a [term_cell] in which every immediate subterm
       that participates in the congruence/evaluation relation
       is normalized (i.e. is its own representative).
       The critical property is that all members of an equivalence class
       that have the same "shape" (including head symbol)
       have the same signature *)

    (* find representative, recursively, and perform path compression *)
    let rec find_rec t : repr =
      if t==t.term_root then t
      else (
        let old_root = t.term_root in
        let root = find_rec old_root in
        (* path compression *)
        if root != old_root then (
          if Backtrack.not_at_level_0 () then (
            Backtrack.push_undo (fun () -> t.term_root <- old_root);
          );
          t.term_root <- root;
        );
        root
      )

    (* non-recursive, inlinable function for [find] *)
    let find t =
      if t == t.term_root then t
      else find_rec t

    let normal_form t =
      let r = find t in
      CCOpt.map fst r.term_nf

    let signature (t:term_cell): term_cell option = match t with
      | True | False | DB _ | Fun _ | Mu _ | Builtin _
        -> None
      | App_cst (_, a) when IArray.is_empty a -> None
      | App_cst (f, a) -> App_cst (f, IArray.map find a) |> CCOpt.return
      | App_ho (f, l) -> App_ho (find f, List.map find l) |> CCOpt.return
      | If (a,b,c) -> If (find a, b, c) |> CCOpt.return
      | Case (t, m) -> Case (find t, m) |> CCOpt.return

    (* find whether the given (parent) term corresponds to some signature
       in [signatures_] *)
    let find_by_signature (t:term_cell): term option = match signature t with
      | None -> None
      | Some t' -> Term_cell.Tbl.get signatures_tbl t'

    let remove_signature (t:term_cell): unit = match signature t with
      | None -> ()
      | Some t' ->
        Term_cell.Tbl.remove signatures_tbl t'

    let add_signature (t:term_cell)(r:term): unit = match signature t with
      | None -> ()
      | Some t' ->
        assert (CCOpt.map_or ~default:false (Term_cell.equal t') (signature r.term_cell));
        (* add, but only if not present already *)
        begin match Term_cell.Tbl.get signatures_tbl t' with
          | None ->
            if Backtrack.not_at_level_0 () then (
              Backtrack.push_undo
                (fun () -> Term_cell.Tbl.remove signatures_tbl t');
            );
            Term_cell.Tbl.add signatures_tbl t' r;
          | Some r' -> assert (Term.equal r r');
        end

    type merge_op = term * term * cc_explanation
    (* a merge operation to perform *)

    type lemma =
      | Propagate of Lit.t * cc_explanation list
      | Split of Lit.t list * cc_explanation list

    type update_state = {
      terms_to_add: term Queue.t;
      (* queue of terms that must be added to the CC first (then to [pending]).

         If [in_cc t], nothing is done. Otherwise, do the full operation.
         A term can occur several times in this queue.
         This is critical for inserting terms in the congruence closure dynamically,
         because we need to remove  them upon backtracking, and remember to add
         them again afterwards. *)
      eqns_to_add: merge_op Queue.t;
      (* (toplevel) equations that must be added, e.g. for [t = normal_form(t)]
         or [f a b = body_f[x:=a, y:=b]] *)
      pending: term Queue.t;
      (* terms to check, maybe their new signature is in {!signatures_tbl} *)
      combine: merge_op Queue.t;
      (* pairs of terms to merge *)
      mutable lemmas: lemma list;
      (* some boolean propagations/splits to make. *)
    }

    (* global state for congruence closure *)
    let st : update_state = {
      terms_to_add=Queue.create();
      eqns_to_add=Queue.create();
      pending=Queue.create();
      combine=Queue.create();
      lemmas=[];
    }

    let is_done_state (): bool =
      Queue.is_empty st.terms_to_add &&
      Queue.is_empty st.eqns_to_add &&
      Queue.is_empty st.pending &&
      Queue.is_empty st.combine

    let push_combine t u e =
      Log.debugf 5
        (fun k->k "(@[<hv1>push_combine@ %a@ %a@ expl: %a@])"
          Term.pp t Term.pp u pp_cc_explanation e);
      Queue.push (t,u,e) st.combine

    let push_pending t =
      Log.debugf 5 (fun k->k "(@[<hv1>push_pending@ %a@])" Term.pp t);
      Queue.push t st.pending

    let push_split (lits:lit list) (expl:cc_explanation list): unit =
      Log.debugf 5
        (fun k->k "(@[<hv1>push_split@ (@[%a@])@ expl: (@[<hv>%a@])@])"
          (Utils.pp_list Lit.pp) lits (Utils.pp_list pp_cc_explanation) expl);
      let l = Split (lits, expl) in
      st.lemmas <- l :: st.lemmas

    let push_propagation (lit:lit) (expl:cc_explanation list): unit =
      Log.debugf 5
        (fun k->k "(@[<hv1>push_propagate@ %a@ expl: (@[<hv>%a@])@])"
          Lit.pp lit (Utils.pp_list pp_cc_explanation) expl);
      let l = Propagate (lit,expl) in
      st.lemmas <- l :: st.lemmas

    let add_cc (t:term): unit = Queue.push t st.terms_to_add

    let add_cc_seq (seq:term Sequence.t): unit = Sequence.iter add_cc seq

    let add_toplevel_eq (t:term) (u:term): unit =
      Log.debugf 5 (fun k->k "(@[<hv1>push_toplevel_eq@ %a@ %a@])" Term.pp t Term.pp u);
      Queue.push (t, u, CC_reduction) st.eqns_to_add

    let union (a:repr) (b:repr) (e:cc_explanation): unit =
      assert (is_root_ a);
      assert (is_root_ b);
      assert (is_done_state ());
      if not (same_class_ a b) then (
        push_combine a b e; (* start by merging [a=b] *)
      )

    (* assert that this boolean literal holds *)
    let assert_lit lit : unit = match Lit.view lit with
      | Lit_fresh _
      | Lit_expanded _ -> ()
      | Lit_atom t ->
        assert (Ty.is_prop t.term_ty);
        let sign = Lit.sign lit in
        (* equate t and true/false *)
        let rhs = if sign then Term.true_ else Term.false_ in
        add_cc t;
        push_combine t rhs (CC_lit lit);
        ()

    (* re-root the explanation tree of the equivalence class of [t]
       so that it points to [t].
       postcondition: [t.term_expl = None] *)
    let rec reroot_expl (t:term): unit =
      let old_expl_t = t.term_expl in
      if Backtrack.not_at_level_0 () then (
        Backtrack.push_undo (fun () -> t.term_expl <- old_expl_t);
      );
      begin match old_expl_t with
        | None -> () (* already root *)
        | Some (u, e_t_u) ->
          reroot_expl u;
          u.term_expl <- Some (t, e_t_u);
          t.term_expl <- None;
      end

    (* instantiate expansion of terms *)
    module E = Expand(struct
        let add_clause = Clause.push_new
        let add_clause_l = Clause.push_new_l
        let add_eqn = add_toplevel_eq
        let delay_expansion = Terms_to_expand.add
      end)

    let expand_term t: unit =
      if not (Term.Field_expanded.get t.term_bits) then (
        Log.debugf 3 (fun k->k "(@[CC.expand@ %a@])" Term.pp t);
        E.expand_term ~mode:E.Force t;
        assert (Term.Field_expanded.get t.term_bits);
      )

    exception Exn_unsat of cc_explanation list

    let unsat (e:cc_explanation list): _ = raise (Exn_unsat e)

    type result =
      | Sat of lemma list
      | Unsat of cc_explanation list
      (* list of direct explanations to the conflict. *)

    let all_classes : repr Sequence.t = fun yield ->
      Term.all_terms
      |> Sequence.filter (fun t -> is_root_ t && Term.Field_in_cc.get t.term_bits)
      |> Sequence.iter yield

    module Theory_actions : THEORY_ACTION = struct
      type repr = term
      let equal_repr = Term.equal
      let all_classes = all_classes
      let find = find
      let add_eqn = push_combine
      let propagate = push_propagation
      let split = push_split
      let unsat = unsat
    end

    module Theory_bool = Bool(Theory_actions)
    module Theory_data = Datatype(Theory_actions)

    let theories : theory list =
      [ (module Theory_bool);
        (module Theory_data)
      ]

    (* does [t] have some (direct) evaluation semantics? *)
    let is_evaluable (t:term): bool =
      List.exists
        (fun (module Theory: THEORY) -> Theory.is_evaluable t)
        theories

    (* main CC algo: add terms from [pending] to the signature table,
       check for collisions *)
    let rec update_pending (): result =
      (* step 2 deal with pending (parent) terms whose equiv class
         might have changed *)
      while not (Queue.is_empty st.pending) do
        let t = Queue.pop st.pending in
        assert (Term.Field_in_cc.get t.term_bits);
        (* check if some parent collided *)
        begin match find_by_signature t.term_cell with
          | None ->
            (* add to the signature table *)
            add_signature t.term_cell t
          | Some u ->
            (* must combine [t] with [r] *)
            push_combine t u (CC_congruence (t,u))
        end;
        eval_pending t;
      done;
      if is_done_state ()
      then (
        let lemmas = st.lemmas in
        st.lemmas <- [];
        Sat lemmas
      )
      else update_combine st (* repeat *)

    (* main CC algo: merge equivalence classes in [st.combine].
       @raise Exn_unsat if merge fails *)
    and update_combine st =
      while not (Queue.is_empty st.combine) do
        let a, b, e_ab = Queue.pop st.combine in
        let ra = find a in
        let rb = find b in
        if not (equal ra rb) then (
          assert (is_root_ ra);
          assert (is_root_ rb);
          (* invariant: [size ra <= size rb].
             we merge [ra] into [rb]. *)
          let ra, rb = if size_ ra > size_ rb then rb, ra else ra, rb in
          (* check normal form(s) for consistency, merge them *)
          let merge_ok = check_normal_forms ra rb e_ab in
          if not merge_ok then (
            let l = [e_ab; CC_reduce_nf a; CC_reduce_nf b] in
            unsat l; (* incompatible *)
          );
          (* remove [ra.parents] from signature, put them into [st.pending] *)
          begin
            Bag.to_seq ra.term_parents
            |> Sequence.iter
              (fun parent ->
                 (* FIXME: with OCaml's hashtable, we should be able
                    to keep this entry (and have it become relevant later
                    once the signature of [parent] is backtracked) *)
                 remove_signature parent.term_cell;
                 push_pending parent)
          end;
          (* perform [union ra rb] *)
          begin
            let rb_old_class = rb.term_class in
            let rb_old_parents = rb.term_parents in
            Backtrack.push_undo
              (fun () ->
                 ra.term_root <- ra;
                 rb.term_class <- rb_old_class;
                 rb.term_parents <- rb_old_parents);
            ra.term_root <- rb;
            rb.term_class <- Bag.append rb_old_class ra.term_class;
            rb.term_parents <- Bag.append rb_old_parents ra.term_parents;
          end;
          (* update explanations (a -> b) *)
          begin
            reroot_expl a;
            assert (a.term_expl = None);
            if Backtrack.not_at_level_0 () then (
              Backtrack.push_undo (fun () -> a.term_expl <- None);
            );
            a.term_expl <- Some (b, e_ab);
          end;
        )
      done;
      (* now update pending terms again *)
      update_pending ()

    (* [r == nf] because [e]; perform propagations to the theories and the
       SAT solver *)
    and set_nf_of_class (nf:term_nf) (r:repr) (e:cc_explanation): unit =
      (* traverse the equiv class of [r], check every term for boolean
         propagations and theory propagations *)
      begin
        Bag.to_seq r.term_class
        |> Sequence.iter
          (fun t ->
             begin match nf with
               | NF_bool sign ->
                 (* propagate to the SAT solver *)
                 if t != r && Term.Field_is_lit.get t.term_bits then (
                   let l = [e; CC_reduce_eq (t, r)] in
                   push_propagation (Lit.atom ~sign t) l;
                 );
               | _ -> ()
             end;
             List.iter
               (fun (module Theory : THEORY) -> Theory.set_nf t nf e)
               theories)
      end;
      (* update parents that might be evaluable, because the newly
         acquired normal form of [r] might trigger some eval rule *)
      begin
        Bag.to_seq r.term_parents
        |> Sequence.filter is_evaluable
        |> Sequence.iter
          (fun parent ->
             remove_signature parent.term_cell;
             push_pending parent)
      end;
      ()

    (* returns [true] if [ra] and [rb] have compatible normal forms.
       Side effect: also pushes sub-tasks *)
    and check_normal_forms (ra:repr)(rb:repr)(e:cc_explanation): bool =
      assert (is_root_ ra);
      assert (is_root_ rb);
      begin match ra.term_nf, rb.term_nf with
        | None, None -> true
        | None, Some (nf,_) ->
          set_nf_of_class nf ra e;
          true
        | Some nf, (None as old_nf_b) ->
          (* update [rb]'s normal form *)
          if Backtrack.not_at_level_0 () then (
            Backtrack.push_undo (fun () -> rb.term_nf <- old_nf_b);
          );
          rb.term_nf <- Some nf;
          (* NOTE: this update must be performed only after [rb.term_nf] is set *)
          set_nf_of_class (fst nf) rb e;
          true
        | Some (nf_a,_), Some (nf_b,_) ->
          List.for_all
            (fun (module Theory : THEORY) -> Theory.merge_nf ra rb nf_a nf_b)
            theories
      end

    (* evaluation rules: if, case... *)
    and eval_pending (t:term): unit =
      List.iter
        (fun (module Theory : THEORY) -> Theory.eval t)
        theories

    (* main CC algo: add missing terms to the congruence class *)
    and update_add_cc_terms () =
      while not (Queue.is_empty st.terms_to_add) do
        let t = Queue.pop st.terms_to_add in
        add_cc_pending t
      done

    and update_add_cc_eqns () =
      while not (Queue.is_empty st.eqns_to_add) do
        let eqn = Queue.pop st.eqns_to_add in
        add_cc_eqn st eqn
      done

    (* add [t] to the congruence closure *)
    and add_cc_pending (t:term): unit =
      if not (in_cc t) then (
        (* on backtrack: add [t] again later *)
        if Backtrack.not_at_level_0 () then (
          Backtrack.push_undo
            (fun () ->
               t.term_bits <- Term.Field_in_cc.set false t.term_bits;
               Queue.push t st.terms_to_add;
            )
        );
        t.term_bits <- Term.Field_in_cc.set true t.term_bits;
        (* expand term *)
        if not (Term.Field_expanded.get t.term_bits) then (
          E.expand_term ~mode:E.Safe t
        );
        let add_sub sub =
          let old_parents = sub.term_parents in
          sub.term_parents <- Bag.cons t sub.term_parents;
          (* NOTE: add to CC after updating parents, so that [t] is merged
             properly too *)
          add_cc_pending sub;
          if Backtrack.not_at_level_0 () then (
            Backtrack.push_undo (fun () -> sub.term_parents <- old_parents);
          )
        in
        (* register sub-terms, add [t] to their parent list *)
        begin match t.term_cell with
          | True | False | DB _ -> ()
          | App_cst (_, a) -> IArray.iter add_sub a
          | App_ho (f, l) ->
            add_sub f;
            List.iter add_sub l
          | Case (t, m) ->
            add_sub t;
            ID.Map.values m |> Sequence.iter add_sub
          | If (a,b,c) ->
            add_sub a;
            add_sub b;
            add_sub c
          | Mu _
          | Fun _ -> () (* not expanded yet *)
          | Builtin b -> Term.builtin_to_seq b add_sub
        end;
        (* will have to find [t]'s congruence class *)
        push_pending t;
      )

    (* add [t=u] to the congruence closure, unconditionally (reduction relation)  *)
    and add_cc_eqn (st:update_state) (eqn:merge_op): unit =
      (* on backtrack: remember to add [t=u] again *)
      if Backtrack.not_at_level_0 () then (
        Backtrack.push_undo (fun () -> Queue.push eqn st.eqns_to_add);
      );
      let t, u, expl = eqn in
      Queue.push t st.terms_to_add;
      Queue.push u st.terms_to_add;
      push_combine t u expl

    (* distance from [t] to its root in the proof forest *)
    let rec distance_to_root (t:term): int = match t.term_expl with
      | None -> 0
      | Some (t', _) -> 1 + distance_to_root t'

    (* find the closest common ancestor of [a] and [b] in the proof forest *)
    let find_common_ancestor a b: term =
      let d_a = distance_to_root a in
      let d_b = distance_to_root b in
      (* drop [n] nodes in the path from [t] to its root *)
      let rec drop_ n t =
        if n=0 then t
        else match t.term_expl with
          | None -> assert false
          | Some (t', _) -> drop_ (n-1) t'
      in
      (* reduce to the problem where [a] and [b] have the same distance to root *)
      let a, b =
        if d_a > d_b then drop_ (d_a-d_b) a, b
        else if d_a < d_b then a, drop_ (d_b-d_a) b
        else a, b
      in
      (* traverse stepwise until a==b *)
      let rec aux_same_dist a b =
        if a==b then a
        else match a.term_expl, b.term_expl with
          | None, _ | _, None -> assert false
          | Some (a', _), Some (b', _) -> aux_same_dist a' b'
      in
      aux_same_dist a b

    type proof_state = {
      mutable ps_lits: Lit.Set.t;
      ps_queue: (term*term) Queue.t;
    }

    let create_proof_state() = {
      ps_lits=Lit.Set.empty;
      ps_queue=Queue.create();
    }
    (* TODO: an additional union-find to keep track, for each term,
       of the terms they are known to be equal to, according
       to the current explanation. That allows not to prove some equality
       several times.
       See "fast congruence closure and extensions", Nieuwenhis&al, page 14 *)

    let ps_add_obligation ps a b = Queue.push (a,b) ps.ps_queue
    let ps_add_lit ps l = ps.ps_lits <- Lit.Set.add l ps.ps_lits
    let ps_add_expl ps e = match e with
      | CC_lit lit -> ps_add_lit ps lit
      | CC_reduce_nf _ | CC_reduce_eq _ | CC_congruence _
      | CC_injectivity _ | CC_reduction
        -> ()

    let decompose_explain ps (e:cc_explanation): unit =
      Log.debugf 5 (fun k->k "(@[decompose_expl@ %a@])" pp_cc_explanation e);
      ps_add_expl ps e;
      begin match e with
        | CC_reduction
        | CC_lit _ -> ()
        | CC_reduce_nf t ->
          let r = find t in
          begin match r.term_nf with
            | None -> assert false
            | Some (_, t_nf) -> ps_add_obligation ps t t_nf
          end
        | CC_reduce_eq (a, b) ->
          ps_add_obligation ps a b;
        | CC_injectivity (t1,t2)
        (* FIXME: should this be different from CC_congruence? just explain why t1==t2? *)
        | CC_congruence (t1,t2) ->
          begin match t1.term_cell, t2.term_cell with
            | True, _ | False, _ | DB _, _
            | Mu _, _ | Fun _, _ -> assert false (* no congruence here *)
            | App_cst (f1, a1), App_cst (f2, a2) ->
              assert (Cst.equal f1 f2);
              assert (IArray.length a1 = IArray.length a2);
              IArray.iter2 (ps_add_obligation ps) a1 a2
            | App_ho (f1, l1), App_ho (f2, l2) ->
              assert (List.length l1 = List.length l2);
              ps_add_obligation ps f1 f2;
              List.iter2 (ps_add_obligation ps) l1 l2
            | Case (t1, m1), Case (t2, m2) ->
              ps_add_obligation ps t1 t2;
              ID.Map.iter
                (fun id rhs1 ->
                   let rhs2 = ID.Map.find id m2 in
                   ps_add_obligation ps rhs1 rhs2)
                m1;
            | If (a1,b1,c1), If (a2,b2,c2) ->
              ps_add_obligation ps a1 a2;
              ps_add_obligation ps b1 b2;
              ps_add_obligation ps c1 c2;
            | Builtin _, _ -> assert false
            | App_cst _, _
            | App_ho _, _
            | Case _, _
            | If _, _
              -> assert false
          end
      end

    (* explain why [a = parent_a], where [a -> ... -> parent_a] in the
       proof forest *)
    let rec explain_along_path ps a parent_a =
      if a!=parent_a then (
        match a.term_expl with
          | None -> assert false
          | Some (next_a, e_a_b) ->
            decompose_explain ps e_a_b;
            (* now prove [next_a = parent_a] *)
            explain_along_path ps next_a parent_a
      )

    let explain_loop ps: Lit.Set.t =
      while not (Queue.is_empty ps.ps_queue) do
        let a, b = Queue.pop ps.ps_queue in
        Log.debugf 5 (fun k->k "(@[explain_loop at@ %a@ %a@])" Term.pp a Term.pp b);
        assert (find a == find b);
        let c = find_common_ancestor a b in
        explain_along_path ps a c;
        explain_along_path ps b c;
      done;
      ps.ps_lits

    let explain_unfold (l:cc_explanation list): Lit.Set.t =
      Log.debugf 5
        (fun k->k "(@[explain_confict@ (@[<hv>%a@])@])"
            (Utils.pp_list pp_cc_explanation) l);
      let ps = create_proof_state () in
      List.iter (decompose_explain ps) l;
      explain_loop ps

    let check_prelude_ () =
      update_add_cc_eqns ();
      (* NOTE: add terms after adding equations, because some
         equations might have pushed terms in [st.terms_to_add] *)
      update_add_cc_terms ();
      ()

    (* check satisfiability, update congruence closure *)
    let check (): result =
      Log.debug 5 "(CC.check)";
      check_prelude_ ();
      try
        update_pending ()
      with Exn_unsat e ->
        Unsat e

    let final_check (): result =
      Log.debug 5 "(CC.final_check)";
      check_prelude_ ();
      try
        Theory_data.final_check();
        update_pending ()
      with Exn_unsat e ->
        Unsat e
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
    Printf.printf "\r[%.2f] expanded %d | clauses %d | lemmas %d%!"
      (get_time())
      !stat_num_cst_expanded
      !stat_num_clause_push
      !stat_num_clause_tautology

  let flush_progress (): unit =
    Printf.printf "\r%-80d\r%!" 0

  (** {2 Toplevel Goals}

      List of toplevel goals to satisfy. Mainly used for checking purpose
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
    let is_true_ (t:term): bool = match CC.normal_form t with
      | None -> false
      | Some (NF_bool b) -> b
      | Some (NF_cstor _) -> assert false (* not a bool *)

    let check () =
      if not (List.for_all is_true_ !toplevel_goals_)
      then (
        if Config.progress then flush_progress();
        Log.debugf 1
          (fun k->
             let pp_lit out t =
               let nf = CC.normal_form t in
               Format.fprintf out "(@[term: %a@ nf: %a@])"
                 Term.pp t (CCFormat.opt pp_term_nf) nf
             in
             k "(@[<hv1>Top_goals.check@ (@[<v>%a@])@])"
               (Utils.pp_list pp_lit) !toplevel_goals_);
        assert false;
      )
  end

  (* push those propagations into the SAT solver *)
  let add_cc_lemmas (l:CC.lemma list): unit =
    List.iter
      (fun l ->
         let c = match l with
           | CC.Propagate (lit,l) ->
             let lit_set = CC.explain_unfold l in
             let c =
               let guard =
                 Lit.Set.to_list lit_set
                 |> List.map Lit.neg
               in
               Clause.make (lit :: guard)
             in
             Log.debugf 2
               (fun k->k "(@[@{<green>propagate@}@ %a@])" Clause.pp c);
             c
           | CC.Split (lits,l) ->
             let lit_set = CC.explain_unfold l in
             let c =
               let guard =
                 Lit.Set.to_list lit_set
                 |> List.map Lit.neg
               in
               Clause.make (lits @ guard)
             in
             Log.debugf 2
               (fun k->k "(@[@{<green>split@}@ %a@])" Clause.pp c);
             c
         in
         Clause.push_new c)
      l

  (* the "theory" part: propagations *)
  module M_th :
    Msat.Theory_intf.S
    with type formula = M_expr.t
     and type proof = M_expr.proof
  = struct
    type formula = M_expr.t
    type proof = M_expr.proof

    type level_ = level
    type level = level_

    let dummy = Backtrack.dummy_level

    (* increment and return level *)
    let current_level () =
      Backtrack.push_level ();
      Backtrack.cur_level ()

    let backtrack = Backtrack.backtrack

    let push_clause slice (c:Clause.t): unit =
      let lits = Clause.lits c in
      slice.TI.push lits ()

    (* push clauses from {!lemma_queue} into the slice *)
    let flush_new_clauses_into_slice slice =
      while not (Queue.is_empty Clause.lemma_queue) do
        let c = Queue.pop Clause.lemma_queue in
        Log.debugf 5 (fun k->k "(@[<2>push_lemma@ %a@])" Clause.pp c);
        push_clause slice c
      done

    (* handle a literal assumed by the SAT solver *)
    let assume_lit (lit:Lit.t) : unit =
      Log.debugf 2
        (fun k->k "(@[<1>@{<green>assume_lit@}@ @[%a@]@])" Lit.pp lit);
      (* check consistency first *)
      begin match Lit.view lit with
        | Lit_fresh _ -> ()
        | Lit_expanded _
        | Lit_atom {term_cell=True; _} -> ()
        | Lit_atom {term_cell=False; _} -> assert false
        | Lit_atom _ ->
          (* let the CC do the job *)
          CC.assert_lit lit
      end

    (* convert a result from CC to one that the SAT solver understands *)
    let transform_res slice (res: CC.result): (_,_) TI.res =
      begin match res with
        | CC.Sat lemmas ->
          add_cc_lemmas lemmas;
          flush_new_clauses_into_slice slice;
          TI.Sat
        | CC.Unsat expls ->
          let lit_set = CC.explain_unfold expls in
          let conflict_clause =
            Lit.Set.to_list lit_set
            |> List.map Lit.neg
            |> Clause.make
          in
          Log.debugf 3
            (fun k->k "(@[<1>conflict@ clause: %a@])"
                Clause.pp conflict_clause);
          (* TODO: proof? *)
          TI.Unsat (Clause.lits conflict_clause, ())
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
      (* now check satisfiability *)
      let res = CC.check () in
      flush_new_clauses_into_slice slice;
      transform_res slice res

    (* perform final check of the model *)
    let if_sat slice =
      let res = CC.final_check() in
      match transform_res slice res with
        | TI.Sat -> ()
        | TI.Unsat (c,_) ->
          push_clause slice (Clause.make c)
  end

  module M = Msat.Solver.Make(M_expr)(M_th)(struct end)

  (* push one clause into [M], in the current level (not a lemma but
     an axiom) *)
  let push_clause (c:Clause.t): unit =
    Log.debugf 2 (fun k->k "(@[<1>push_clause@ @[%a@]@])" Clause.pp c);
    incr stat_num_clause_push;
    (* add terms to the congruence closure *)
    Clause.iter
      (fun lit -> match Lit.view lit with
         | Lit_expanded t
         | Lit_atom t -> CC.add_cc t
         | Lit_fresh _ -> ())
      c;
    M.assume [Clause.lits c]

  (** {2 Conversion} *)

  (* list of constants we are interested in *)
  let model_support_ : Cst.t list ref = ref []

  let model_env_ : Ast.env ref = ref Ast.env_empty

  let add_cst_support_ (c:cst): unit =
    CCList.Ref.push model_support_ c

  let add_ty_support_ (_ty:Ty.t): unit = ()

  module Conv : sig
    val add_statement : Ast.statement -> unit
    val add_statement_l : Ast.statement list -> unit
    val ty_to_ast: Ty.t -> Ast.Ty.t
    val term_to_ast: term -> Ast.term
  end = struct
    (* for converting Ast.Ty into Ty *)
    let ty_tbl_ : Ty.t lazy_t ID.Tbl.t = ID.Tbl.create 16

    (* for converting constants *)
    let decl_ty_ : cst lazy_t ID.Tbl.t = ID.Tbl.create 16

    module AstVarMap = CCMap.Make(struct
        type t = Ast.var
        let compare = Ast.Var.compare
      end)

    (* environment for variables *)
    type conv_env = {
      bound: Ast.var list; (* bound variables, turn into De Bruijn *)
      subst: term AstVarMap.t; (* variables to substitute *)
    }

    let empty_env : conv_env = {bound=[]; subst=AstVarMap.empty}

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
        begin match Ast.term_view f with
          | Ast.Const id ->
            let f =
              try ID.Tbl.find decl_ty_ id |> Lazy.force
              with Not_found ->
                errorf "could not find constant `%a`" ID.pp id
            in
            let l = List.map (conv_term env) l in
            if List.length l = fst (Ty.unfold_n (Cst.ty f))
            then Term.app_cst f (IArray.of_list l) (* fully applied *)
            else Term.app (Term.const f) l
          | _ ->
            let f = conv_term env f in
            let l = List.map (conv_term env) l in
            Term.app f l
        end
      | Ast.Var v ->
        (* look whether [v] must be replaced by some term *)
        begin match AstVarMap.get v env.subst with
          | Some t -> t
          | None ->
            (* lookup as bound variable *)
            begin match CCList.find_idx (Ast.Var.equal v) env.bound with
              | None -> errorf "could not find var `%a`" Ast.Var.pp v
              | Some (i,_) ->
                let ty = Ast.Var.ty v |> conv_ty in
                Term.db (DB.make i ty)
            end
        end
      | Ast.Fun (v,body) ->
        let body = conv_term {env with bound=v::env.bound} body in
        let ty = Ast.Var.ty v |> conv_ty in
        Term.fun_ ty body
      | Ast.Forall _
      | Ast.Exists _ ->
        errorf "quantifiers not supported"
      | Ast.Mu (v,body) ->
        let body = conv_term {env with bound=v::env.bound} body in
        Term.mu body
      | Ast.Match (u,m) ->
        let u = conv_term env u in
        let data = match Ty.view u.term_ty with
          | Atomic (_, Data data) -> data
          | _ -> assert false
        in
        let m =
          ID.Map.mapi
            (fun c_id (vars,rhs) ->
               let cstor =
                 try ID.Map.find c_id (Lazy.force data.data_cstors)
                 with Not_found -> errorf "invalid constructor %a" ID.pp c_id
               in
               (* replace the variables of the pattern-matching with
                  projections of cstor *)
               let subst =
                 CCList.Idx.foldi
                   (fun subst i v ->
                      let arg_i = Term.cstor_proj cstor i u in
                      let subst = AstVarMap.add v arg_i subst in
                      subst)
                   env.subst vars
               in
               conv_term {env with subst} rhs)
            m
        in
        let res = Term.case u m in
        res
      | Ast.Switch _ ->
        errorf "cannot convert switch %a" Ast.pp_term t
      | Ast.Let (v,t,u) ->
        (* substitute on the fly *)
        let t = conv_term env t in
        conv_term {env with subst=AstVarMap.add v t env.subst} u
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
      begin match st with
        | Ast.Assert t ->
          let t = conv_term empty_env t in
          Top_goals.push t;
          push_clause (Clause.make [Lit.atom t])
        | Ast.Goal (vars, t) ->
          (* skolemize *)
          let env, consts =
            CCList.fold_map
              (fun env v ->
                 let ty = Ast.Var.ty v |> conv_ty in
                 let c = Cst.make_undef (Ast.Var.id v) ty in
                 {env with subst=AstVarMap.add v (Term.const c) env.subst}, c)
              empty_env
              vars
          in
          (* model should contain values of [consts] *)
          List.iter add_cst_support_ consts;
          let t = conv_term env t in
          Top_goals.push t;
          push_clause (Clause.make [Lit.atom t])
        | Ast.TyDecl id ->
          let ty = Ty.atomic id Uninterpreted ~card:(Lazy.from_val Infinite) in
          add_ty_support_ ty;
          ID.Tbl.add ty_tbl_ id (Lazy.from_val ty)
        | Ast.Decl (id, ty) ->
          assert (not (ID.Tbl.mem decl_ty_ id));
          let ty = conv_ty ty in
          let cst = Cst.make_undef id ty in
          add_cst_support_ cst; (* need it in model *)
          ID.Tbl.add decl_ty_ id (Lazy.from_val cst)
        | Ast.Data l ->
          (* the datatypes in [l]. Used for computing cardinalities *)
          let in_same_block : ID.Set.t =
            List.map (fun {Ast.Ty.data_id; _} -> data_id) l |> ID.Set.of_list
          in
          (* declare the type, and all the constructors *)
          List.iter
            (fun {Ast.Ty.data_id; data_cstors} ->
               let ty = lazy (
                 let card_ : ty_card ref = ref Finite in
                 let cstors = lazy (
                   data_cstors
                   |> ID.Map.map
                     (fun c ->
                        let c_id = c.Ast.Ty.cstor_id in
                        let ty_c = conv_ty c.Ast.Ty.cstor_ty in
                        let ty_args, ty_ret = Ty.unfold ty_c in
                        (* add cardinality of [c] to the cardinality of [data_id].
                           (product of cardinalities of args) *)
                        let cstor_card =
                          ty_args
                          |> List.map
                            (fun ty_arg -> match ty_arg.ty_cell with
                               | Atomic (id, _) when ID.Set.mem id in_same_block ->
                                 Infinite
                               | _ -> Lazy.force ty_arg.ty_card)
                          |> Ty_card.product
                        in
                        card_ := Ty_card.( !card_ + cstor_card );
                        let rec cst = lazy (
                          Cst.make_cstor c_id ty_c cstor
                        ) and cstor = lazy (
                          let cstor_proj = lazy (
                            let n = ref 0 in
                            List.map2
                              (fun id ty_arg ->
                                 let ty_proj = Ty.arrow ty_ret ty_arg in
                                 let i = !n in
                                 incr n;
                                 Cst.make_proj id ty_proj cstor i)
                              c.Ast.Ty.cstor_proj ty_args
                            |> IArray.of_list
                          ) in
                          let cstor_test = lazy (
                            let ty_test = Ty.arrow ty_ret Ty.prop in
                            Cst.make_tester c.Ast.Ty.cstor_test ty_test cstor
                          ) in
                          { cstor_ty=ty_c; cstor_cst=Lazy.force cst;
                            cstor_args=IArray.of_list ty_args;
                            cstor_proj; cstor_test; cstor_card; }
                        ) in
                        ID.Tbl.add decl_ty_ c_id cst; (* declare *)
                        Lazy.force cstor)
                 )
                 in
                 let data = { data_cstors=cstors; } in
                 let card = lazy (
                   ignore (Lazy.force cstors);
                   let r = !card_ in
                   Log.debugf 5
                     (fun k->k "(@[card_of@ %a@ %a@])" ID.pp data_id Ty_card.pp r);
                   r
                 ) in
                 Ty.atomic data_id (Data data) ~card
               ) in
               ID.Tbl.add ty_tbl_ data_id ty;
            )
            l;
          (* force evaluation *)
          List.iter
            (fun {Ast.Ty.data_id; _} ->
               let lazy ty = ID.Tbl.find ty_tbl_ data_id in
               ignore (Lazy.force ty.ty_card);
               begin match ty.ty_cell with
                 | Atomic (_, Data {data_cstors=lazy _; _}) -> ()
                 | _ -> assert false
               end)
            l
        | Ast.Define (k,l) ->
          (* declare the mutually recursive functions *)
          List.iter
            (fun (id,ty,rhs) ->
               let ty = conv_ty ty in
               let rhs = lazy (conv_term empty_env rhs) in
               let k = match k with
                 | Ast.Recursive -> Cst_recursive
                 | Ast.Non_recursive -> Cst_non_recursive
               in
               let cst = lazy (
                 Cst.make_defined id ty rhs k
               ) in
               ID.Tbl.add decl_ty_ id cst)
            l;
          (* force thunks *)
          List.iter
            (fun (id,_,_) -> ignore (ID.Tbl.find decl_ty_ id |> Lazy.force))
            l
      end

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

    let term_to_ast (t:term): Ast.term =
      let rec aux env t = match t.term_cell with
        | True -> A.true_
        | False -> A.false_
        | DB d ->
          begin match DB_env.get d env with
            | Some t' -> t'
            | None -> errorf "cannot find DB %a in env" Term.pp t
          end
        | App_cst (f, args) when IArray.is_empty args ->
          A.const f.cst_id (ty_to_ast t.term_ty)
        | App_cst (f, args) ->
          let f = A.const f.cst_id (ty_to_ast (Cst.ty f)) in
          let args = IArray.map (aux env) args in
          A.app f (IArray.to_list args)
        | App_ho (f,l) -> A.app (aux env f) (List.map (aux env) l)
        | Fun (ty,bod) ->
          with_var ty env
            ~f:(fun v env -> A.fun_ v (aux env bod))
        | Mu _ -> assert false
        | If (a,b,c) -> A.if_ (aux env a)(aux env b) (aux env c)
        | Case (u,m) ->
          let u = aux env u in
          let m =
            ID.Map.mapi
              (fun _c_id _rhs ->
                 assert false  (* TODO: fetch cstor; bind variables; convert rhs *)
                   (*
                 with_vars tys env ~f:(fun vars env -> vars, aux env rhs)
                      *)
              )
              m
          in
          A.match_ u m
        | Builtin b ->
          begin match b with
            | B_not t -> A.not_ (aux env t)
            | B_and (a,b) -> A.and_ (aux env a) (aux env b)
            | B_or (a,b) -> A.or_ (aux env a) (aux env b)
            | B_eq (a,b) -> A.eq (aux env a) (aux env b)
            | B_imply (a,b) -> A.imply (aux env a) (aux env b)
          end
      in aux DB_env.empty t
  end

  (** {2 Result} *)

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

  module Model_build : sig
    val make: unit -> model

    val check : model -> unit
  end = struct
    module ValueListMap = CCMap.Make(struct
        type t = Term.t list (* normal forms *)
        let compare = CCOrd.list_ Term.compare
      end)

    type doms = {
      dom_of_ty: ID.t list Ty.Tbl.t; (* uninterpreted type -> domain elements *)
      dom_of_class: term Term.Tbl.t; (* representative -> normal form *)
      dom_of_cst: term Cst.Tbl.t; (* cst -> its normal form *)
      dom_of_fun: term ValueListMap.t Cst.Tbl.t; (* function -> args -> normal form *)
      dom_traversed: unit Term.Tbl.t; (* avoid cycles *)
    }

    let create_doms() : doms =
      { dom_of_ty=Ty.Tbl.create 32;
        dom_of_class = Term.Tbl.create 32;
        dom_of_cst=Cst.Tbl.create 32;
        dom_of_fun=Cst.Tbl.create 32;
        dom_traversed=Term.Tbl.create 128;
      }

    (* pick a term belonging to this type.
       we just generate a new constant, as picking true/a constructor might
       refine the partial model into an unsatisfiable state. *)
    let pick_default ~prefix (doms:doms)(ty:Ty.t) : term =
      (* introduce a fresh constant for this equivalence class *)
      let elts = Ty.Tbl.get_or ~or_:[] doms.dom_of_ty ty in
      let cst = ID.makef "%s%s_%d" prefix (Ty.mangle ty) (List.length elts) in
      let nf = Term.const (Cst.make_undef cst ty) in
      Ty.Tbl.replace doms.dom_of_ty ty (cst::elts);
      nf

    (* follow "normal form" pointers deeply in the term *)
    let deref_deep (doms:doms) (t:term) : term =
      let rec aux t =
        let repr = (CC.find t :> term) in
        (* if not already done, traverse all parents to update the functions'
           models *)
        if not (Term.Tbl.mem doms.dom_traversed repr) then (
          Term.Tbl.add doms.dom_traversed repr ();
          Bag.to_seq repr.term_parents |> Sequence.iter aux_ignore;
        );
        (* find a normal form *)
        let nf: term =
          begin match CC.normal_form t with
            | Some (NF_bool true) -> Term.true_
            | Some (NF_bool false) -> Term.false_
            | Some (NF_cstor (cstor, args)) ->
              (* cstor applied to sub-normal forms *)
              Term.app_cst cstor.cstor_cst (IArray.map aux args)
            | None ->
              let repr = (CC.find t :> term) in
              begin match Term.Tbl.get doms.dom_of_class repr with
                | Some u -> u
                | None when Ty.is_uninterpreted t.term_ty ->
                  let nf = pick_default ~prefix:"$" doms t.term_ty in
                  Term.Tbl.add doms.dom_of_class repr nf;
                  nf
                | None ->
                  let nf = pick_default ~prefix:"?" doms t.term_ty in
                  Term.Tbl.add doms.dom_of_class repr nf;
                  nf
              end
          end
        in
        (* update other tables *)
        begin match t.term_cell with
          | True | False -> assert false (* should have normal forms *)
          | Fun _ | DB _ | Mu _
            -> ()
          | Builtin b -> ignore (Term.map_builtin aux b)
          | If (a,b,c) -> aux_ignore a; aux_ignore b; aux_ignore c
          | App_ho (f, l) -> aux_ignore f; List.iter aux_ignore l
          | Case (t, m) -> aux_ignore t; ID.Map.iter (fun _ rhs -> aux_ignore rhs) m
          | App_cst (f, a) when IArray.is_empty a ->
            (* remember [f := c] *)
            Cst.Tbl.replace doms.dom_of_cst f nf
          | App_cst (f, a) ->
            (* remember [f a := c] *)
            let a_values = IArray.map aux a |> IArray.to_list in
            let map =
              Cst.Tbl.get_or ~or_:ValueListMap.empty doms.dom_of_fun f
            in
            Cst.Tbl.replace doms.dom_of_fun f (ValueListMap.add a_values nf map)
        end;
        nf
      and aux_ignore t =
        ignore (aux t)
      in
      aux t

    (* TODO: maybe we really need a notion of "Undefined" that is
             also not a domain element (i.e. equality not defined on it)
             + some syntax for it *)

    (* build the model of a function *)
    let model_of_fun (doms:doms) (c:cst): Ast.term =
      let ty_args, ty_ret = Ty.unfold (Cst.ty c) in
      assert (ty_args <> []);
      let vars =
        List.mapi
          (fun i ty -> Ast.Var.make (ID.makef "x_%d" i) (Conv.ty_to_ast ty))
          ty_args
      in
      let default = match ty_ret.ty_cell with
        | Prop -> Ast.true_ (* should be safe: we would have split it otherwise *)
        | _ ->
          (* TODO: what about other finites types? *)
          pick_default ~prefix:"?" doms ty_ret |> Conv.term_to_ast
      in
      let cases =
        Cst.Tbl.get_or ~or_:ValueListMap.empty doms.dom_of_fun c
        |> ValueListMap.to_list
        |> List.map
          (fun (args,rhs) ->
             assert (List.length ty_args = List.length vars);
             let tests =
               List.map2
                 (fun v arg -> Ast.eq (Ast.var v) (Conv.term_to_ast arg))
                 vars args
             in
             Ast.and_l tests, Conv.term_to_ast rhs)
      in
      (* decision tree for the body *)
      let body =
        List.fold_left
          (fun else_ (test, then_) -> Ast.if_ test then_ else_)
          default cases
      in
      Ast.fun_l vars body

    let make () : model =
      let env = !model_env_ in
      let doms = create_doms () in
      (* compute values of meta variables *)
      let consts =
        !model_support_
        |> Sequence.of_list
        |> Sequence.filter_map
          (fun c ->
             if Ty.is_arrow (Cst.ty c) then None
             else
               (* find normal form of [c] *)
               let t = Term.const c in
               let t = deref_deep doms t |> Conv.term_to_ast in
               Some (c.cst_id, t))
        |> ID.Map.of_seq
      in
      (* now compute functions (the previous "deref_deep" have updated their use cases)  *)
      let consts =
        !model_support_
        |> Sequence.of_list
        |> Sequence.filter_map
          (fun c ->
             if Ty.is_arrow (Cst.ty c)
             then (
               let t = model_of_fun doms c in
               Some (c.cst_id, t)
             ) else None)
        |> ID.Map.add_seq consts
      in
      (* now we can convert domains *)
      let domains =
        Ty.Tbl.to_seq doms.dom_of_ty
        |> Sequence.filter_map
          (fun (ty,dom) ->
             if Ty.is_uninterpreted ty
             then Some (Conv.ty_to_ast ty, List.rev dom)
             else None)
        |> Ast.Ty.Map.of_seq
      (* and update env: add every domain element to it *)
      and env =
        Ty.Tbl.to_seq doms.dom_of_ty
        |> Sequence.flat_map_l (fun (_,dom) -> dom)
        |> Sequence.fold
          (fun env id -> Ast.env_add_def env id Ast.E_uninterpreted_cst)
          env
      in
      Model.make ~env ~consts ~domains

    let check m =
      Log.debugf 1 (fun k->k "checking model…");
      Log.debugf 5 (fun k->k "(@[<1>candidate model: %a@])" Model.pp m);
      let goals =
        Top_goals.to_seq
        |> Sequence.map Conv.term_to_ast
        |> Sequence.to_list
      in
      Model.check m ~goals
  end

  (** {2 Main} *)

  let clause_of_mclause (c:M.St.clause): Clause.t =
    M.Proof.to_list c |> List.map (fun a -> a.M.St.lit) |> Clause.make

  (* convert unsat-core *)
  let clauses_of_unsat_core (core:M.St.clause list): Clause.t Sequence.t =
    Sequence.of_list core
    |> Sequence.map clause_of_mclause

  (* print all terms reachable from watched literals *)
  let pp_term_graph _out () =
    ()

  let pp_stats out () : unit =
    Format.fprintf out
      "(@[<hv1>stats@ \
       :num_expanded %d@ \
       :num_uty_expanded %d@ \
       :num_clause_push %d@ \
       :num_clause_tautology %d@ \
       :num_propagations %d@ \
       :num_unif %d@ \
       @])"
      !stat_num_cst_expanded
      !stat_num_uty_expanded
      !stat_num_clause_push
      !stat_num_clause_tautology
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

  type unsat_core = M.St.clause list

  (* find, in the UNSAT core, a term to expand, or [None] otherwise.
     This will pick the oldest unexpanded term that also belongs to the core *)
  let find_to_expand (core: unsat_core): Terms_to_expand.t option =
    clauses_of_unsat_core core
    |> Sequence.flat_map Clause.to_seq
    |> Sequence.filter_map
      (fun lit -> match Lit.view lit with
         | Lit_expanded t -> Terms_to_expand.find t
         | _ -> None)
    |> Sequence.max
      ~lt:(fun a b -> a.Terms_to_expand.timestamp < b.Terms_to_expand.timestamp)

  (* TODO: max_depth should actually correspond to the maximum depth
     of un-expanded terms (expand in body of t --> depth = depth(t)+1),
     so it corresponds to unfolding call graph to some depth *)

  let solve ?(on_exit=[]) ?(check=true) () =
    let n_iter = ref 0 in
    let rec check_cc (): res =
      assert (Backtrack.at_level_0 ());
      if !n_iter > Config.max_depth then Unknown U_max_depth (* exceeded limit *)
      else begin match CC.check () with
        | CC.Unsat _ -> Unsat (* TODO proof *)
        | CC.Sat lemmas  ->
          add_cc_lemmas lemmas;
          check_solver()
      end

    and check_solver (): res =
      (* assume all literals [expanded t] are false *)
      let assumptions =
        Terms_to_expand.to_seq
        |> Sequence.map (fun {Terms_to_expand.lit; _} -> Lit.neg lit)
        |> Sequence.to_rev_list
      in
      incr n_iter;
      Log.debugf 2
        (fun k->k
            "(@[<1>@{<Yellow>solve@}@ @[:with-assumptions@ (@[%a@])@ n_iter: %d]@])"
            (Utils.pp_list Lit.pp) assumptions !n_iter);
      begin match M.solve ~assumptions() with
        | M.Sat _ ->
          Log.debugf 1 (fun k->k "@{<Yellow>** found SAT@}");
          do_on_exit ~on_exit;
          let m = Model_build.make () in
          if check then Model_build.check m;
          Sat m
        | M.Unsat us ->
          let p = us.SI.get_proof () in
          Log.debugf 4 (fun k->k "proof: @[%a@]@." pp_proof p);
          let core = p |> M.unsat_core in
          (* check if unsat because of assumptions *)
          expand_next core
      end

    (* pick a term to expand, or UNSAT *)
    and expand_next (core:unsat_core) =
      begin match find_to_expand core with
        | None -> Unsat (* TODO proof *)
        | Some to_expand ->
          let t = to_expand.Terms_to_expand.term in
          Log.debugf 2 (fun k->k "(@[<1>@{<green>expand_next@}@ :term %a@])" Term.pp t);
          CC.expand_term t;
          Terms_to_expand.remove t;
          Clause.push_new (Clause.make [to_expand.Terms_to_expand.lit]);
          Backtrack.backtrack_to_level_0 ();
          check_cc () (* recurse *)
      end
    in
    check_cc()
end

