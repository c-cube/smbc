
(* This file is free software. See file "license" for more details. *)

let get_time : unit -> float =
  let start = Unix.gettimeofday() in
  fun () ->
    Unix.gettimeofday() -. start

module M_lit = Minisat.Lit

type minisat_clause = M_lit.t list

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
  let stat_num_propagations = ref 0
  let stat_num_clause_tautology = ref 0
  let stat_num_equiv_lemmas = ref 0
  let stat_num_calls_minisat = ref 0

  (** {2 Timestamps: number of calls to Minisat} *)
  module Timestamp : sig
    type t = private int
    val zero : t
    val cur : unit -> t
    val incr : unit -> unit (* increment time *)
    val pp : t CCFormat.printer
  end = struct
    type t = int
    let n_ = ref 1
    let zero = 0
    let cur() = !n_
    let incr () =
      Log.debugf 4 (fun k->k "(@[incr_timestamp@ old: %d@])" !n_);
      incr n_;
      ()
    let pp = Format.pp_print_int
  end

  (* for objects that are expanded on demand only *)
  type 'a lazily_expanded =
    | Lazy_none
    | Lazy_some of 'a

  (* main term cell *)
  type term = {
    mutable term_id: int; (* unique ID *)
    mutable term_ty: ty_h;
    term_cell: term_cell;
    mutable term_nf: (term * explanation * Timestamp.t) option;
      (* normal form + explanation of why + timestamp *)
    mutable term_deps: term_dep list;
    (* set of undefined constants
       that can make evaluation go further *)
    mutable term_proxy: term_proxy option;
    (* forward evaluation to this proxy? *)
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
    | Match of term * (ty_h list * term) ID.Map.t
    | Switch of term * switch_cell (* function table *)
    | Quant of quant * ty_uninterpreted_slice * term
      (* quantification on finite types *)
    | Builtin of builtin
    | Proxy of term_proxy (* boolean literal standing for some (boolean) term *)

  and db = int * ty_h

  and quant =
    | Forall
    | Exists

  (* what can block evaluation of a term *)
  and term_dep =
    | Dep_cst of cst
      (* blocked by non-refined constant *)
    | Dep_uty of ty_uninterpreted_slice
      (* blocked because this type is not expanded enough *)
    | Dep_proxy of term_proxy
      (* blocked by this propositional literal *)

  and builtin =
    | B_not of term
    | B_eq of term * term
    | B_and of term list
    | B_or of term list
    | B_imply of term * term
    | B_equiv of term * term

  (* boolean proxy. This pairs a term (of type prop) and a boolean literal,
     such that the value of the term is determined by the value of
     the literal in Minisat's current model. However, evaluation
     also needs to check the proxy's consistency.

     Consistency, for a proxy, means that either:
     - [Proxy_subs l]: its sub-proxies [l] are consistent
     - [Proxy_self]: the proxified term evaluates to the same value
       as the proxy was decided (true/false) *)
  and term_proxy = {
    proxy_for: term;
    (* the term this is standing for *)
    proxy_deps: term_proxy_deps;
    (* other proxies to check consistency of *)
    proxy_atom: atom lazy_t;
    (* the boolean atom. *)
    mutable proxy_expanded: bool;
    (* did we already expand this into CNF? *)
    mutable proxy_last_checked: Timestamp.t;
    (* last time we checked this proxy's consistency *)
    mutable proxy_graph: proxy_graph_edge list;
    (* list of other boolean terms that are linked to this one *)
  }

  and term_proxy_deps =
    | Proxy_self
    | Proxy_subs of term_proxy list

    (* edge of the boolean graph: destination + kind of edge *)
  and proxy_graph_edge = term_proxy * proxy_graph_edge_kind

  and proxy_graph_edge_kind =
    | GE_conditional (* linked by CNF *)
    | GE_equiv of explanation (* equivalent to this other terms under assumptions *)

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

  (* boolean atom (without a sign) *)
  and atom = {
    mutable atom_id: int; (* unique ID *)
    atom_view: atom_view;
  }

  and atom_view =
    | Atom_fresh of ID.t (* fresh literals *)
    | Atom_assert of term_proxy
    | Atom_assign of cst * term
    | Atom_uty_empty of ty_uninterpreted_slice

  (* boolean literal: atom + sign. Belongs in a boolean clause. *)
  and lit = {
    lit_atom: atom;
    lit_sign: bool;
  }

  and cst = {
    cst_id: ID.t;
    cst_kind: cst_kind;
  }

  and cst_kind =
    | Cst_undef of ty_h * cst_info * ty_uninterpreted_slice option
    | Cst_cstor of ty_h
    | Cst_uninterpreted_dom_elt of ty_h (* uninterpreted domain constant *)
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
    mutable cst_cases_lits: lit list lazily_expanded;
    (* literals obtained from [cst_cases].
       invariant: [c.cst_cases_lits = List.map (Lit.cst_choice c) c.cst_cases] *)
    mutable cst_complete: bool;
    (* does [cst_cases] cover all possible cases, or only
       a subset? Affects completeness *)
  }

  (* this is a disjunction of sufficient conditions for the existence of
     some meta (cst). Each condition is a literal. *)
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
    mutable uty_lit_empty: lit lazily_expanded;
    (* boolean literal corresponding to this slice being empty.
       Invariant: Lazy_none iif uty_pair = Lazy_none*)
  }

  (* environment for evaluation: not-yet-evaluated terms *)
  type eval_env = term db_env

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

    let is_arrow t =
      match t.ty_cell with | Arrow _ -> true | _ -> false

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

    let is_empty e = e.db_size = 0
    let equal eq_x e1 e2 =
      e1.db_size = e2.db_size
      && CCList.equal (CCOpt.equal eq_x) e1.db_st e2.db_st
    let to_list e = e.db_st
    let hash h e = Hash.(list (opt h)) e.db_st
    let push x env = { db_size=env.db_size+1; db_st=Some x :: env.db_st }
    let push_l l env = List.fold_left (fun e x -> push x e) env l
    let push_none env =
      { db_size=env.db_size+1; db_st=None::env.db_st }
    let push_none_l l env = List.fold_left (fun e _ -> push_none e) env l
    let map f e = {e with db_st = List.map f e.db_st }
    let mapi f e = {e with db_st = List.mapi f e.db_st }
    let empty = {db_st=[]; db_size=0}
    let of_list l = push_l l empty
    let singleton x = {db_st=[Some x]; db_size=1}
    let take n e =
      if n >= e.db_size then e
      else { db_size=n; db_st=CCList.take n e.db_st}
    let append e1 e2 =
      { db_size=e1.db_size+e2.db_size; db_st = e1.db_st @ e2.db_st }
    let size env = env.db_size
    let get ((n,_):DB.t) env : _ option =
      if n < env.db_size then List.nth env.db_st n else None

    let pp pp_x out e =
      let l =
        e.db_st
        |> List.mapi (fun i o -> i,o)
        |> CCList.filter_map
          (function (_,None) -> None | (i,Some x) -> Some (i,x))
      in
      match l with
        | [] -> ()
        | _ ->
          let pp_pair out (i,x) =
            Format.fprintf out "@[%d: %a@]" i pp_x x
          in
          CCFormat.list ~start:"" ~stop:"" ~sep:"," pp_pair out l
  end

  let term_equal_ a b = a==b
  let term_hash_ a = a.term_id
  let term_cmp_ a b = CCOrd.int_ a.term_id b.term_id

  module Typed_cst = struct
    type t = cst

    let id t = t.cst_id
    let kind t = t.cst_kind

    let ty_of_kind = function
      | Cst_defined (ty, _)
      | Cst_undef (ty, _, _)
      | Cst_uninterpreted_dom_elt ty
      | Cst_cstor ty -> ty

    let ty t = ty_of_kind t.cst_kind

    let make cst_id cst_kind = {cst_id; cst_kind}
    let make_cstor id ty =
      let _, ret = Ty.unfold ty in
      assert (Ty.is_data ret);
      make id (Cst_cstor ty)
    let make_defined id ty t = make id (Cst_defined (ty, t))
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
          cst_cases_lits=Lazy_none;
          cst_complete=false;
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

  let pp_uty out uty =
    let n = uty.uty_offset in
    let lazy ty = uty.uty_self in
    if n=0
    then Format.fprintf out "%a[:]" Ty.pp ty
    else Format.fprintf out "%a[%d:]" Ty.pp ty n

  let pp_uty_status out = function
    | Uty_empty -> CCFormat.string out "empty"
    | Uty_nonempty -> CCFormat.string out "non_empty"

  let hash_proxy_ (p:term_proxy) = Hash.combine2 40 (term_hash_ p.proxy_for)

  let eq_proxy_ p1 p2 = term_equal_ p1.proxy_for p2.proxy_for

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
          | Match (u,m) ->
            let hash_case (tys,rhs) =
              Hash.combine2 (Hash.list Ty.hash tys) rhs.term_id
            in
            let hash_m =
              Hash.seq (Hash.pair ID.hash hash_case) (ID.Map.to_seq m)
            in
            Hash.combine3 8 u.term_id hash_m
          | Builtin (B_not a) -> Hash.combine2 20 a.term_id
          | Builtin (B_and l) -> Hash.combine2 21 (Hash.list sub_hash l)
          | Builtin (B_or l) -> Hash.combine2 22 (Hash.list sub_hash l)
          | Builtin (B_imply (t1,t2)) -> Hash.combine3 23 t1.term_id t2.term_id
          | Builtin (B_equiv (t1,t2)) -> Hash.combine3 24 t1.term_id t2.term_id
          | Builtin (B_eq (t1,t2)) -> Hash.combine3 25 t1.term_id t2.term_id
          | Mu sub -> Hash.combine sub_hash 30 sub
          | Switch (t, tbl) ->
            Hash.combine3 31 (sub_hash t) tbl.switch_id
          | Quant (q,ty,bod) ->
            Hash.combine4 32 (Hash.poly q) (hash_uty ty) (sub_hash bod)
          | Proxy p -> hash_proxy_ p

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
              | B_and l1, B_and l2
              | B_or l1, B_or l2 -> CCList.equal term_equal_ l1 l2
              | B_eq (a1,b1), B_eq (a2,b2)
              | B_equiv (a1,b1), B_equiv (a2,b2)
              | B_imply (a1,b1), B_imply (a2,b2) -> a1 == a2 && b1 == b2
              | B_not _, _ | B_and _, _ | B_eq _, _
              | B_or _, _ | B_imply _, _ | B_equiv _, _ -> false
            end
          | Mu t1, Mu t2 -> t1==t2
          | Quant (q1,ty1,bod1), Quant (q2,ty2,bod2) ->
            q1=q2 && equal_uty ty1 ty2 && bod1==bod2
          | Proxy p1, Proxy p2 -> eq_proxy_ p1 p2
          | True, _
          | False, _
          | DB _, _
          | Const _, _
          | App _, _
          | Fun _, _
          | If _, _
          | Match _, _
          | Builtin _, _
          | Mu _, _
          | Switch _, _
          | Quant _, _
          | Proxy _, _
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
        term_proxy=None;
      } in
      H.hashcons t

    let true_ = mk_bool_ true
    let false_ = mk_bool_ false

    type deps =
      | Term_dep_cst of cst (* the term itself is a constant *)
      | Term_dep_none
      | Term_dep_sub of term
      | Term_dep_sub2 of term * term
      | Term_dep_subs of term list
      | Term_dep_uty of ty_uninterpreted_slice
      | Term_dep_proxy of term_proxy

    type delayed_ty =
      | DTy_direct of ty_h
      | DTy_lazy of (unit -> ty_h)

    (* TODO: remove this? *)
    let sorted_merge_ l1 l2 = CCList.sorted_merge_uniq ~cmp:compare l1 l2

    let cmp_term_dep_ a b =
      let to_int_ = function
        | Dep_cst _ -> 0
        | Dep_uty _ -> 1
        | Dep_proxy _ -> 2
      in
      match a, b with
      | Dep_cst c1, Dep_cst c2 -> Typed_cst.compare c1 c2
      | Dep_uty u1, Dep_uty u2 ->
        let (<?>) = CCOrd.(<?>) in
        Ty.compare (Lazy.force u1.uty_self) (Lazy.force u2.uty_self)
        <?> (CCOrd.int_, u1.uty_offset, u2.uty_offset)
      | Dep_proxy t1, Dep_proxy p2 -> term_cmp_ t1.proxy_for p2.proxy_for
      | Dep_cst _, _
      | Dep_uty _, _
      | Dep_proxy _, _ -> CCOrd.int_ (to_int_ a) (to_int_ b)

    (* build a term. If it's new, add it to the watchlist
       of every member of [watching] *)
    let mk_term_ ~(deps:deps) cell ~(ty:delayed_ty) : term =
      let t = {
        term_id= -1;
        term_ty=Ty.prop; (* will be changed *)
        term_cell=cell;
        term_nf=None;
        term_deps=[];
        term_proxy=None;
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
          | Term_dep_subs l ->
            CCList.flat_map (fun t->t.term_deps) l
            |> CCList.sort_uniq ~cmp:cmp_term_dep_
          | Term_dep_uty uty -> [Dep_uty uty]
          | Term_dep_proxy p -> [Dep_proxy p]
        in
        t'.term_deps <- deps
      );
      t'

    let db d =
      mk_term_ ~deps:Term_dep_none (DB d) ~ty:(DTy_direct (DB.ty d))

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
      let mk b = mk_term_ ~deps (Builtin b) ~ty:(DTy_direct Ty.prop) in
      begin match b with
        | B_eq (a,b) when a.term_id > b.term_id -> B_eq (b,a) |> mk
        | B_and l ->
          let l =
            CCList.flat_map
              (fun sub -> match sub.term_cell with
                 | True -> []
                 | Builtin (B_and l') -> l'
                 | _ -> [sub])
              l
          in
          begin match l with
            | [] -> true_
            | [t] -> t
            | _ -> B_and l |> mk
          end
        | B_or l ->
          let l =
            CCList.flat_map
              (fun sub -> match sub.term_cell with
                 | False -> []
                 | Builtin (B_or l') -> l'
                 | _ -> [sub])
              l
          in
          begin match l with
            | [] -> false_
            | [t] -> t
            | _ -> B_or l |> mk
          end
        | B_equiv (a,b) when a.term_id > b.term_id -> B_equiv (b,a) |> mk
        | _ -> mk b
      end

    let builtin b =
      let deps = match b with
        | B_not u -> Term_dep_sub u
        | B_and l | B_or l -> Term_dep_subs l
        | B_equiv (a,b) | B_imply (a,b) | B_eq (a,b) -> Term_dep_sub2 (a,b)
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

    let abs_fst (t:t): t = fst (abs t)

    let quant q uty body =
      assert (Ty.is_prop body.term_ty);
      (* evaluation is blocked by the uninterpreted type *)
      let deps = Term_dep_uty uty in
      mk_term_ ~deps ~ty:(DTy_direct Ty.prop) (Quant (q,uty,body))

    let proxy p =
      assert (Ty.is_prop p.proxy_for.term_ty);
      mk_term_ ~deps:(Term_dep_proxy p) ~ty:(DTy_direct Ty.prop) (Proxy p)

    let forall = quant Forall
    let exists = quant Exists

    let and_ l = builtin (B_and l)
    let or_ l = builtin (B_or l)
    let imply a b = builtin (B_imply (a,b))
    let equiv a b = builtin (B_equiv (a,b))
    let eq a b =
      assert (not (Ty.is_prop a.term_ty));
      builtin (B_eq (a,b))
    let neq a b = not_ (eq a b)

    let is_const t = match t.term_cell with
      | Const _ -> true
      | _ -> false

    let map_builtin f b = match b with
      | B_not t -> B_not (f t)
      | B_and l -> B_and (List.map f l)
      | B_or l -> B_or (List.map f l)
      | B_equiv (a,b) -> B_equiv (f a, f b)
      | B_eq (a,b) -> B_eq (f a, f b)
      | B_imply (a,b) -> B_imply (f a, f b)

    let builtin_to_seq b yield = match b with
      | B_not t -> yield t
      | B_and l
      | B_or l -> List.iter yield l
      | B_imply (a,b)
      | B_equiv (a,b)
      | B_eq (a,b) -> yield a; yield b

    let ty t = t.term_ty

    let equal = term_equal_
    let hash = term_hash_
    let compare = term_cmp_

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
          | Match (t, m) ->
            aux t;
            ID.Map.iter (fun _ (_,rhs) -> aux rhs) m
          | Switch (u,_) -> aux u (* ignore the table *)
          | Builtin b -> builtin_to_seq b aux
          | Quant (_, _, body)
          | Mu body
          | Fun (_, body) -> aux body
          | Proxy _ -> ()
      in
      aux t

    let is_neg_ t = match t.term_cell with
      | Builtin (B_not _)
      | False -> true
      | _ -> false

    let is_blocked_by (t:t) ~(dep:term_dep): bool =
      List.exists
        (fun d' -> cmp_term_dep_ d' dep = 0)
        t.term_deps

    (* return [Some] iff the term is an undefined constant *)
    let as_cst_undef (t:term):
      (cst * Ty.t * cst_info * ty_uninterpreted_slice option) option
      =
      match t.term_cell with
        | Const c -> Typed_cst.as_undefined c
        | _ -> None

    let as_proxy (t:term): term_proxy option =
      match t.term_cell with
        | Proxy p -> Some p
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
        | Quant (q,uty,f) ->
          fpf out "(@[%a %a@ %a@])" pp_quant q pp_uty uty pp f
        | Mu sub -> fpf out "(@[mu@ %a@])" pp sub
        | If (a, b, c) ->
          fpf out "(@[if %a@ %a@ %a@])" pp a pp b pp c
        | Match (t,m) ->
          let pp_bind out (id,(_tys,rhs)) =
            fpf out "(@[<1>case@ %a@ %a@])" ID.pp id pp rhs
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
        | Builtin (B_not t) -> fpf out "(@[<hv1>not@ %a@])" pp t
        | Builtin (B_and l) ->
          fpf out "(@[<hv1>and@ %a@])" (Utils.pp_list pp) l
        | Builtin (B_or l) ->
          fpf out "(@[<hv1>or@ %a@])" (Utils.pp_list pp) l
        | Builtin (B_imply (a,b)) ->
          fpf out "(@[<hv1>=>@ %a@ %a@])" pp a pp b
        | Builtin (B_equiv (a,b)) ->
          fpf out "(@[<hv1>=@ %a@ %a@])" pp a pp b
        | Builtin (B_eq (a,b)) ->
          fpf out "(@[<hv1>=@ %a@ %a@])" pp a pp b
        | Proxy p ->
          fpf out "(@[<1>proxy@ %a@])" pp p.proxy_for
      in
      pp out t

    let pp = pp_top ~ids:true

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
          | Proxy p ->
            proxy p (* NOTE: should be closed *)
        and aux_l env l =
          List.map (aux env) l
        in
        aux env t
      )

    (* simplify: evaluate without following current values of constants, boolean
       expressions, etc. That is, compute the unconditional normal form
       (the one in an empty SAT trail) *)
    let rec simplify (t:term): term =
      match t.term_cell with
        | DB _ | True | False -> t
        | Const c ->
          begin match c.cst_kind with
            | Cst_defined (_, rhs) ->
              (* expand defined constants, and only them *)
              simplify (Lazy.force rhs)
            | Cst_undef _ | Cst_uninterpreted_dom_elt _ | Cst_cstor _ -> t
          end
        | Fun _ -> t (* no eval under lambda *)
        | Mu body ->
          (* [mu x. body] becomes [body[x := mu x. body]] *)
          let env = DB_env.singleton t in
          eval_db env body
        | Quant _ -> t
        | Builtin b ->
          let b' = map_builtin simplify b in
          begin match b' with
            | B_not {term_cell=True; _} -> false_
            | B_not {term_cell=False; _} -> true_
            | B_not t' -> not_ (simplify t')
            | B_equiv ({term_cell=True; _}, a)
            | B_equiv (a, {term_cell=True; _}) -> a
            | B_equiv ({term_cell=False; _}, a)
            | B_equiv (a, {term_cell=False; _}) -> not_ a
            | B_imply ({term_cell=True; _}, a) -> a
            | B_imply (a, {term_cell=False; _}) -> not_ a
            | B_imply (_, {term_cell=True; _})
            | B_imply ({term_cell=False; _}, _) -> true_
            | B_eq (a,b) when equal a b -> true_
            | B_and l when CCList.Set.mem ~eq:equal false_ l -> false_
            | B_or l when CCList.Set.mem ~eq:equal true_ l -> true_
            | _ -> builtin b'
          end
        | If (a,b,c) ->
          let a' = simplify a in
          let default() =
            if a==a' then t else if_ a' b c
          in
          begin match a'.term_cell with
            | True -> simplify b
            | False -> simplify c
            | _ -> default()
          end
        | Match (u, m) ->
          let u' = simplify u in
          let default() =
            if u==u' then t else match_ u' m
          in
          begin match as_cstor_app u' with
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
                    simplify rhs
                  )
                  else default()
                with Not_found -> assert false
              end
            | None -> default()
          end
        | Switch (u, m) ->
          let u' = simplify u in
          begin match as_domain_elt u' with
            | Some (c_elt,_) ->
              (* do a lookup for this value! *)
              let rhs =
                match ID.Tbl.get m.switch_tbl c_elt.cst_id with
                  | Some rhs -> rhs
                  | None ->
                    (* add an entry, by generating a new RHS *)
                    let rhs = m.switch_make_new () in
                    ID.Tbl.add m.switch_tbl c_elt.cst_id rhs;
                    rhs
              in
              (* continue evaluation *)
              simplify rhs
            | None ->
              (* block again *)
              if u==u' then t else switch u' m
          end
        | App ({term_cell=Const {cst_kind=Cst_cstor _; _}; _}, _) ->
          t (* do not reduce under cstors *)
        | App (f, l) ->
          let f' = simplify f in
          (* now beta-reduce if needed *)
          simplify_app DB_env.empty f' l
        | Proxy _ -> t

    and simplify_app env f l = match f.term_cell, l with
      | Const {cst_kind=Cst_defined (_, lazy def_f); _}, l ->
        (* reduce [f l] into [def_f l] when [f := def_f] *)
        simplify_app env def_f l
      | Fun (_ty, body), arg :: other_args ->
        (* beta-reduce *)
        assert (Ty.equal _ty arg.term_ty);
        let new_env = DB_env.push arg env in
        (* apply [body] to [other_args] *)
        simplify_app new_env body other_args
      | _ ->
        (* cannot reduce, unless [f] reduces to something else. *)
        let f' = eval_db env f |> simplify in
        if equal f f'
        then app f' l (* no more reduction *)
        else simplify_app DB_env.empty f' l (* try it again *)
  end

  let pp_proxy_ out p =
    Format.fprintf out "(@[<1>proxy@ %a@])" Term.pp p.proxy_for

  module Atom : sig
    type t = atom

    val make : atom_view -> t
    (** Make an atom for this view.
        Assume the view is normalized:

        - [Atom_assert t]: [t] must be simplified and positive
    *)

    val mlit : t -> M_lit.t
    (** Unique Minisat literal for this boolean atom *)

    val view : t -> atom_view
    val id : t -> int
    val num_atoms: unit -> int
    val all_atoms : unit -> t list
    val equal : t -> t -> bool
    val hash : t -> int
    val compare : t -> t -> int
    val pp : t CCFormat.printer
  end = struct
    type t = atom

    module H = Hashcons.Make(struct
        type t = atom

        let equal a b = match a.atom_view, b.atom_view with
          | Atom_fresh i1, Atom_fresh i2 -> ID.equal i1 i2
          | Atom_assign (c1,t1), Atom_assign (c2,t2) ->
            Typed_cst.equal c1 c2 && t1 == t2
          | Atom_uty_empty u1, Atom_uty_empty u2 -> cmp_uty u1 u2=0
          | Atom_assert p1, Atom_assert p2 -> Term.equal p1.proxy_for p2.proxy_for
          | Atom_fresh _, _
          | Atom_assign _, _
          | Atom_uty_empty _, _
          | Atom_assert _, _ -> false

        let hash a = match a.atom_view with
          | Atom_fresh i -> Hash.combine2 331 (ID.hash i)
          | Atom_assign (c,t) ->
            Hash.combine3 332 (Typed_cst.hash c) (term_hash_ t)
          | Atom_uty_empty uty -> Hash.combine2 333 (hash_uty uty)
          | Atom_assert p ->
            Hash.combine2 334 (term_hash_ p.proxy_for)

        let set_id a i = a.atom_id <- (i+1) (* avoid 0 *)
      end)

    (* keep a list of all atoms, to prevent them from being garbage collected
       (which would make a given term map to several literals, duplicating
       search effort) *)
    let all_atoms_ : t list ref = ref []

    let num_atoms() = List.length !all_atoms_
    let all_atoms() = !all_atoms_

    let make v =
      assert (match v with
        | Atom_assert p ->
          let t = p.proxy_for in
          not (Term.is_neg_ t) && Term.equal t (Term.simplify t)
        | _ -> true);
      let a0 = {atom_id= -1; atom_view=v; } in
      let a = H.hashcons a0 in
      (* [a] is new? then prevent it from being GC'd *)
      if a==a0 then (
        CCList.Ref.push all_atoms_ a;
      );
      a

    let mlit a = M_lit.make a.atom_id

    let id a = a.atom_id
    let view a = a.atom_view
    let equal a b = a.atom_id = b.atom_id
    let compare a b = CCOrd.int_ a.atom_id b.atom_id
    let hash a = a.atom_id

    let pp_inner out a = match a.atom_view with
      | Atom_fresh i -> Format.fprintf out "#%a" ID.pp i
      | Atom_assert p -> Term.pp out p.proxy_for
      | Atom_assign (c,t) ->
        Format.fprintf out "(@[:= %a@ %a@])" Typed_cst.pp c Term.pp t
      | Atom_uty_empty u -> Format.fprintf out "(empty %a)" pp_uty u

    let pp out a =
      pp_inner out a;
      if Config.pp_hashcons then Format.fprintf out "/%d" a.atom_id;
      ()
  end

  (* turn [t] into a proxy + sign *)
  let rec proxify (t:term): term_proxy * bool =
    assert (Ty.is_prop t.term_ty);
    (* simplify, remove sign *)
    let t = Term.simplify t in
    let t_abs, sign = Term.abs t in
    match t_abs.term_proxy with
      | Some p -> p, sign
      | None ->
        (* only need to evaluate sub-proxies for boolean connectives *)
        let deps = match t_abs.term_cell with
          | Builtin (B_and l | B_or l) ->
            Proxy_subs (List.map proxify_abs l)
          | Builtin (B_imply (a,b) | B_equiv (a,b)) ->
            Proxy_subs [proxify_abs a; proxify_abs b]
          | _ -> Proxy_self
        in
        (* [p], the proxy, refers to itself through its atom *)
        let rec p = {
          proxy_for=t_abs;
          proxy_atom=lazy (Atom.make (Atom_assert p));
          proxy_graph=[];
          proxy_deps=deps;
          proxy_last_checked=Timestamp.zero;
          proxy_expanded=false;
        } in
        (* have [t_abs] point to [p] *)
        t_abs.term_proxy <- Some p;
        p, sign

  (* turn [t] into a proxy, ignoring its sign *)
  and proxify_abs (t:term): term_proxy = fst (proxify t)

  (** {2 Literals} *)
  module Lit : sig
    type t = lit
    val neg : t -> t
    val abs : t -> t
    val sign : t -> bool
    val atom : t -> atom
    val atom_view : t -> atom_view
    val of_atom : atom -> t
    val map : f:(atom_view -> atom_view) -> t -> t
    val as_atom : t -> Atom.t * bool
    val as_assert : t -> (term_proxy * bool) option
    val mlit : t -> M_lit.t
    val fresh_with : ID.t -> t
    val fresh : unit -> t
    val assert_ : ?sign:bool -> term -> t
    val assert_proxy : ?sign:bool -> term_proxy -> t
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
  end = struct
    type t = lit

    let neg l = {l with lit_sign=not l.lit_sign}

    let sign t = t.lit_sign
    let atom t = t.lit_atom
    let atom_view t = Atom.view t.lit_atom

    let abs t: t = {t with lit_sign=true}

    (* build literal, normalizing on the fly *)
    let make ~sign (v:atom_view): t =
      let lit_atom = Atom.make v in
      {lit_sign=sign; lit_atom}

    let of_atom (a:atom): t = make ~sign:true a.atom_view

    (* map [f] on the view *)
    let map ~f lit =
      let v = f lit.lit_atom.atom_view in
      (* re-normalize *)
      make ~sign:lit.lit_sign v

    (* assume the ID is fresh *)
    let fresh_with id = make ~sign:true (Atom_fresh id)

    (* fresh boolean literal *)
    let fresh: unit -> t =
      let n = ref 0 in
      fun () ->
        let id = ID.makef "#fresh_%d" !n in
        incr n;
        make ~sign:true (Atom_fresh id)

    (* assert this term, or its negation *)
    let assert_ ?(sign=true) (t:term) : t =
      let p, sign' = proxify t in
      let sign = if sign' then sign else not sign in
      make ~sign (Atom_assert p)

    let assert_proxy ?(sign=true) (p:term_proxy): t =
      make ~sign (Atom_assert p)

    let eq a b = assert_ ~sign:true (Term.eq a b)
    let neq a b = assert_ ~sign:false (Term.eq a b)
    let cst_choice c t = make ~sign:true (Atom_assign (c, t))
    let uty_choice_empty uty = make ~sign:true (Atom_uty_empty uty)
    let uty_choice_nonempty uty : t = make ~sign:false (Atom_uty_empty uty)
    let uty_choice_status uty s : t = match s with
      | Uty_empty -> uty_choice_empty uty
      | Uty_nonempty -> uty_choice_nonempty uty

    let as_atom (lit:t) = lit.lit_atom, lit.lit_sign

    let as_assert (lit:t) : (term_proxy * bool) option =
      match lit.lit_atom.atom_view with
        | Atom_assert p -> Some (p, lit.lit_sign)
        | _ -> None

    let hash l = Hash.combine2 (Hash.bool l.lit_sign) (Atom.hash l.lit_atom)
    let compare a b =
      CCOrd.(bool_ a.lit_sign b.lit_sign <?> (Atom.compare, a.lit_atom, b.lit_atom))
    let equal a b = compare a b = 0

    let mlit (l:t): M_lit.t =
      let ml = Atom.mlit l.lit_atom in
      if l.lit_sign then ml else M_lit.neg ml

    let pp_lit out l =
      if l.lit_sign then Atom.pp out l.lit_atom
      else Format.fprintf out "(@[@<1>¬@ %a@])" Atom.pp l.lit_atom

    let pp = pp_lit
    let print = pp
  end

  let pp_dep out = function
    | Dep_cst c -> Typed_cst.pp out c
    | Dep_uty uty -> pp_uty out uty
    | Dep_proxy p -> Format.fprintf out "(@[proxy@ %a@])" Term.pp p.proxy_for

  module Explanation = struct
    type t = explanation
    let empty : t = E_empty
    let return e = E_leaf e
    let append s1 s2 = match s1, s2 with
      | E_empty, _ -> s2
      | _, E_empty -> s1
      | _ -> E_append (s1, s2)

    let is_empty = function
      | E_empty -> true
      | E_leaf _
      | E_append _ -> false (* by smart cstor *)

    let rec to_seq e yield = match e with
      | E_empty -> ()
      | E_leaf x -> yield x
      | E_append (a,b) -> to_seq a yield; to_seq b yield

    let to_list e =
      let rec aux acc = function
        | E_empty -> acc
        | E_leaf x -> x::acc
        | E_append (a,b) -> aux (aux acc a) b
      in
      aux [] e

    let to_list_uniq e =
      to_seq e
      |> Sequence.to_rev_list
      |> CCList.sort_uniq ~cmp:Lit.compare

    let equal a b =
      let la = to_list a in
      let lb = to_list b in
      (* double inclusion *)
      let mem l x = List.exists (fun y -> Lit.equal x y) l in
      List.for_all (mem lb) la
      && List.for_all (mem la) lb

    let pp out e =
      Format.fprintf out "(@[%a@])"
        (Utils.pp_list Lit.pp) (to_list_uniq e)
  end

  (** {2 Clauses} *)

  module Clause : sig
    type t = private {
      lits: Lit.t list;
      id: int;
    }
    val make : Lit.t list -> t
    val of_terms : term list -> t
    val lits : t -> Lit.t list
    val to_minisat : t -> minisat_clause

    val equal : t -> t -> bool
    val hash : t -> int
    val iter : (Lit.t -> unit) -> t -> unit
    val to_seq : t -> Lit.t Sequence.t
    val pp : t CCFormat.printer

    module Tbl : CCHashtbl.S with type key = t
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
          lits=l; (* CCList.sort_uniq ~cmp:Lit.compare l; *)
          id= !n_;
        } in
        incr n_;
        c

    let of_terms l =
      let l = List.map (fun t->Lit.assert_ t) l in
      make l

    let to_minisat (c:t): minisat_clause =
      List.map Lit.mlit c.lits

    let equal c1 c2 = CCList.equal Lit.equal c1.lits c2.lits
    let hash c = Hash.list Lit.hash c.lits

    let iter f c = List.iter f c.lits
    let to_seq c = Sequence.of_list c.lits

    module Tbl = CCHashtbl.Make(struct
        type t_ = t
        type t = t_
        let equal = equal
        let hash = hash
      end)
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

  module Expand : sig
    val expand_uninterpreted_slice :
      ty_uninterpreted_slice ->
      cst * ty_uninterpreted_slice * Clause.t list

    val expand_cases : cst -> Ty.t -> cst_info -> term list * Clause.t list
  end = struct
    (* make a fresh constant, with a unique name *)
    let new_cst_ =
      let n = ref 0 in
      fun ?slice ?exist_if ~parent name ty ->
        let id = ID.makef "?%s_%d" name !n in
        incr n;
        Typed_cst.make_undef ?slice ?exist_if ~parent id ty

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
            uty_lit_empty=Lazy_none;
            uty_offset=n+1;
          } in
          Log.debugf 5
            (fun k->k "expand slice %a@ into (@[%a,@ %a@])"
                pp_uty uty Typed_cst.pp c_head pp_uty uty_tail);
          (* memoize *)
          uty.uty_pair <- Lazy_some (c_head, uty_tail);
          uty.uty_lit_empty <- Lazy_some (Lit.uty_choice_empty uty);
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

  (** {2 The minisat instance} *)
  module Sat : sig
    type value = Minisat.value =
      | V_undef
      | V_true
      | V_false

    val pp_value : value CCFormat.printer

    val value : Lit.t -> value

    val value_cst : cst -> cst_info -> (Explanation.t * term) option
    (** Evaluate the given meta-variable in the model *)

    val value_uty :
      ty_uninterpreted_slice ->
      (Explanation.t * ty_uninterpreted_status) option
    (** Status of this slice in the model *)

    val value_proxy : term_proxy -> (Explanation.t * bool) option
    (** Evaluate the boolean literal in the current model *)

    val push_new : Clause.t -> unit
    (** Push a clause into a queue before it is fed to the SAT solver *)

    val push_new_l : Clause.t list -> unit
    (** Push clauses into a queue before it is fed to the SAT solver *)

    type res =
      | Sat
      | Unsat

    val last_call : unit -> Timestamp.t * res
    (** Time and result of last call *)

    val solve : assumptions:Lit.t list -> unit -> res
    (** Actually try to send clauses to the SAT solver, then call
        its solve function with the given assumptions.
        Assumes that {!Timestamp.incr} was called prior to {!solve},
        that is, that [last_call() |> fst] returns an obsolete timestamp.
        @param assumptions local assumptions *)
  end = struct
    type value = Minisat.value =
      | V_undef
      | V_true
      | V_false

    let pp_value out = function
      | V_undef -> CCFormat.string out "undef"
      | V_true -> CCFormat.string out "true"
      | V_false -> CCFormat.string out "false"

    (* unique instance of minisat *)
    let solver_ = Minisat.create()

    let value l = Minisat.value solver_ (Lit.mlit l)

    let value_cst c info = match info.cst_cases_lits with
      | Lazy_none -> assert (info.cst_cases=Lazy_none); None
      | Lazy_some lits ->
        CCList.find_map
          (fun lit -> match value lit, Lit.atom_view lit with
             | V_true, Atom_assign (c', case) ->
               (* this literal is true! it corresponds to the value *)
               assert (Typed_cst.equal c c');
               Some (Explanation.return lit, case)
             | V_true, _ -> assert false
             | V_false, _
             | V_undef, _ -> None)
          lits

    let value_uty uty = match uty.uty_lit_empty with
      | Lazy_none -> None
      | Lazy_some lit ->
        begin match value lit with
          | V_undef -> None
          | V_true -> Some (Explanation.return lit, Uty_empty)
          | V_false -> Some (Explanation.return (Lit.neg lit), Uty_nonempty)
        end

    let value_proxy (p:term_proxy) =
      let lazy a = p.proxy_atom in
      let lit = Lit.of_atom a in
      assert (Lit.sign lit);
      begin match value lit with
        | V_undef -> None
        | V_true -> Some (Explanation.return lit, true)
        | V_false -> Some (Explanation.return (Lit.neg lit), false)
      end

    (* all lemmas generated so far, to avoid duplicates *)
    let all_lemmas_ : unit Clause.Tbl.t = Clause.Tbl.create 1024

    (* list of clauses that have been newly generated, waiting
       to be propagated to Msat.
       invariant: those clauses must be tautologies *)
    let lemma_queue : Clause.t Queue.t = Queue.create()

    let push_new (c:Clause.t): unit =
      begin match c.Clause.lits with
        | [a;b] when Lit.equal (Lit.neg a) b -> () (* trivial *)
        | _ when Clause.Tbl.mem all_lemmas_ c -> () (* already asserted *)
        | _ ->
          Log.debugf 3
            (fun k->k "(@[<1>@{<green>new_tautology@}@ @[%a@]@])" Clause.pp c);
          incr stat_num_clause_tautology;
          Clause.Tbl.add all_lemmas_ c ();
          Queue.push c lemma_queue
      end;
      ()

    let push_new_l = List.iter push_new

    let flush_ () =
      while not (Queue.is_empty lemma_queue) do
        let c = Queue.pop lemma_queue in
        let cm = Clause.to_minisat c in
        Log.debugf 5
          (fun k->k "(@[add_minisat_clause@ %a@ original: %a@])"
              Minisat.pp_clause cm Clause.pp c);
        Minisat.add_clause_l solver_ cm;
      done

    type res =
      | Sat
      | Unsat

    let last_call_ = ref (Timestamp.zero, Sat)

    let last_call () = !last_call_

    let solve ~assumptions () =
      incr stat_num_calls_minisat;
      let now = Timestamp.cur () in
      assert (fst !last_call_ < now);
      let r =
        try
          flush_ ();
          let assumptions =
            List.map Lit.mlit assumptions |> Array.of_list
          in
          Minisat.solve ~assumptions solver_;
          Sat
        with Minisat.Unsat ->
          Unsat
      in
      last_call_ := now, r;
      r
  end

  (** {2 Reduction to Normal Form} *)

  module Reduce : sig
    val get_nf : term -> explanation * term * Timestamp.t
    (** Current normal form, without any further computation *)

    val compute_nf : term -> explanation * term
    (** Compute the normal form of this term. *)

    val compute_nf_full : on_proxy:(term_proxy -> unit) -> term -> explanation * term
    (** Compute the normal form of this term.
        @param on_proxy callback called on every single proxy met *)
  end = struct
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

    (* set the normal form of [t], propagate to watchers *)
    let set_nf_ t new_t (e:explanation) : unit =
      if Term.equal t new_t then ()
      else (
        let now = Timestamp.cur() in
        t.term_nf <- Some (new_t, e, now);
        Log.debugf 5
          (fun k->k
              "(@[<hv1>set_nf@ @[%a@]@ @[%a@]@ explanation: @[<hv>%a@]@ time: %d@])"
              Term.pp t Term.pp new_t Explanation.pp e (now:>int));
      )

    let get_nf t : explanation * term * Timestamp.t =
      match t.term_nf with
        | None -> Explanation.empty, t, Timestamp.cur()
        | Some (new_t,e,time) -> e, new_t, time

    (* compute the normal form of this term. We know at least one of its
       subterm(s) has been reduced *)
    let rec compute_nf_full ~on_proxy (t:term) : explanation * term =
      (* follow the "normal form" pointer *)
      let now = Timestamp.cur() in
      match t.term_nf, t.term_proxy with
        | Some (t', e, time), _ when time=now->
          (* already computed, just return *)
          e, t'
        | _, Some p ->
          (* avoid looping there *)
          compute_nf_proxy ~on_proxy p
        | None, None
        | Some _, None ->
          let e, nf = compute_nf_noncached ~on_proxy t in
          set_nf_ t nf e;
          e, nf

    and compute_nf_noncached ~on_proxy t =
      match t.term_cell with
        | DB _ -> Explanation.empty, t
        | True | False ->
          Explanation.empty, t (* always trivial *)
        | Const c ->
          begin match c.cst_kind with
            | Cst_defined (_, rhs) ->
              (* expand defined constants *)
              compute_nf_full ~on_proxy (Lazy.force rhs)
            | Cst_undef (_, info, _) ->
              begin match Sat.value_cst c info with
                | None -> Explanation.empty, t (* no value in model *)
                | Some (e, new_t) ->
                  (* c := new_t, we can reduce *)
                  compute_nf_add ~on_proxy e new_t
              end
            | Cst_uninterpreted_dom_elt _ | Cst_cstor _ ->
              Explanation.empty, t
          end
        | Fun _ -> Explanation.empty, t (* no eval under lambda *)
        | Mu body ->
          (* [mu x. body] becomes [body[x := mu x. body]] *)
          let env = DB_env.singleton t in
          Explanation.empty, Term.eval_db env body
        | Quant (q,uty,body) ->
          begin match Sat.value_uty uty with
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
                  let t' = Term.and_ [t1(); t2()] in
                  compute_nf_add ~on_proxy e t'
                | Exists, Uty_nonempty ->
                  (* converse of the forall case, it becomes a "or" *)
                  let t' = Term.or_ [t1(); t2()] in
                  compute_nf_add ~on_proxy e t'
              end
          end
        | Builtin b ->
          (* try boolean reductions, after trivial simplifications *)
          let e, t' =
            let t' = Term.simplify t in
            if t==t'
            then compute_builtin ~on_proxy ~term:t b
            else compute_nf_full ~on_proxy t'
          in
          set_nf_ t t' e;
          e, t'
        | If (a,b,c) ->
          let e_a, a' = compute_nf_full ~on_proxy a in
          let default() =
            if a==a' then t else Term.if_ a' b c
          in
          let e_branch, t' = match a'.term_cell with
            | True -> compute_nf_full ~on_proxy b
            | False -> compute_nf_full ~on_proxy c
            | _ -> Explanation.empty, default()
          in
          (* merge evidence from [a]'s normal form and [b/c]'s
             normal form *)
          let e = Explanation.append e_a e_branch in
          set_nf_ t t' e;
          e, t'
        | Match (u, m) ->
          let e_u, u' = compute_nf_full ~on_proxy u in
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
                    let rhs = Term.eval_db env rhs in
                    (* evaluate new [rhs] *)
                    compute_nf_full ~on_proxy rhs
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
          let e_u, u' = compute_nf_full ~on_proxy u in
          begin match Term.as_domain_elt u' with
            | Some (c_elt,_) ->
              (* do a lookup for this value! *)
              let rhs =
                match ID.Tbl.get m.switch_tbl c_elt.cst_id with
                  | Some rhs -> rhs
                  | None ->
                    (* add an entry, by generating a new RHS *)
                    let rhs = m.switch_make_new () in
                    ID.Tbl.add m.switch_tbl c_elt.cst_id rhs;
                    rhs
              in
              (* continue evaluation *)
              compute_nf_add ~on_proxy e_u rhs
            | None ->
              (* block again *)
              let t' = if u==u' then t else Term.switch u' m in
              e_u, t'
          end
        | App ({term_cell=Const {cst_kind=Cst_cstor _; _}; _}, _) ->
          Explanation.empty, t (* do not reduce under cstors *)
        | App (f, l) ->
          let e_f, f' = compute_nf_full ~on_proxy f in
          (* now beta-reduce if needed *)
          let e_reduce, new_t =
            compute_nf_app ~on_proxy DB_env.empty Explanation.empty f' l
          in
          (* merge explanations *)
          let e = Explanation.append e_reduce e_f in
          set_nf_ t new_t e;
          e, new_t
        | Proxy p ->
          compute_nf_proxy ~on_proxy p

    and compute_nf_proxy ~on_proxy p =
      on_proxy p;
      (* now just trust the SAT solver's decision *)
      begin match Sat.value_proxy p with
        | None -> Explanation.empty, Term.proxy p
        | Some (e, true) -> e, Term.true_
        | Some (e, false) -> e, Term.false_
      end

    (* apply [f] to [l], until no beta-redex is found *)
    and compute_nf_app ~on_proxy env e f l = match f.term_cell, l with
      | Const {cst_kind=Cst_defined (_, lazy def_f); _}, l ->
        (* reduce [f l] into [def_f l] when [f := def_f] *)
        compute_nf_app ~on_proxy env e def_f l
      | Fun (_ty, body), arg :: other_args ->
        (* beta-reduce *)
        assert (Ty.equal _ty arg.term_ty);
        let new_env = DB_env.push arg env in
        (* apply [body] to [other_args] *)
        compute_nf_app ~on_proxy new_env e body other_args
      | _ ->
        (* cannot reduce, unless [f] reduces to something else. *)
        let e_f, f' = Term.eval_db env f |> compute_nf_full ~on_proxy in
        let exp = Explanation.append e e_f in
        if Term.equal f f'
        then (
          (* no more reduction *)
          let t' = Term.app f' l in
          exp, t'
        ) else (
          (* try it again *)
          compute_nf_app ~on_proxy DB_env.empty exp f' l
        )

    (* compute nf of [t], append [e] to the explanation *)
    and compute_nf_add ~on_proxy (e : explanation) (t:term) : explanation * term =
      let e', t' = compute_nf_full ~on_proxy t in
      Explanation.append e e', t'

    (* compute the builtin, assuming its components are
       already reduced *)
    and compute_builtin ~on_proxy ~term:(t:term) (bu:builtin)
      : explanation * term
      = match bu with
      | B_not a ->
        let e_a, a' = compute_nf_full ~on_proxy a in
        begin match a'.term_cell with
          | True -> e_a, Term.false_
          | False -> e_a, Term.true_
          | _ ->
            let t' = if a==a' then t else Term.not_ a' in
            e_a, t'
        end
      | B_and _
      | B_or _
      | B_equiv  (_,_)
      | B_imply (_,_) ->
        assert (t.term_proxy=None);
        (* proxify now, resulting into a blocked evaluation *)
        let p, sign = proxify t in
        assert (t.term_proxy <> None);
        assert sign;
        assert (Sat.value_proxy p = None); (* proxy should be fresh *)
        let new_t = Term.proxy p in
        on_proxy p;
        Explanation.empty, new_t
      | B_eq (a,b) ->
        assert (not (Ty.is_prop a.term_ty));
        let e_a, a' = compute_nf_full ~on_proxy a in
        let e_b, b' = compute_nf_full ~on_proxy b in
        let e_ab = Explanation.append e_a e_b in
        let default() =
          if a==a' && b==b' then t else Term.eq a' b'
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
              |> Term.and_
              |> compute_nf_add ~on_proxy e_ab
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

    let compute_nf t = compute_nf_full ~on_proxy:(fun _ ->()) t
  end

  let pp_dep_full out = function
    | Dep_cst c ->
      let _, nf = Reduce.compute_nf (Term.const c) in
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
    | Dep_proxy p ->
      let v = CCOpt.map snd (Sat.value_proxy p) in
      Format.fprintf out "(@[proxy %a@ value: %a@@])"
        Term.pp p.proxy_for CCFormat.(opt bool) v

  (* from explanation [e1, e2, ..., en] build the guard
         [e1 & e2 & ... & en => …], that is, the clause
         [not e1 | not e2 | ... | not en] *)
  let clause_guard_of_exp_ (e:explanation): Lit.t list =
    Explanation.to_list e
    |> List.map Lit.neg (* this is a guard! *)
    |> CCList.sort_uniq ~cmp:Lit.compare

  (** {2 Global Constraint Graph}

      A graph representing the propositional structure of the problem,
      a link [t -> t'] means either:

      - [t <=> t'] under some assumptions,
      - [t <=> t' OP u] where OP is a boolean connective
  *)
  module Term_graph : sig
    val add : term_proxy -> term_proxy -> proxy_graph_edge_kind -> unit
    val mem : term_proxy -> term_proxy -> proxy_graph_edge_kind -> bool
    val pp_dot : term_proxy Sequence.t CCFormat.printer
  end = struct
    (* TODO: use a smarter data structure? *)

    let mem a b k =
      List.exists
        (fun (b',k') ->
           Term.equal b.proxy_for b'.proxy_for
           &&
           match k, k' with
             | GE_conditional, GE_conditional -> true
             | GE_equiv e1, GE_equiv e2 -> Explanation.equal e1 e2
             | GE_conditional, _
             | GE_equiv _, _ -> false)
        a.proxy_graph

    let add a b k =
      a.proxy_graph <- (b,k) :: a.proxy_graph

    let as_graph : (term_proxy, _ * proxy_graph_edge_kind * _) CCGraph.t =
      CCGraph.make_labelled_tuple
        (fun t ->
           t.proxy_graph
           |> Sequence.of_list
           |> Sequence.map CCPair.swap)

    (* print this set of terms (and their relations) in DOT *)
    let pp_dot out ps =
      let pp_node p: string = CCFormat.sprintf "@[%a@]" Term.pp p.proxy_for in
      let attrs_v p =
        [`Label (pp_node p); `Shape "record"]
      and attrs_e (_,e,_) = match e with
        | GE_conditional -> [`Style "dashed"; `Weight 15]
        | GE_equiv e ->
          let lab = CCFormat.to_string Explanation.pp e in
          [`Label lab; `Weight 1]
      in
      let pp_ out terms =
        CCGraph.Dot.pp_seq
          ~tbl:(CCGraph.mk_table ~eq:eq_proxy_ ~hash:hash_proxy_ 256)
          ~eq:eq_proxy_
          ~attrs_v
          ~attrs_e
          ~graph:as_graph
          out
          terms
      in
      Format.fprintf out "@[%a@]@." pp_ ps
  end

  let print_progress () : unit =
    Printf.printf
      "\r[%.2f] depth %d | expanded %d | clauses %d | \
       lemmas %d | propagated %d%!"
      (get_time())
      (Iterative_deepening.current_depth() :> int)
      !stat_num_cst_expanded
      !stat_num_clause_push
      !stat_num_clause_tautology
      !stat_num_propagations

  let flush_progress (): unit =
    (* TODO: find the proper code for "kill line" *)
    Printf.printf "\r%-80d\r%!" 0

  (** {2 Body of the main loop}

      for each top goal, apply the following recursive function:

      - take a boolean term [t] of interest (initially, the goal)
      - evaluate it in the current model
        + if it reduces to true/false under E, propagate to minisat
         (and add to the graph?)
        + if it reduces to, say, [a & b],
          * add to the graph
          * add to Sat the clauses [equiv t (a&b)];
          * if [a&b] not expanded, then expand it;
          * recurse on [a], [b] (to check they are consistent/totally evaluated)
        + otherwise it should reduce to a blocked term,
         expand what blocks it (and add to {!Sat}). Will return Some_expanded.

      - if all terms reduced to True and were not blocked, return All_check;
        otherwise return Some_expansions or Some_false
  *)
  module Main_step : sig
    (** Result of running one iteration of the main loop, assuming
        last call to the solver returned SAT. *)
    type res =
      | All_true
      | Some_false
      | Some_expansions

    val pp_res : res CCFormat.printer

    val add_top_goal : term -> unit
    (** add [t] to the set of terms that must be evaluated *)

    val top_goals : (term_proxy * bool) Sequence.t
    (** All toplevel goals so far, as proxified terms *)

    val run : unit -> res
    (** Run the main loop, checking all toplevel goals (recursively) in
        the current model. *)
  end = struct
    type res =
      | All_true
      | Some_false
      | Some_expansions

    let pp_res out = function
      | All_true -> CCFormat.string out "all_true"
      | Some_false  -> CCFormat.string out "some_false"
      | Some_expansions -> CCFormat.string out "some_expansions"

    (* list of proxified terms to fully evaluate *)
    let toplevel_goals_ : (term_proxy * bool) list ref = ref []

    (* add a toplevel goal [g] means:
       - remembering it so we can check its value later
       - asserting the unit clause [g] to the SAT solver *)
    let add_top_goal g =
      Log.debugf 2 (fun k->k "(@[<1>add_toplevel_goal@ %a@])" Term.pp g);
      let g_proxy, g_sign = proxify g in
      CCList.Ref.push toplevel_goals_ (g_proxy, g_sign);
      let lit = Lit.assert_proxy ~sign:g_sign g_proxy in
      Sat.push_new (Clause.make [lit]);
      ()

    let top_goals k = List.iter k !toplevel_goals_

    type state = {
      mutable some_expansions: bool;
      mutable all_goals_true: bool;
    }

    (* clause for [e => l] *)
    let clause_imply (l:lit) (e:explanation): Clause.t =
      let c = l :: clause_guard_of_exp_ e |> Clause.make in
      c

    (* clauses that express [e => (a <=> b)] *)
    let clauses_equiv (a:lit) (b:lit) (e:explanation): Clause.t list =
      assert (not (Lit.equal a b));
      let guard = clause_guard_of_exp_ e in
      let c1 = b :: Lit.neg a :: guard |> Clause.make in
      let c2 = a :: Lit.neg b :: guard |> Clause.make in
      [ c1; c2 ]

    (* check that [t] is fully evaluated in the current model, and return its
       value. *)
    let rec check_rec (st:state) (p:term_proxy): bool option =
      match Sat.value_proxy p with
        | None -> None (* well, trivial *)
        | Some (_, b_decided) ->
          let now = Timestamp.cur() in
          (* only check once! *)
          if p.proxy_last_checked<now then (
            p.proxy_last_checked <- now;
            check_rec_with st p ~decided:b_decided
          );
          Some b_decided

    and check_rec_with st p ~decided = match p.proxy_deps with
      | Proxy_subs l ->
        List.iter (check_ignore st) l
      | Proxy_self ->
        (* compute and, maybe, propagate *)
        let e_nf, nf =
          Reduce.compute_nf_full ~on_proxy:(check_ignore st) p.proxy_for
        in
        begin match nf.term_cell, decided with
          | True, true
          | False, false -> () (* checks *)
          | True, false
          | False, true ->
            (* conflict clause *)
            let lit = Lit.assert_proxy ~sign:(not decided) p in
            let c = clause_imply lit e_nf in
            Log.debugf 4
              (fun k->k
                  "(@[<hv1>@{<green>propagate_lit@}@ %a@ nf: %a@ clause: %a@])"
                  pp_proxy_ p Term.pp nf Clause.pp c);
            incr stat_num_propagations;
            st.some_expansions <- true;
            Sat.push_new c;
          | _ ->
            assert (nf.term_deps <> []);
            (* another term. We must expand its  dependencies so
               it can expand further *)
            List.iter (expand_and_check_dep st) nf.term_deps;
            (* add [e => (p <=> nf)] to the graph *)
            let p_nf, p_nf_sign = proxify nf in
            if not (eq_proxy_ p p_nf)
            && not (Term_graph.mem p p_nf (GE_equiv e_nf)) then (
              Log.debugf 3
                (fun k->k
                    "(@[<1>add_intermediate_lemma@ %a@ with: %a@ exp: (@[%a@])@])"
                    pp_proxy_ p pp_proxy_ p_nf Explanation.pp e_nf);
              Term_graph.add p p_nf (GE_equiv e_nf);
              let cs =
                clauses_equiv
                  (Lit.assert_proxy p)
                  (Lit.assert_proxy ~sign:p_nf_sign p_nf)
                  e_nf
              in
              Sat.push_new_l cs;
              st.some_expansions <- true;
              incr stat_num_equiv_lemmas;
            )
        end

    and check_ignore st t =
      ignore (check_rec st t)

    (* expand the given term dependency so that, later, it will be
       assigned a value by the SAT solver;
       in the case of boolean connectives, also check their sub-formulas *)
    and expand_and_check_dep (st:state) (d:term_dep): unit =
      begin match d with
        | Dep_cst c ->
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
              let lits = List.map (Lit.cst_choice c) l in
              info.cst_cases_lits <- Lazy_some lits;
              incr stat_num_cst_expanded;
              st.some_expansions <- true;
              Sat.push_new_l clauses
            | Lazy_some _ -> ()
          end
        | Dep_uty uty ->
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
              st.some_expansions <- true;
              Sat.push_new_l clauses
            | Lazy_some _ -> ()
          end
        | Dep_proxy p ->
          (* check whether [b_expr] is expanded *)
          if not p.proxy_expanded then (
            p.proxy_expanded <- true;
            st.some_expansions <- true;
            let neg_ = Term.not_ in
            let t = p.proxy_for in
            let (clauses:term list list) = match p.proxy_for.term_cell with
              | Builtin (B_not _) -> assert false
              | Builtin (B_and l) ->
                (t :: List.map neg_ l) ::
                  (List.map
                     (fun sub -> [neg_ t; sub])
                     l)
              | Builtin (B_or l) ->
                (neg_ t :: l) ::
                  (List.map
                     (fun sub -> [neg_ sub; t])
                     l)
              | Builtin (B_imply (a,b)) ->
                [ [a; t ];
                  [neg_ b; t];
                  [neg_ a; b; neg_ t]]
              | Builtin (B_equiv (a,b)) ->
                [ [neg_ a; neg_ b; t];
                  [a; b; t];
                  [a; neg_ b; neg_ t];
                  [neg_ a; b; neg_ t];
                ]
              | _ ->
                assert (p.proxy_deps = Proxy_self);
                []
            in
            let clauses =
              List.rev_map Clause.of_terms clauses
            in
            Log.debugf 4
              (fun k->k "(@[<hv1>expand_CNF@ %a@ @[<hv2>:clauses@ %a@]@])"
                  Term.pp t (Utils.pp_list Clause.pp) clauses);
            Sat.push_new_l clauses;
          );
      end

    (* check that [t], a toplevel goal, is fully expanded, and return [true] iff
       it reduces to [Term.true_] in the current model. *)
    let check_top (st:state) (p:term_proxy)(sign:bool): unit =
      let b_opt = check_rec st p in
      (* check that the goal is true *)
      let is_true = match b_opt with
        | None -> false
        | Some b -> b=sign
      in
      Log.debugf 2
        (fun k->k "(@[<hv1>check_top@ goal: %a@ sign: %B nf: %a@])"
            pp_proxy_ p sign CCFormat.(opt bool) b_opt);
      if not is_true then (
        st.all_goals_true <- false;
      );
      ()

    let run (): res =
      let now = Timestamp.cur() in
      Log.debugf 2
        (fun k->k "(@[@{<green>main_step_run@}@ time: %a@])" Timestamp.pp now);
      let st = {
        some_expansions=false;
        all_goals_true=true;
      } in
      List.iter (fun (p,sign) -> check_top st p sign) !toplevel_goals_;
      if st.some_expansions then Some_expansions
      else if st.all_goals_true then All_true
      else Some_false
  end

  (** {2 Conversion} *)

  (* list of constants we are interested in *)
  let model_support_ : Typed_cst.t list ref = ref []

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
          | Ast.And -> Term.and_ [a; b]
          | Ast.Or -> Term.or_ [a; b]
          | Ast.Imply -> Term.imply a b
          | Ast.Eq ->
            if Ty.is_prop a.term_ty
            then Term.equiv a b
            else Term.eq a b
        end

    let add_statement st =
      Log.debugf 2
        (fun k->k "(@[add_statement@ @[%a@]@])" Ast.pp_statement st);
      match st with
        | Ast.Assert t ->
          let t = conv_term [] t in
          Main_step.add_top_goal t;
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
          Main_step.add_top_goal t;
        | Ast.TyDecl id ->
          let rec ty = lazy (
            let ty0 = {
              uty_self=ty;
              uty_parent=None;
              uty_offset=0; (* root *)
              uty_pair=Lazy_none;
              uty_lit_empty=Lazy_none;
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
               declare_defined_cst c)
            l

    let add_statement_l = List.iter add_statement
  end

  (** {2 Main} *)

  type unknown =
    | U_timeout
    | U_max_depth
    | U_incomplete

  module Model = struct
    type domain = cst list

    type t = {
      domains: domain Ty.Tbl.t;
      (* uninterpreted type -> its domain *)
      consts: term Typed_cst.Map.t;
      (* constant -> its value *)
    }

    let make ~consts ~domains = {consts; domains}

    type entry =
      | E_ty of Ty.t * domain
      | E_const of Typed_cst.t * term

    let pp out (m:t) =
      let pp_cst_name out c = ID.pp_name out (Typed_cst.id c) in
      let pp_entry out = function
        | E_ty (ty,l) ->
          Format.fprintf out "(@[<1>type@ %a@ (@[<hv>%a@])@])"
            Ty.pp ty (Utils.pp_list pp_cst_name) l
        | E_const (c,t) ->
          Format.fprintf out "(@[<1>val@ %a@ %a@])"
            ID.pp_name (Typed_cst.id c)
            (Term.pp_top ~ids:false) t
      in
      let es =
        CCList.append
          (Ty.Tbl.to_list m.domains |> List.map (fun (ty,dom) -> E_ty (ty,dom)))
          (Typed_cst.Map.to_list m.consts |> List.map (fun (c,t) -> E_const (c,t)))
      in
      Format.fprintf out "(@[<v>%a@])" (Utils.pp_list pp_entry) es

    exception Bad_model of t * term * term

    let () = Printexc.register_printer
        (function
          | Bad_model (m,t,t') ->
            let msg = CCFormat.sprintf
                "@[<hv2>Bad model:@ goal `@[%a@]`@ evaluates to `@[%a@]`,@ \
                 not true,@ in model @[%a@]@."
                Term.pp t Term.pp t' pp m
            in
            Some msg
          | _ -> None)

    (* helper to return a boolean, checking consistency with [bi] *)
    let ret_proxy_ p b = match Sat.value_proxy p with
      | None -> if b then Term.true_ else Term.false_
      | Some (_, b') -> assert (b=b'); if b then Term.true_ else Term.false_

    (* eval term [t] under model [m] *)
    let eval_ (m:t) t =
      let rec aux t =
        match t.term_cell with
        | True
        | False
        | DB _ -> t
        | Const {cst_kind=Cst_defined(_,lazy t'); _} -> aux t'
        | Const ({cst_kind=Cst_undef(_,_,_); _} as c) ->
          begin match Typed_cst.Map.get c m.consts with
            | None -> t
            | Some t' -> aux t'
          end
        | Const _ -> t
        | App (f,l) ->
          (* here, call by value *)
          let l = List.map aux l in
          aux_app DB_env.empty f l
        | If (a,b,c) ->
          let a = aux a in
          begin match a.term_cell with
            | True -> aux b
            | False -> aux c
            | _ -> Term.if_ a b c
          end
        | Fun _ -> t
        | Quant (q,uty,body) ->
          let lazy ty = uty.uty_self in
          let dom =
            try Ty.Tbl.find m.domains ty
            with Not_found -> errorf "could not find type %a in model" Ty.pp ty
          in
          (* expand into and/or over the domain *)
          let t' =
            let l =
              List.map
                (fun c_dom ->
                   Term.eval_db (DB_env.singleton (Term.const c_dom)) body)
                dom
            in
            match q with
              | Forall -> Term.and_ l
              | Exists -> Term.or_ l
          in
          aux t'
        | Match (u, m) ->
          let u = aux u in
          begin match Term.as_cstor_app u with
            | None -> Term.match_ u m
            | Some (c, _, args) ->
              match ID.Map.get c.cst_id m with
                | None -> Term.match_ u m
                | Some (tys, rhs) ->
                  assert (List.length tys = List.length args);
                  let env = DB_env.push_l args DB_env.empty in
                  let rhs = Term.eval_db env rhs in
                  aux rhs
          end
        | Switch (u, m) ->
          let u = aux u in
          begin match Term.as_domain_elt u with
            | None -> Term.switch u m
            | Some (cst,_) ->
              begin match ID.Tbl.get m.switch_tbl cst.cst_id with
                | Some rhs -> aux rhs
                | None -> Term.switch u m
              end
          end
        | Mu f ->
          let env = DB_env.singleton f in
          aux (Term.eval_db env f)
        | Proxy p ->
          let nf = aux p.proxy_for in
          begin match nf.term_cell with
            | True -> ret_proxy_ p true
            | False -> ret_proxy_ p false
            | _ -> nf
          end
        | Builtin b ->
          let is_true_ t = Term.equal t Term.true_ in
          let is_false_ t = Term.equal t Term.false_ in
          begin match b with
            | B_not f ->
              let f = aux f in
              begin match f.term_cell with
                | True -> Term.false_
                | False -> Term.true_
                | _ -> Term.not_ f
              end
            | B_and l ->
              let l = List.map aux l in
              if List.for_all is_true_ l
              then Term.true_
              else if List.exists is_false_ l
              then Term.false_
              else Term.and_ l
            | B_or l ->
              let l = List.map aux l in
              if List.for_all is_false_ l
              then Term.false_
              else if List.exists is_true_ l
              then Term.true_
              else Term.or_ l
            | B_imply (a,b) ->
              let a = aux a in
              let b = aux b in
              begin match a.term_cell, b.term_cell with
                | _, True
                | False, _  -> Term.true_
                | True, False -> Term.false_
                | _ -> Term.imply a b
              end
            | B_equiv (a,b) ->
              let a = aux a in
              let b = aux b in
              begin match a.term_cell, b.term_cell with
                | True, True
                | False, False -> Term.true_
                | True, False
                | False, True -> Term.false_
                | _ when Term.equal a b -> Term.true_
                | _ -> Term.equiv a b
              end
            | B_eq (a,b) ->
              let a = aux a in
              let b = aux b in
              begin match Term.as_cstor_app a, Term.as_cstor_app b with
                | _ when Term.equal a b -> Term.true_
                | Some (c1,_,l1), Some (c2,_,l2) ->
                  if Typed_cst.equal c1 c2 then (
                    assert (List.length l1 = List.length l2);
                    aux (Term.and_ (List.map2 Term.eq l1 l2))
                  ) else Term.false_
                | _ ->
                  begin match Term.as_domain_elt a, Term.as_domain_elt b with
                    | Some (c1,ty1), Some (c2,ty2) ->
                      (* domain elements: they are all distinct *)
                      assert (Ty.equal ty1 ty2);
                      if Typed_cst.equal c1 c2
                      then Term.true_
                      else Term.false_
                    | _ ->
                      Term.eq a b
                  end
              end
          end
      and aux_app env f l = match f.term_cell, l with
        | Const {cst_kind=Cst_defined(_, lazy def_f); _}, _ ->
          aux_app env def_f l
        | Fun (_, body), arg :: tail ->
          let env = DB_env.push arg env in
          aux_app env body tail
        | _, _ ->
          (* see if [f] reduces in [env] *)
          let f' = aux (Term.eval_db env f) in
          if Term.equal f f'
          then Term.app f l
          else aux_app DB_env.empty f' l
      in
      aux t

    (* check model *)
    let check (m:t) =
      let bad =
        Main_step.top_goals
        |> Sequence.find
          (fun (p,sign) ->
             let t = p.proxy_for in
             let t = if sign then t else Term.not_ t in
             let t' = eval_ m t in
             match t'.term_cell with
               | True -> None
               | _ -> Some (t, t'))
      in
      match bad with
        | None -> ()
        | Some (t,t') -> raise (Bad_model (m, t, t'))
  end

  type model = Model.t

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
        | Proxy p ->
          begin match Sat.value_proxy p with
            | None -> t
            | Some (_, true) -> Term.true_
            | Some (_, false) -> Term.false_
          end
    in
    aux t

  let rec find_domain_ (uty:ty_uninterpreted_slice): cst list =
    match Sat.value_uty uty, uty.uty_pair with
      | None, _
      | _, Lazy_none -> assert false
      | Some (_, Uty_empty), _ -> []
      | Some (_, Uty_nonempty), Lazy_some (c_head, uty_tail) ->
        c_head :: find_domain_ uty_tail

  let compute_model_ () : model =
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
           let t = deref_deep doms t in
           c, t)
      |> Typed_cst.Map.of_seq
    in
    Model.make ~consts ~domains:doms

  (* print all terms reachable from watched literals *)
  let pp_term_graph out () =
    Main_step.top_goals
    |> Sequence.map fst
    |> Term_graph.pp_dot out

  let pp_stats out () : unit =
    Format.fprintf out
      "(@[<hv1>stats@ \
       :num_expanded %d@ \
       :num_uty_expanded %d@ \
       :num_clause_push %d@ \
       :num_clause_tautology %d@ \
       :num_equiv_lemmas %d@ \
       :num_propagations %d@ \
       :num_atoms %d@ \
       :num_calls_minisat %d \
       @])"
      !stat_num_cst_expanded
      !stat_num_uty_expanded
      !stat_num_clause_push
      !stat_num_clause_tautology
      !stat_num_equiv_lemmas
      !stat_num_propagations
      (Atom.num_atoms ())
      !stat_num_calls_minisat

  let do_on_exit ~on_exit =
    List.iter (fun f->f()) on_exit;
    ()

  let add_statement_l = Conv.add_statement_l

  type proof_status =
    | PS_depth_limited of Lit.t
    | PS_complete
    | PS_incomplete

  let pp_proof_status out = function
    | PS_depth_limited lit ->
      Format.fprintf out "(@[depth_limited@ by: %a@])" Lit.pp lit
    | PS_complete -> CCFormat.string out "complete"
    | PS_incomplete -> CCFormat.string out "incomplete"

  (* print the current Minisat model *)
  let pp_cur_trail out () =
    let pp_atom out a =
      let lit = Lit.of_atom a in
      let v = Sat.value lit in
      Format.fprintf out "(@[<1>%a@ value: %a@])"
        Lit.pp lit Sat.pp_value v
    in
    Format.fprintf out "(@[<hv1>trail@ %a@])"
      (Utils.pp_list pp_atom) (Atom.all_atoms ())

  let solve ?(on_exit=[]) ?(pp_trail=false) ?(check=true) () =
    let module ID = Iterative_deepening in
    (* iterated deepening *)
    let rec iter state = match state with
      | ID.Exhausted ->
        do_on_exit ~on_exit;
        Unknown U_max_depth
      | ID.At (cur_depth, cur_lit) ->
        (* new timestamp *)
        Timestamp.incr();
        (* restrict depth *)
        match Sat.solve ~assumptions:[cur_lit] () with
          | Sat.Sat ->
            (* fine, we have a model. Just check that all values are fully
               expanded! *)
            let step_res = Main_step.run () in
            Format.printf "%a@." pp_cur_trail ();
            begin match step_res with
              | Main_step.All_true ->
                (* truly a model *)
                let m = compute_model_ () in
                Log.debugf 1
                  (fun k->k "@{<Yellow>** found SAT@} at depth %a"
                      ID.pp cur_depth);
                if pp_trail then (
                  Format.printf "(@[<2>trail@ @[<hv>%a@]@])@." pp_cur_trail ();
                );
                do_on_exit ~on_exit;
                if check then (
                  Log.debugf 1 (fun k->k "checking model…");
                  Model.check m
                );
                Sat m
              | Main_step.Some_expansions
              | Main_step.Some_false ->
                (* not everything was expanded, or some constraints failed,
                   try again (with same state) *)
                Log.debugf 2
                  (fun k->k
                      "@{<Yellow>** SAT but incomplete, continue@}@ (res %a) \
                       at depth %a" Main_step.pp_res step_res ID.pp cur_depth);
                iter state
            end
          | Sat.Unsat ->
            Timestamp.incr();
            (* check if still unsat without the assumption *)
            let status = match Sat.solve ~assumptions:[] () with
              | Sat.Unsat ->
                (* truly unsat *)
                (* TODO: check if at least one incomplete literal was
                   expanded, in which case, return PS_incomplete *)
                PS_complete
              | Sat.Sat ->
                (* clearly, the conflict needs [cur_lit] *)
                PS_depth_limited cur_lit
            in
            Log.debugf 1
              (fun k->k
                  "@{<Yellow>** found Unsat@} at depth %a;@ \
                   status: %a"
                  ID.pp cur_depth pp_proof_status status);
            assert (Lit.equal (Lit.abs cur_lit) cur_lit);
            begin match status with
              | PS_depth_limited _ ->
                (* negation of the previous limit *)
                Sat.push_new (Clause.make [Lit.neg cur_lit]);
                iter (ID.next ()) (* deeper! *)
              | PS_incomplete ->
                do_on_exit ~on_exit;
                Unknown U_incomplete
              | PS_complete ->
                do_on_exit ~on_exit;
                Unsat
            end
    in
    ID.reset ();
    iter (ID.current ())
end

