
(* This file is free software. See file "license" for more details. *)

module Fmt = CCFormat

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

  val uniform_depth : bool
  (** Depth increases uniformly *)

  val progress: bool
  (** progress display progress bar *)

  val pp_hashcons: bool

  val dimacs_file : string option
  (** File for dumping the SAT problem *)

  val check_proof : bool
  (** Check proofs given by MSat? *)
end

module Bag : sig
  type +'a t
  val empty : 'a t
  val is_empty : _ t -> bool
  val return : 'a -> 'a t
  val append : 'a t -> 'a t -> 'a t (* O(1) *)
  val to_list : 'a t -> 'a list
  val to_seq : 'a t -> 'a Sequence.t
end = struct
  type 'a t =
    | Empty
    | Leaf of 'a
    | Append of 'a t * 'a t
  let is_empty = function Empty -> true | _ -> false
  let empty : _ t = Empty
  let return e = Leaf e
  let append s1 s2 = match s1, s2 with
    | Empty, s | s, Empty -> s
    | _ -> Append (s1, s2)
  let rec to_seq t yield = match t with
    | Empty -> ()
    | Leaf x -> yield x
    | Append (l,r) -> to_seq l yield; to_seq r yield
  let to_list t = to_seq t |> Sequence.to_rev_list
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

  (* did we perform at least one expansion on an unknown that is
     of a type that cannot support exhaustive expansion (e.g. functions)?
  If true, it means that "unsat" might be wrong, so we'll answer "unknown" *)
  let incomplete_expansion : bool ref = ref false

  (* if [true], it means that at least once, a goal was reduced to
     [Undefined_value], meaning we lost precision.
     This means that we are not refutationnally complete. *)
  let has_met_undefined : bool ref = ref false

  (* for objects that are expanded on demand only *)
  type 'a lazily_expanded =
    | Lazy_some of 'a
    | Lazy_none

  (* option with a special case for "Undefined_value" *)
  type 'a option_or_fail =
    | OF_some of 'a
    | OF_none
    | OF_undefined_value

  (* main term cell *)
  type term = {
    mutable term_id: int; (* unique ID, created by hashconsing *)
    mutable term_ty: ty_h;
    mutable term_being_evaled: bool; (* true if currently being evaluated *)
    term_cell: term_cell;
    mutable term_nf: term_nf; (* normal form + explanation of why *)
  }

  (* term shallow structure *)
  and term_cell =
    | Const of cst
    | App of term * term list (* invariants: head not an App, list non empty *)
    | Var of var
    | Binop of bin_op * term * term (* (dis)equality/comparison *)
    | Undefined_value of ty_h
    (* Value that is not defined. On booleans it corresponds to
       the middle case of https://en.wikipedia.org/wiki/Three-valued_logic.
       The [ty] argument is needed for typing *)

  and bin_op =
    | O_eq (* equality *)
    | O_leq (* ≤ *)
    | O_lt (* < *)

  (* pointer to a term to its (current) normal form, updated during evaluation *)
  and term_nf =
    | NF_some of term * explanation
    | NF_none

  (* variable, used in rewrite rules *)
  and var = {
    v_id: int;
    v_ty: ty_h;
  }

  (* bag of atomic explanations. It is optimized for traversal
     and fast cons/snoc/append *)
  and explanation=
    | E_empty
    | E_leaf of lit
    | E_append of explanation * explanation
    | E_or of explanation * explanation (* disjunction! *)

  (* what can block evaluation: a bag of (undefined) constants *)
  and blocking = cst Bag.t

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
    cst_ty: ty_h;
    cst_kind: cst_kind;
    mutable cst_from: Rw_ast.term option; (* translation *)
  }

  and cst_kind =
    | Cst_undef of cst_info
    | Cst_cstor of ty_h (* the datatype *)
    | Cst_defined of (int * rw_rule list) lazy_t (* arity of rules, list of rules *)

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

  (* a rewrite rule of the form [cst args --> rhs], with [vars rhs ⊆ vars args]
     and each [a ∈ args] being a pattern *)
  and rw_rule = {
    rule_cst: cst;
    rule_arity: int; (* len args *)
    rule_args: term list; (* arguments *)
    rule_rhs: term;
  }

  and cond_list = lit lazy_t list

  (* Hashconsed type *)
  and ty_h = {
    mutable ty_id: int;
    ty_cell: ty_cell;
  }

  and ty_cell =
    | Atomic of ID.t * cstor_list
    | Arrow of ty_h * ty_h

  (* set of constructors *)
  and cstor_list = cst lazy_t list

  module Ty_h = struct
    type t = ty_h

    let view t = t.ty_cell

    let equal a b = a.ty_id = b.ty_id
    let compare a b = CCInt.compare a.ty_id b.ty_id
    let hash a = a.ty_id

    module H = Hashcons.Make(struct
        type t = ty_h
        let equal a b = match a.ty_cell, b.ty_cell with
          | Atomic (i1,_), Atomic (i2,_) -> ID.equal i1 i2
          | Arrow (a1,b1), Arrow (a2,b2) ->
            equal a1 a2 && equal b1 b2
          | Atomic _, _
          | Arrow _, _ -> false

        let hash t = match t.ty_cell with
          | Atomic (i,_) -> Hash.combine2 2 (ID.hash i)
          | Arrow (a,b) -> Hash.combine3 3 (hash a) (hash b)

        let set_id ty i = ty.ty_id <- i
      end)

    (* hashcons terms *)
    let hashcons_ ty_cell =
      H.hashcons { ty_cell; ty_id = -1; }

    let atomic id def = hashcons_ (Atomic (id,def))

    let arrow a b = hashcons_ (Arrow (a,b))
    let arrow_l = List.fold_right arrow

    let is_data t = match t.ty_cell with | Atomic (_, _) -> true | _ -> false
    let is_arrow t = match t.ty_cell with | Arrow (_, _) -> true | _ -> false

    let unfold ty : t list * t =
      let rec aux acc ty = match ty.ty_cell with
        | Arrow (a,b) -> aux (a::acc) b
        | _ -> List.rev acc, ty
      in
      aux [] ty

    let rec pp out t = match t.ty_cell with
      | Atomic (id, _) -> ID.pp out id
      | Arrow _ ->
        let args, ret = unfold t in
        Format.fprintf out "(@[->@ %a@ %a@])"
          (Utils.pp_list pp) args pp ret

    (* representation as a single identifier *)
    let rec mangle t : string = match t.ty_cell with
      | Atomic (id,_) -> ID.to_string id
      | Arrow (a,b) -> mangle a ^ "_" ^ mangle b

    module Tbl = CCHashtbl.Make(struct
        type t = ty_h
        let equal = equal
        let hash = hash
      end)
  end

  let cst_pp out (c:cst) = ID.pp out c.cst_id

  let term_equal_ (a:term) b = a==b
  let term_hash_ a = a.term_id
  let term_cmp_ a b = CCInt.compare a.term_id b.term_id

  module Cst = struct
    type t = cst

    let id t = t.cst_id
    let ty t = t.cst_ty
    let view t = t.cst_kind

    let make ?from cst_id ty cst_kind =
      {cst_id; cst_ty=ty; cst_kind; cst_from=from; }

    let make_cstor ?from id ty =
      let _, ret = Ty_h.unfold ty in
      assert (Ty_h.is_data ret);
      make ?from id ty (Cst_cstor ret)

    let make_defined ?from id ty rules : t =
      (* check arity *)
      let rules_with_ar = lazy (
        match rules with
          | lazy [] -> assert false
          | lazy (r1 :: tail) ->
            List.iter (fun r2 -> assert (r1.rule_arity = r2.rule_arity)) tail;
            r1.rule_arity, r1::tail
      ) in
      make ?from id ty (Cst_defined rules_with_ar)

    let make_defined_fix ?from id ty (rules_f : cst -> rw_rule list) : t =
      let rec c = lazy (
        let rules = lazy (rules_f (Lazy.force c)) in
        make_defined ?from id ty rules
      ) in
      Lazy.force c

    let depth (c:t): int = match c.cst_kind with
      | Cst_undef i -> i.cst_depth
      | _ -> assert false

    let make_undef ?parent ?(exist_if=[]) ~depth:cst_depth id ty =
      assert (CCOpt.for_all (fun p -> cst_depth > depth p) parent);
      let info = {
        cst_depth;
        cst_parent=parent;
        cst_exist_conds=exist_if;
        cst_cases=Lazy_none;
        cst_cur_case=None;
      } in
      make id ty (Cst_undef info)

    let as_undefined (c:t) : (t * Ty_h.t * cst_info) option =
      match c.cst_kind with
        | Cst_undef i -> Some (c,c.cst_ty,i)
        | Cst_defined _ | Cst_cstor _ -> None

    let add_exists_if (i:cst_info) cond =
      i.cst_exist_conds <- cond :: i.cst_exist_conds

    let as_undefined_exn (c:t): t * Ty_h.t * cst_info =
      match c.cst_kind with
        | Cst_undef i -> c,c.cst_ty,i
        | Cst_defined _ | Cst_cstor _ -> assert false

    let is_cstor c = match c.cst_kind with Cst_cstor _ -> true | _ -> false

    let equal a b = ID.equal a.cst_id b.cst_id
    let compare a b = ID.compare a.cst_id b.cst_id
    let hash t = ID.hash t.cst_id
    let pp = cst_pp

    module Tbl = CCHashtbl.Make(struct type t=cst let equal=equal let hash=hash end)
  end

  (* what can block a term: a set of constants *)
  module Blocking : sig
    type t = blocking
    val empty : t
    val is_empty : t -> bool
    val return : cst -> t
    val merge : t -> t -> t
    val pp : t Fmt.printer
    val to_seq : t -> cst Sequence.t
    val to_list : t -> cst list
  end = struct
    type t = blocking
    let empty = Bag.empty
    let is_empty = Bag.is_empty
    let return = Bag.return
    let merge = Bag.append
    let pp out l = Fmt.fprintf out "[@[<2>%a@]]" (Utils.pp_list Cst.pp) (Bag.to_list l)
    let to_seq = Bag.to_seq
    let to_list = Bag.to_list
  end

  let cmp_lit a b =
    let c = CCBool.compare a.lit_sign b.lit_sign in
    if c<>0 then c
    else (
      let int_of_cell_ = function
        | Lit_fresh _ -> 0
        | Lit_atom _ -> 1
        | Lit_assign _ -> 2
      in
      begin match a.lit_view, b.lit_view with
        | Lit_fresh i1, Lit_fresh i2 -> ID.compare i1 i2
        | Lit_atom t1, Lit_atom t2 -> term_cmp_ t1 t2
        | Lit_assign (c1,t1), Lit_assign (c2,t2) ->
          CCOrd.(Cst.compare c1 c2 <?> (term_cmp_, t1, t2))
        | Lit_fresh _, _
        | Lit_atom _, _
        | Lit_assign _, _
          -> CCInt.compare (int_of_cell_ a.lit_view) (int_of_cell_ b.lit_view)
      end
    )

  let hash_lit a =
    let sign = a.lit_sign in
    match a.lit_view with
      | Lit_fresh i -> Hash.combine3 1 (Hash.bool sign) (ID.hash i)
      | Lit_atom t -> Hash.combine3 2 (Hash.bool sign) (term_hash_ t)
      | Lit_assign (c,t) ->
        Hash.combine4 3 (Hash.bool sign) (Cst.hash c) (term_hash_ t)

  module Backtrack = struct
    type _level = level
    type level = _level

    let dummy_level = -1

    type stack_cell =
      | S_set_nf of
          term * term_nf
          (* t1.nf <- t2 *)
      | S_set_cst_case of
          cst_info * (explanation * term) option
          (* c1.cst_case <- t2 *)

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
  end

  (* the "bool" constructors *)
  let bool_cstors : cst lazy_t list =
    let rec l = lazy (
      let ty () = Ty_h.atomic (ID.make "bool") (Lazy.force l) in
      [ lazy (Cst.make_cstor (ID.make "true") (ty ()));
        lazy (Cst.make_cstor (ID.make "false") (ty ()));
      ]
    ) in
    Lazy.force l

  let bool_ty : ty_h = List.hd bool_cstors |> Lazy.force |> Cst.ty

  let ty_is_prop t = Ty_h.equal bool_ty t

  (** {2 Free variables} *)
  module IVar = struct
    type t = var
    let mk v_id v_ty : var = {v_id; v_ty}

    let id {v_id; _} = v_id
    let ty {v_ty; _} = v_ty
    let equal v1 v2 = v1.v_id = v2.v_id && Ty_h.equal v1.v_ty v2.v_ty
    let hash v = Hash.combine2 (Hash.int (id v)) (Ty_h.hash (ty v))
    let compare v1 v2 =
      if id v1=id v2 then Ty_h.compare (ty v1)(ty v2)
      else CCInt.compare (id v1)(id v2)

    let pp out {v_id=v; v_ty=ty} =
      if ty_is_prop ty then Fmt.fprintf out "P%d" v
      else if Ty_h.is_arrow ty then Fmt.fprintf out "F%d" v
      else Fmt.fprintf out "X%d" v


    module As_key = struct
      type t = var
      let compare = compare
      let hash = hash
      let equal = equal
    end

    module Map = CCMap.Make(As_key)
    module Tbl = CCHashtbl.Make(As_key)
  end

  let term_pp =
    let rec pp out t =
      pp_rec out t;
      if Config.pp_hashcons then Format.fprintf out "/%d" t.term_id;
      ()
    and pp_rec out t = match t.term_cell with
      | Var v -> IVar.pp out v
      | Const c -> cst_pp out c
      | App (f,l) ->
        Fmt.fprintf out "(@[<1>%a@ %a@])" pp f (Utils.pp_list pp) l
      | Binop (op,t,u) ->
        begin match op with
          | O_eq -> Fmt.fprintf out "(@[<hv1>=@ %a@ %a@])" pp t pp u
          | O_leq -> Fmt.fprintf out "(@[<hv1><=@ %a@ %a@])" pp t pp u
          | O_lt -> Fmt.fprintf out "(@[<hv1><@ %a@ %a@])" pp t pp u
        end
      | Undefined_value ty -> Fmt.fprintf out "?__%s" (Ty_h.mangle ty)
    in
    pp

  module Term = struct
    type t = term

    let id t = t.term_id
    let ty t = t.term_ty
    let sub_hash (t:term): int = t.term_id
    let view t = t.term_cell

    let equal = term_equal_
    let equal_l = CCList.equal equal
    let hash = term_hash_
    let compare a b = CCInt.compare a.term_id b.term_id
    let pp = term_pp

    module H = Hashcons.Make(struct
        type t = term

        (* shallow hash *)
        let hash (t:term) : int = match t.term_cell with
          | Var v -> IVar.hash v
          | Const c -> Hash.combine2 4 (Cst.hash c)
          | App (f,l) -> Hash.combine3 5 (sub_hash f) (Hash.list sub_hash l)
          | Binop (op,t1,t2) ->
            Hash.combine4 6 (Hash.poly op) (sub_hash t1) (sub_hash t2)
          | Undefined_value _ -> 10

        (* equality that relies on physical equality of subterms *)
        let equal t1 t2 : bool = match t1.term_cell, t2.term_cell with
          | Var v1, Var v2 -> IVar.equal v1 v2
          | Const (c1), Const (c2) -> Cst.equal c1 c2
          | App (f1, l1), App (f2, l2) -> f1 == f2 && CCList.equal (==) l1 l2
          | Binop (o1,l1,r1), Binop(o2,l2,r2) -> o1=o2 && l1==l2 && r1==r2
          | Undefined_value ty1, Undefined_value ty2 -> Ty_h.equal ty1 ty2
          | Var _, _
          | Const _, _
          | App _, _
          | Binop _, _
          | Undefined_value _, _
            -> false

        let set_id t i = t.term_id <- i
      end)

    type delayed_ty =
      | DTy_direct of ty_h
      | DTy_lazy of (unit -> ty_h)

    (* build a term. If it's new, add it to the watchlist
       of every member of [watching] *)
    let mk_term_ cell ~(ty:delayed_ty) : term =
      let t = {
        term_id= -1;
        term_ty=bool_ty; (* will be changed *)
        term_being_evaled=false;
        term_cell=cell;
        term_nf=NF_none;
      } in
      let t' = H.hashcons t in
      if t==t' then (
        (* compute ty *)
        t.term_ty <- begin match ty with
          | DTy_direct ty -> ty
          | DTy_lazy f -> f ()
        end;
      );
      t'

    let var (v:var): t = mk_term_ ~ty:(DTy_direct (IVar.ty v)) (Var v)

    let const c : t =
      mk_term_ (Const c) ~ty:(DTy_direct (Cst.ty c))

    (* type of an application *)
    let rec app_ty_ ty l : Ty_h.t = match Ty_h.view ty, l with
      | _, [] -> ty
      | Arrow (ty_a,ty_rest), a::tail ->
        assert (Ty_h.equal ty_a a.term_ty);
        app_ty_ ty_rest tail
      | Atomic _, a::_ ->
        Log.debugf 5
          (fun k->k "cannot apply term of type `%a`@ to `%a:%a`"
              Ty_h.pp ty term_pp a Ty_h.pp a.term_ty);
        assert false

    let app f l : t = match l with
      | [] -> f
      | _ ->
        (* watch head, not arguments *)
        let t = match f.term_cell with
          | App (f1, l1) ->
            let l' = l1 @ l in
            mk_term_ (App (f1, l'))
              ~ty:(DTy_lazy (fun () -> app_ty_ f1.term_ty l'))
          | _ ->
            mk_term_ (App (f,l))
              ~ty:(DTy_lazy (fun () -> app_ty_ f.term_ty l))
        in
        t

    let app_cst f l = app (const f) l

    let binop op t u : t =
      (* for equality, have canonical order on operands *)
      let t, u = if op=O_eq && compare t u > 0 then u, t else t, u in
      mk_term_ ~ty:(DTy_direct bool_ty) (Binop (op,t,u))

    let eq t u : t = binop O_eq t u
    let leq t u : t = binop O_leq t u
    let lt t u : t = binop O_lt t u

    let comparison ~strict t u = if strict then lt t u else leq t u

    let undefined_value ty : t =
      mk_term_ ~ty:(DTy_direct ty) (Undefined_value ty)

    let undefined_value_prop = undefined_value bool_ty

    (* containers *)
    module As_key = struct
        type t = term
        let equal = equal
        let hash = hash
    end

    module Tbl = CCHashtbl.Make(As_key)

    (* utils *)

    let to_seq t (yield:t ->unit): unit =
      let rec aux t =
        yield t;
        match t.term_cell with
          | Var _ | Const _ | Undefined_value _ -> ()
          | App (f,l) -> aux f; List.iter aux l
          | Binop (_,t,u) -> aux t; aux u
      in
      aux t

    (* return [Some] iff the term is an undefined constant *)
    let as_cst_undef (t:term): (cst * Ty_h.t * cst_info) option_or_fail =
      match t.term_cell with
        | Undefined_value _ -> OF_undefined_value
        | Const c ->
          begin match Cst.as_undefined c with
            | Some res -> OF_some res
            | None -> OF_none
          end
        | _ -> OF_none

    (* return [Some (cstor,ty,args)] if the term is a constructor
       applied to some arguments *)
    let as_cstor_app (t:term): (cst * Ty_h.t * term list) option_or_fail =
      match t.term_cell with
        | Undefined_value _ -> OF_undefined_value
        | Const ({cst_kind=Cst_cstor _; _} as c) -> OF_some (c,c.cst_ty,[])
        | App (f, l) ->
          begin match f.term_cell with
            | Const ({cst_kind=Cst_cstor _; _} as c) -> OF_some (c,c.cst_ty,l)
            | _ -> OF_none
          end
        | _ -> OF_none

    (* a value is a constructor application or a term of function type *)
    let is_value t =
      Ty_h.is_arrow (ty t) ||
      begin match t.term_cell with
        | App ({term_cell=Const c; _}, _) | Const c -> Cst.is_cstor c
        | App _ | Binop (_,_,_) | Var _ | Undefined_value _ -> false
      end

    let is_undefined t = match view t with Undefined_value _ -> true | _ -> false

    (* a pattern is made of cstors and variables. *)
    let rec is_pattern t =
      begin match t.term_cell with
        | Var _ -> true
        | Const c -> Cst.is_cstor c
        | App ({term_cell=Const f;_}, l) ->
          Cst.is_cstor f && List.for_all is_pattern l
        | App _ | Binop (_,_,_) | Undefined_value _ -> false
      end

    (* typical view for unification/equality *)
    type unif_form =
      | Unif_cst of cst * Ty_h.t * cst_info
      | Unif_cstor of cst * Ty_h.t * term list
      | Unif_fail
      | Unif_none

    let as_unif (t:term): unif_form = match t.term_cell with
      | Undefined_value _ -> Unif_fail (* can never unify with anything *)
      | Const ({cst_kind=Cst_undef info; _} as c) ->
        Unif_cst (c,c.cst_ty,info)
      | Const ({cst_kind=Cst_cstor _; _} as c) -> Unif_cstor (c,c.cst_ty,[])
      | App (f, l) ->
        begin match f.term_cell with
          | Const ({cst_kind=Cst_cstor _; _} as c) -> Unif_cstor (c,c.cst_ty,l)
          | _ -> Unif_none
        end
      | _ -> Unif_none
  end

  let pp_rule out (r:rw_rule) =
    Format.fprintf out "(@[@[%a@ %a@]@ -> %a@])"
      Cst.pp r.rule_cst (Utils.pp_list term_pp) r.rule_args
      term_pp r.rule_rhs

  let mk_rule c args rule_rhs : rw_rule =
    assert (List.for_all Term.is_pattern args);
    let rule_arity = List.length args in
    {rule_cst=c; rule_args=args; rule_arity; rule_rhs}

  (** Boolean Builtins *)
  module Form = struct
    let true_c, false_c = match bool_cstors with
      | [lazy c1; lazy c2] -> c1, c2
      | _ -> assert false

    let true_, false_ =
      let mk_bool_ (b:bool) : term =
        let c = if b then true_c else false_c in
        let t = {
          term_id= -1;
          term_being_evaled = false;
          term_ty=bool_ty;
          term_cell=Const c;
          term_nf=NF_none;
        } in
        Term.H.hashcons t
      in
      mk_bool_ true, mk_bool_ false

    let bool b = if b then true_ else false_

    let is_true = Term.equal true_
    let is_false = Term.equal false_

    let v_bool = IVar.mk 0 bool_ty
    let ty_bool1 = Ty_h.arrow bool_ty bool_ty
    let ty_bool2 = Ty_h.arrow_l [bool_ty; bool_ty] bool_ty

    let not_c =
      Cst.make_defined_fix (ID.make "not") ty_bool1
        (fun not_c ->
           [ mk_rule not_c [true_] false_;
             mk_rule not_c [false_] true_;
           ])

    let not_ t = Term.app_cst not_c [t]

    let and_c =
      Cst.make_defined_fix (ID.make "and") ty_bool2
        (fun and_c ->
           [ mk_rule and_c [true_; true_] true_;
             mk_rule and_c [false_; Term.var v_bool] false_;
             mk_rule and_c [Term.var v_bool; false_] false_;
           ])

    let and_ t u = Term.app_cst and_c [t; u]

    let or_c =
      Cst.make_defined_fix (ID.make "or") ty_bool2
        (fun or_c ->
           [ mk_rule or_c [false_; false_] false_;
             mk_rule or_c [true_; Term.var v_bool] true_;
             mk_rule or_c [Term.var v_bool; true_] true_;
           ])

    let or_ t u = Term.app_cst or_c [t; u]

    let imply t u = or_ (not_ t) u

    let rec and_l = function
      | [] -> true_
      | [t] -> t
      | a :: l -> and_ a (and_l l)

    let or_l = function
      | [] -> false_
      | [t] -> t
      | a :: l -> List.fold_left or_ a l

    type form_view =
      | F_and of term * term
      | F_or of term * term
      | F_not of term
      | F_binary of bin_op * term * term
      | F_bool of bool
      | F_atom of term

    let form_view (t:term): form_view = match Term.view t with
      | Binop (o, t, u) -> F_binary (o,t,u)
      | Const c when Cst.equal c true_c -> F_bool true
      | Const c when Cst.equal c false_c -> F_bool false
      | App ({term_cell=Const c; _}, [u]) when Cst.equal c not_c -> F_not u
      | App ({term_cell=Const c; _}, [t1;t2]) when Cst.equal c and_c -> F_and (t1,t2)
      | App ({term_cell=Const c; _}, [t1;t2]) when Cst.equal c or_c -> F_or (t1,t2)
      | _ -> F_atom t

    (* remove sign from term, if any *)
    let rec abs t : term * bool = match form_view t with
      | F_not u ->
        let u, sign = abs u in
        u, not sign
      | F_bool false -> true_, false
      | _ -> t, true
  end

  (** Datatype builtins *)
  module Data_term : sig
    val test_cstor : cst -> cst

    val if_c : ty_h -> cst

    val if_ : term -> term -> term -> term
  end = struct
    (* table cstor -> tester for this constructor *)
    let tbl_test_ : cst Cst.Tbl.t = Cst.Tbl.create 128

    (* create a tester function for this constructor *)
    let mk_test (c:cst) : cst =
      let cstors = match Cst.view c with
        | Cst_cstor {ty_cell=Atomic (_,l); _} -> l
        | _ -> assert false
      in
      assert (List.exists (fun (lazy c') -> Cst.equal c c') cstors);
      let _, ty_data = Ty_h.unfold (Cst.ty c) in
      Cst.make_defined_fix
        (ID.make ("is-" ^ ID.name (Cst.id c)))
        (Ty_h.arrow ty_data bool_ty)
        (fun c_test ->
           List.map
             (fun (lazy c') ->
                let ty_args, _ = Ty_h.unfold (Cst.ty c') in
                (* rule [is-c (c' x1…xn) --> δ_{c,c'}] *)
                let args =
                  [Term.app_cst c'
                     (List.mapi (fun i ty -> Term.var (IVar.mk i ty)) ty_args)]
                in
                let rhs = Form.bool (Cst.equal c c') in
                mk_rule c_test args rhs)
             cstors)

    (* get or create tester function for this constructor *)
    let test_cstor (c:cst): cst =
      try Cst.Tbl.find tbl_test_ c
      with Not_found ->
        let c_test = mk_test c in
        Cst.Tbl.add tbl_test_ c c_test;
        c_test

    let tbl_if_ : cst Ty_h.Tbl.t = Ty_h.Tbl.create 32

    (* "if" combinator for the given type *)
    let if_c ty =
      try Ty_h.Tbl.find tbl_if_ ty
      with Not_found ->
        let if_c =
          let x = IVar.mk 0 ty |> Term.var in
          let y = IVar.mk 1 ty |> Term.var in
          Cst.make_defined_fix
            (ID.make ("if-" ^ Ty_h.mangle ty))
            (Ty_h.arrow_l [bool_ty; ty; ty] ty)
            (fun if_c ->
               [ mk_rule if_c [Form.true_; x; y] x;
                 mk_rule if_c [Form.false_; x; y] y;
               ])
        in
        Ty_h.Tbl.add tbl_if_ ty if_c;
        if_c

    let if_ a b c =
      let ty = Term.ty b in
      Term.app_cst (if_c ty) [a;b;c]
  end

  module Subst = struct
    module M = IVar.Map

    type t = term M.t

    let is_empty = M.is_empty
    let empty = M.empty
    let mem subst v = M.mem v subst
    let add m v t =
      assert (not (M.mem v m));
      M.add v t m

    let find m v : term option =
      try Some (M.find v m)
      with Not_found -> None

    let pp out (s:t): unit =
      let pp_bind out (v,t) =
        Fmt.fprintf out "@[<2>%a ->@ %a@]" IVar.pp v Term.pp t
      in
      Fmt.fprintf out "{@[<hv>%a@]}"
        (Fmt.seq ~sep:(Fmt.return ",@ ") pp_bind) (M.to_seq s)

    let rec deref (subst:t) (t:Term.t) = match Term.view t with
      | Var v ->
        begin match find subst v with
          | Some u -> deref subst u
          | None -> t
        end
      | _ -> t

    type eval_mode =
      | Eval_rec
      | Eval_once

    let eval ~mode (subst:t) (t:Term.t): Term.t =
      let module T = Term in
      let rec aux t = match T.view t with
        | Const _
        | Undefined_value _
          -> t
        | Var v ->
          begin match find subst v, mode with
            | None, _ -> t
            | Some u, Eval_once -> u
            | Some u, Eval_rec -> aux u
          end
        | App (f, l) ->
          let f' = aux f in
          let l' = List.map aux l in
          if T.equal f f' && T.equal_l l l' then t else T.app f' l'
        | Binop (op, t1, t2) ->
          let t1' = aux t1 in
          let t2' = aux t2 in
          if T.equal t1 t1' && T.equal t2 t2' then t
          else T.binop op t1' t2'
      in
      if is_empty subst then t else aux t
  end

  let pp_lit out l =
    let pp_lit_view out = function
      | Lit_fresh i -> Format.fprintf out "#%a" ID.pp i
      | Lit_atom t -> Term.pp out t
      | Lit_assign (c,t) ->
        Format.fprintf out "(@[:= %a@ %a@])" Cst.pp c Term.pp t
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
      let t, sign' = Form.abs t in
      let sign = if not sign' then not sign else sign in
      make ~sign (Lit_atom t)

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
  end

  module Explanation = struct
    type t = explanation
    let is_empty = function E_empty -> true | _ -> false
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

    let to_lists e: lit list Sequence.t =
      let open Sequence.Infix in
      let rec aux acc = function
        | E_empty -> Sequence.return acc
        | E_leaf x -> Sequence.return (x::acc)
        | E_append (a,b) ->
          aux acc a >>= fun acc ->
          aux acc b
        | E_or (a,b) ->
          Sequence.append (aux acc a)(aux acc b)
      in
      aux [] e

    let to_lists_uniq e =
      let f l = Lit.Set.of_list l |> Lit.Set.to_list in
      to_lists e |> Sequence.map f

    let to_lists_uniq_l e =
      to_lists_uniq e |> Sequence.to_rev_list

    let pp out e =
      let pp1 out l =
        Format.fprintf out "(@[%a@])"
          (Utils.pp_list Lit.pp) l
      in
      match to_lists_uniq_l e with
        | [] -> assert false
        | [e] -> pp1 out e
        | l ->
          Format.fprintf out "(@[<hv2>or@ %a@])"
            (Utils.pp_list pp1) l
  end

  type 'a match_res =
    | MR_ok of explanation * Subst.t * 'a
    | MR_blocked of Blocking.t (* blocking terms *)
    | MR_fail
    | MR_undefined of explanation (* some matched term is `undefined` *)

  (** {2 Matching} *)
  module Matching : sig
    val match_ :
      ?subst:Subst.t ->
      eval:(term -> explanation * Blocking.t * term) ->
      term ->
      term ->
      unit match_res
      (** [match_ ~eval t u] matches pattern [t] against term [u], trying to bind
          variables of [t].
          We assume that [t] is of the form [f t1…tn] where each [t_i] is
          a pattern (built from variables and constructors).
          [eval] is called on some subterms of [u] to obtain values to match
          against constructors; in case of success all explanations are
          returned in the {!res}.
      *)

    val match_l :
      eval:(term -> explanation * Blocking.t * term) ->
      term list ->
      term list ->
      term list match_res
      (** match patterns with arguments pairwise.
          If there are too many arguments, the remaining ones are returned along
          with the substitution *)
  end = struct
    module T = Term

    exception Fail
    exception Undefined of explanation

    let hd_ t = match T.view t with
      | Const _ | Var _ | Undefined_value _ | Binop _ -> t
      | App (f, _) -> f

    let match_ ?(subst=Subst.empty) ~eval t u : unit match_res =
      let deps = ref Blocking.empty in
      let expls = ref Explanation.empty in
      let rec aux subst t u = match T.view t with
        | Var v ->
          (* variable: just bind. patterns should be linear, thus [v ∉ subst] *)
          assert (not (Subst.mem subst v));
          Subst.add subst v u
        | Const _ ->
          if T.equal t u then subst
          else (
            let e_u, block_u, u = eval u in
            if T.equal t u then (
              expls := Explanation.append e_u !expls;
              subst
            ) else if T.is_value u then (
              raise Fail
            ) else if T.is_undefined u then (
              raise (Undefined e_u)
            ) else (
              assert (not (Blocking.is_empty block_u));
              deps := Blocking.merge block_u !deps;
              subst
            )
          )
        | App ({term_cell=Const c;_} as f, l) ->
          (* see if [u] reduces to a term with same head *)
          assert (Cst.is_cstor c);
          let e_u, block_u, u = eval u in
          begin match T.view u with
            | App (f', l') when T.equal f f' ->
              (* heads match, now recurse to subterms *)
              expls := Explanation.append e_u !expls;
              aux_l subst l l'
            | _ ->
              if T.is_value u then (
                (* value with the wrong cstor *)
                raise Fail
              ) else if T.is_undefined u then (
                raise (Undefined e_u)
              ) else (
                assert (not (Blocking.is_empty block_u));
                deps := Blocking.merge block_u !deps;
                subst
              )
          end
        | Binop _ | App _ | Undefined_value _
          -> assert false (* invalid pattern *)
      and aux_l subst l1 l2 = match l1, l2 with
        | [], [] -> subst
        | [], _ | _, [] -> raise Fail (* missing args *)
        | t1::tail1, t2::tail2 ->
          let subst = aux subst t1 t2 in
          aux_l subst tail1 tail2
      in
      try
        let subst = aux subst t u in
        (* see if some subterms of u block *)
        if Blocking.is_empty !deps
        then MR_ok (!expls,subst,())
        else MR_blocked !deps
      with
        | Fail -> MR_fail
        | Undefined e -> MR_undefined e

    type state =
      | S_all_ok of Explanation.t
      | S_some_blocked of Blocking.t

    let match_l ~eval l1 l2 : _ match_res =
      let rec aux ~st subst l1 l2 = match l1, l2 with
        | [], _ ->
          begin match st with
            | S_all_ok expl -> MR_ok (expl, subst, l2) (* return subst + rest *)
            | S_some_blocked block ->
              assert (not (Blocking.is_empty block));
              MR_blocked block
          end
        | _::_, [] -> MR_fail (* too few patterns *)
        | t1 :: l1', t2 :: l2' ->
          begin match match_ ~subst ~eval t1 t2 with
            | MR_fail -> MR_fail
            | MR_undefined e -> MR_undefined e (* can stop directly *)
            | MR_blocked blk ->
              let st = match st with
                | S_all_ok _ -> S_some_blocked blk
                | S_some_blocked blk' ->
                  S_some_blocked (Blocking.merge blk blk')
              in
              aux ~st subst l1' l2'
            | MR_ok (expl', subst, ()) ->
              let st = match st with
                | S_some_blocked _ -> st (* will block anyway *)
                | S_all_ok expl -> S_all_ok (Explanation.append expl expl')
              in
              aux ~st subst l1' l2'
          end
      in
      aux ~st:(S_all_ok Explanation.empty) Subst.empty l1 l2
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

    let to_seq c = Sequence.of_list c.lits
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
          prev_depth, Lit.atom Form.true_

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

  module Expand : sig
    val expand_cst : cst -> unit
  end = struct
    (* make a fresh constant, with a unique name *)
    let new_cst_ =
      let n = ref 0 in
      fun ?exist_if ~parent ~depth name ty :cst ->
        let id = ID.makef "?%s_%d" name !n in
        incr n;
        Cst.make_undef ?exist_if ~parent ~depth id ty

    (* [imply_product l cs] builds the list of
       [F => cs] for each [F] in [l], or returns [cs] if [l] is empty *)
    let imply_product guards (c:Lit.t list) : Lit.t list list =
      match guards with
        | [] -> [c]
        | l -> List.map (fun f -> Lit.neg f :: c) l

    let depth_of_term (t:term): int option =
      Term.to_seq t
      |> Sequence.filter_map
        (fun sub -> match sub.term_cell with
           | Const {cst_kind=Cst_undef info; _} -> Some info.cst_depth
           | _ -> None)
      |> Sequence.max ~lt:(fun a b ->a<b)

    (* build clause(s) that explains that [c] must be one of its
       cases *)
    let clauses_of_cases (c:cst) (l:term list): Clause.t list =
      let info = match Cst.as_undefined c with
        | None -> assert false
        | Some (_,_,info) -> info
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
    let mk_sub_cst ?exist_if ~parent ~depth ty_arg : cst =
      let basename = Ty_h.mangle ty_arg in
      new_cst_ ?exist_if basename ty_arg ~parent ~depth

    type state = {
      cst: cst;
      info: cst_info;
      ty: Ty_h.t;
      memo: cst list Ty_h.Tbl.t;
      (* table of already built constants, by type *)
    }

    let mk_state cst ty info : state = {
      cst; info; ty;
      memo = Ty_h.Tbl.create 16;
    }

    (* get or create a constant that has this type *)
    let get_or_create_cst
        ~(st:state) ~(parent:cst) ~(used:cst list ref) ~depth ty_arg
      : cst * (lit lazy_t -> unit) =
      let usable =
        Ty_h.Tbl.get_or ~default:[] st.memo ty_arg
        |> List.filter
          (fun c' -> not (List.exists (Cst.equal c') !used))
      in
      let cst = match usable with
        | [] ->
          (* make a new constant and remember it *)
          let cst = mk_sub_cst ~exist_if:[] ~parent ~depth ty_arg in
          Ty_h.Tbl.add_list st.memo ty_arg cst;
          used := cst :: !used; (* cannot use it in the same case *)
          cst
        | cst :: _ ->
          (* [cst] has the proper type, and is not used yet *)
          used := cst :: !used;
          cst
      in
      let _, _, info = Cst.as_undefined_exn cst in
      cst, (Cst.add_exists_if info)

    (* expand [cst : data] where [data] has given [cstors] *)
    let expand_cases_data st cstors =
      (* datatype: refine by picking the head constructor *)
      List.map
        (fun (lazy c) ->
           let rec case = lazy (
             let ty_args, _ = Cst.ty c |> Ty_h.unfold in
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

    (* synthesize a function [fun x:ty_arg. body]
       where [body] will destruct [x] depending on its type,
       or [fun _:ty_arg. constant] *)
    let expand_cases_arrow _st ty_arg ty_ret =
      (* TODO: get-or-create combinators for [arg -> ret]:
         [const x y := x;
          match_nat x f 0 := x;
          match_nat x f (s n) := f n]
         and return set [{ const ?x, match_nat ?x ?f }]
      *)
      Format.printf "TODO: implement expand_arrow %a@." Ty_h.pp (Ty_h.arrow ty_arg ty_ret);
      assert false

    (* build the disjunction [l] of cases for [info]. Might expand other
       objects, such as uninterpreted slices. *)
    let expand_cases
        (cst:cst)
        (ty:Ty_h.t)
        (info:cst_info)
        : term list * Clause.t list  =
      assert (info.cst_cases = Lazy_none);
      (* expand constant depending on its type *)
      let st = mk_state cst ty info in
      let by_ty, other_clauses = match Ty_h.view ty with
        | Atomic (_, cstors) ->
          expand_cases_data st cstors
        | Arrow (ty_arg, ty_ret) ->
          expand_cases_arrow st ty_arg ty_ret
      in
      (* build clauses *)
      let case_clauses = clauses_of_cases cst by_ty in
      by_ty, List.rev_append other_clauses case_clauses

    (* expand the given constant so that, later, it will be
       assigned a value by the SAT solver *)
    let expand_cst (c:cst): unit =
      let _, ty, info = Cst.as_undefined_exn c in
      let depth = info.cst_depth in
      (* check whether [c] is expanded *)
      begin match info.cst_cases with
        | Lazy_none ->
          (* [c] is blocking, not too deep, but not expanded *)
          let l, clauses = expand_cases c ty info in
          Log.debugf 2
            (fun k->k "(@[<1>expand_cst@ `@[%a:@,%a@]`@ :into (@[%a@])@ :depth %d@])"
                Cst.pp c Ty_h.pp ty (Utils.pp_list Term.pp) l depth);
          info.cst_cases <- Lazy_some l;
          incr stat_num_cst_expanded;
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
              | OF_undefined_value | OF_none -> false
              | OF_some (_, _, l) -> List.exists aux l
          )
        end
      in
      List.exists aux l

    (* set the normal form of [t], propagate to watchers *)
    let set_nf_ t new_t (e:explanation) : unit =
      if Term.equal t new_t then ()
      else (
        Backtrack.push_set_nf_ t;
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

    type match_st =
      | M_blocked of Blocking.t
      | M_undef of Explanation.t (* at least one term is undefined *)

    let pp_match_st out = function
      | M_blocked b -> Fmt.fprintf out "(@[blocked %a@])" Blocking.pp b
      | M_undef e -> Fmt.fprintf out "(@[undef %a@])" Explanation.pp e

    (* compute the normal form of this term. We know at least one of its
       subterm(s) has been reduced *)
    let rec compute_nf (t:term) : explanation * blocking * term =
      if t.term_being_evaled then (
        (* [t] is already being evaluated, this means there is
             an evaluation in the loop.
             We must approximate and return [Undefined_value] *)
        Explanation.empty, Blocking.empty, Term.undefined_value t.term_ty
      ) else (
        (* follow the "normal form" pointer *)
        begin match t.term_nf with
          | NF_some (t', e) ->
            t.term_being_evaled <- true;
            let exp, blocking, nf = compute_nf_add e t' in
            (* path compression here *)
            if not (Term.equal t' nf) then (
              assert (not (Term.equal t nf));
              set_nf_ t nf exp;
            );
            t.term_being_evaled <- false;
            exp, blocking, nf
          | NF_none ->
            t.term_being_evaled <- true;
            let res = compute_nf_noncached t in
            t.term_being_evaled <- false;
            res
        end
      )

    (* compute nf of [t], append [e] to the explanation *)
    and compute_nf_add (e : explanation) (t:term)
      : explanation * blocking * term =
      let e', b', t' = compute_nf t in
      Explanation.append e e', b', t'

    and compute_nf_noncached (t:term): explanation * blocking * term =
      assert (t.term_nf = NF_none);
      begin match t.term_cell with
        | Var _ -> Explanation.empty, Blocking.empty, t
        | Const c ->
          begin match c.cst_kind with
            | Cst_undef {cst_cur_case=Some (e,new_t); _} ->
              (* c := new_t, we can reduce *)
              compute_nf_add e new_t
            | Cst_undef _ ->
              (* blocked by [c] *)
              Explanation.empty, Blocking.return c, t
            | Cst_defined (lazy (0, r :: _)) ->
              (* nullary rule *)
              assert (r.rule_args=[]);
              compute_nf r.rule_rhs
            | Cst_defined _ | Cst_cstor _ ->
              Explanation.empty, Blocking.empty, t
          end
        | App ({term_cell=Const {cst_kind=Cst_cstor _; _}; _}, _) ->
          Explanation.empty, Blocking.empty, t (* do not reduce under cstors *)
        | App (f, l) ->
          let e_f, b_f, f' = compute_nf f in
          if Term.equal f f' then (
            assert (Explanation.is_empty e_f); (* termination! *)
            let n = List.length l in
            begin match Term.view f' with
              | Const {cst_kind=Cst_defined (lazy (ar, rules)); _} when ar <= n ->
                (* a defined constant, see if we can rewrite *)
                begin match find_rule rules l with
                  | MR_fail -> assert false
                  | MR_blocked b -> e_f, Blocking.merge b b_f, t
                  | MR_ok (e, subst, (rule, rest)) ->
                    (* rule applies, now substitute, add remaining args,
                       and recurse *)
                    let t' =
                      Term.app
                        (Subst.eval ~mode:Subst.Eval_once subst rule.rule_rhs)
                        rest
                    in
                    let expl = Explanation.append e e_f in
                    compute_nf_add expl t'
                  | MR_undefined e ->
                    (* evaluates to [undefined] *)
                    let expl = Explanation.append e e_f in
                    expl, Blocking.empty, Term.undefined_value (Term.ty t)
                end
              | _ -> e_f, b_f, t (* normal form *)
            end
          ) else (
            (* compute [f' l] *)
            let t' = Term.app f' l in
            compute_nf_add e_f t'
          )
        | Undefined_value _ ->
          Explanation.empty, Blocking.empty, t (* already a normal form *)
        | Binop (O_eq, t1, t2) -> compute_unif t t1 t2
        | Binop (O_leq, t1, t2) -> compute_cmp t t1 t2 ~strict:false
        | Binop (O_lt, t1, t2) -> compute_cmp t t1 t2 ~strict:true
      end

    (* find a rule that applies to the given list of arguments.
       returns the rule that applies and the unused arguments. *)
    and find_rule (rules0: rw_rule list) (args:term list) : (rw_rule * term list) match_res =
      let rec aux ~st rules = match rules with
        | [] ->
          (*Format.printf "(@[:rules (@[%a@])@ :args (@[%a@])@ :st %a@])@."
            (Utils.pp_list pp_rule) rules0 (Utils.pp_list Term.pp) args
            pp_match_st st;*)
          begin match st with
            | M_blocked block ->
              assert (not (Blocking.is_empty block)); (* rules should be total *)
              MR_blocked block
            | M_undef e -> MR_undefined e
          end
        | rule :: rules_tl ->
          let res = Matching.match_l ~eval:compute_nf rule.rule_args args in
          begin match res with
            | MR_ok (e,subst,rest) ->
              (* rule matches, we can ignore the other rules *)
              MR_ok (e,subst,(rule,rest))
            | MR_fail -> aux ~st rules_tl (* ignore rule *)
            | MR_undefined e ->
              (* there might be several rules which meet an undefined term,
                 we ought to conflict on all of them *)
              let st = match st with
                | M_undef e' -> M_undef (Explanation.or_ e e')
                | M_blocked _ -> M_undef e
              in
              aux ~st rules_tl
            | MR_blocked block' ->
              let st = match st with
                | M_undef _ -> st (* ignore block, will be undefined anyway *)
                | M_blocked block ->
                  (* add [block'] to blocking terms and try next rules *)
                  M_blocked (Blocking.merge block block')
              in
              aux ~st rules_tl
          end
      in
      assert (rules0 <> []);
      aux ~st:(M_blocked Blocking.empty) rules0

    (* compute [t1 =?= t2] *)
    and compute_unif old t1 t2 : explanation * blocking * term =
      let e1, b1, t1' = compute_nf t1 in
      let e2, b2, t2' = compute_nf t2 in
      let e_both = Explanation.append e1 e2 in
      let b_both = Blocking.merge b1 b2 in
      let default() =
        if t1==t1' && t2==t2' then old else Term.eq t1' t2'
      in
      (* check first for failures, then try to unify *)
      begin match Term.as_unif t1', Term.as_unif t2' with
        | Term.Unif_fail, Term.Unif_fail ->
          Explanation.or_ e1 e2, Blocking.empty, Term.undefined_value_prop
        | Term.Unif_fail, _ -> e1, Blocking.empty, Term.undefined_value_prop
        | _, Term.Unif_fail -> e2, Blocking.empty, Term.undefined_value_prop
        | _ when Term.equal t1' t2' ->
          e_both, Blocking.empty, Form.true_ (* physical equality *)
        | Term.Unif_cstor (c1,ty1,l1), Term.Unif_cstor (c2,_,l2) ->
          if not (Cst.equal c1 c2)
          then
            (* [c1 ... = c2 ...] --> false, as distinct constructors
               can never be equal *)
            e_both, Blocking.empty, Form.false_
          else if Cst.equal c1 c2
               && List.length l1 = List.length l2
               && List.length l1 = List.length (fst (Ty_h.unfold ty1))
          then (
            (* same constructor, fully applied -> injectivity:
               arguments are pairwise equal.
               We need to evaluate the arguments further (e.g.
               if they start with constructors) *)
            List.map2 Term.eq l1 l2
            |> Form.and_l
            |> compute_nf_add e_both
          )
          else e_both, b_both, default()
        | Term.Unif_cstor (_, _, l), _ when cycle_check_l ~sub:t2' l ->
          (* acyclicity rule *)
          e_both, Blocking.empty, Form.false_
        | _, Term.Unif_cstor (_, _, l) when cycle_check_l ~sub:t1' l ->
          e_both, Blocking.empty, Form.false_
        | Term.Unif_cstor (cstor, _, args), Term.Unif_cst (c, _, info)
        | Term.Unif_cst (c, _, info), Term.Unif_cstor (cstor, _, args) ->
          (* expand right now, so we can get a list of cases *)
          Expand.expand_cst c;
          begin match info.cst_cases with
            | Lazy_none -> assert false
            | Lazy_some cases ->
              (* unification: use the literal [c := case] for
                 the [case in cases] that matches [cstor].
                 Reduce to [:= c case & case.i=args.i] *)
              let sub_metas =
                CCList.find_map
                  (fun t -> match Term.as_cstor_app t with
                     | OF_some (cstor', _, sub_metas) ->
                       if Cst.equal cstor cstor'
                       then Some sub_metas
                       else None
                     | OF_undefined_value | OF_none -> assert false)
                  cases
                |> (function | Some x->x | None -> assert false)
              in
              assert (List.length sub_metas = List.length args);
              (* check if [c] starts with [cstor] *)
              let same_cstor =
                Term.app_cst (Data_term.test_cstor cstor) [Term.const c]
              and check_subs =
                List.map2 Term.eq sub_metas args
                |> Form.and_l
              in
              incr stat_num_unif;
              (* eager "and", as a "if" (do not check subs if wrong cstor) *)
              let t' = Data_term.if_ same_cstor check_subs Form.false_ in
              compute_nf_add e_both t'
          end
        | _ -> e_both, b_both, default()
      end

    (* comparison (strict or not) between datatypes*)
    and compute_cmp old t1 t2 ~strict : explanation * blocking * term =
      let e1, b1, t1' = compute_nf t1 in
      let e2, b2, t2' = compute_nf t2 in
      let e_both = Explanation.append e1 e2 in
      let b_both = Blocking.merge b1 b2 in
      let default() =
        if t1==t1' && t2==t2' then old else Term.comparison ~strict t1' t2'
      in
      (* check first for failures, then try to unify *)
      begin match Term.as_cstor_app t1', Term.as_cstor_app t2' with
        | OF_undefined_value, _
        | _, OF_undefined_value ->
          e_both, Blocking.empty, Term.undefined_value_prop
        | OF_none, OF_none ->
          e_both, b_both, default()
        | OF_none, OF_some _ -> e_both, b1, default()
        | OF_some _, OF_none -> e_both, b2, default()
        | OF_some (c1,_,l1), OF_some (c2,_,l2) ->
          assert (Blocking.is_empty b_both);
          if Cst.compare c1 c2 < 0 then (
            (* smaller by head cstor *)
            e_both, Blocking.empty, Form.true_
          ) else if Cst.compare c1 c2 > 0 then (
            (* greater *)
            e_both, Blocking.empty, Form.false_
          ) else if l1=[] then (
            assert (l2=[]);
            e_both, Blocking.empty, Form.bool (not strict);
          ) else (
            (* same cstor: compare lexico *)
            assert (List.length l1 = List.length l2); (* by typing *)
            let rec mk_sub l1 l2 = match l1, l2 with
              | [], _ | _, [] -> assert false
              | [t1], [t2] -> Term.comparison ~strict t1 t2 (* last case *)
              | t1 :: l1', t2 :: l2' ->
                (* [if t1=t2 then compare l1' l2' else t1<t2 *)
                Data_term.if_
                  (Term.eq t1 t2)
                  (mk_sub l1' l2')
                  (Term.lt t1 t2)
            in
            e_both, b_both, mk_sub l1 l2
          )
      end

    let compute_nf_lit (lit:lit): explanation * blocking * lit =
      match Lit.view lit with
        | Lit_fresh _
        | Lit_assign (_,_)
          -> Explanation.empty, Blocking.empty, lit
        | Lit_atom t ->
          let e, b, t' = compute_nf t in
          e, b, Lit.atom ~sign:(Lit.sign lit) t'
  end

  (** {2 A literal asserted to SAT}

      A set of terms that must be evaluated (and their value, propagated)
      in the current partial model. *)

  module Top_terms : sig
    val add : term -> unit
    val size : unit -> int
    val update_all : unit -> unit (** update all top terms *)
  end = struct
    type t = {
      root: term;
      mutable block: blocking;
    }
    (* actually, the watched lit is [Lit.atom t.root], but we link
       [t] directly because this way we have direct access to its
       normal form *)

    let pp out t = Term.pp out t.root

    (* clauses for [e => l] *)
    let clause_imply (l:lit) (e:explanation): Clause.t Sequence.t =
      clause_guard_of_exp_ e
      |> Sequence.map
        (fun guard -> l :: guard |> Clause.make)

    let propagate_lit_ (t:term) (e:explanation): unit =
      let cs = clause_imply (Lit.atom ~sign:true t) e |> Sequence.to_rev_list in
      Log.debugf 4
        (fun k->k
            "(@[<hv1>@{<green>propagate_lit@}@ %a@ nf: %a@ clauses: (@[%a@])@])"
            Term.pp t Term.pp (let _,_,t=Reduce.compute_nf t in t)
            (Utils.pp_list Clause.pp) cs);
      incr stat_num_propagations;
      Clause.push_new_l cs;
      ()

    let trigger_conflict (e:explanation): unit =
      let cs =
        clause_guard_of_exp_ e
        |> Sequence.map Clause.make
        |> Sequence.to_rev_list
      in
      Log.debugf 4
        (fun k->k
            "(@[<hv1>@{<green>conflict@}@ clauses: (@[%a@])@])"
            (Utils.pp_list Clause.pp) cs);
      incr stat_num_propagations;
      Clause.push_new_l cs;
      ()

    (* evaluate [t] in current partial model, and expand the constants
       that block it *)
    let update (t:t): unit =
      assert (ty_is_prop (Term.ty t.root));
      let e, block, new_t = Reduce.compute_nf t.root in
      (* if [new_t = true/false], propagate literal *)
      begin match new_t.term_cell with
        | _ when Form.is_true new_t  -> propagate_lit_ t.root e
        | _ when Form.is_false new_t -> propagate_lit_ (Form.not_ t.root) e
        | Undefined_value _ ->
          (* there is no chance that this goal evaluates to a boolean anymore,
             we must try something else *)
          has_met_undefined := true;
          trigger_conflict e
        | _ ->
          Log.debugf 4
            (fun k->k
                "(@[<1>update@ %a@ @[<1>:normal_form@ %a@]@ \
                 :deps (@[%a@])@ :exp @[<hv>%a@]@])"
                Term.pp t.root Term.pp new_t Blocking.pp block
                Explanation.pp e);
          t.block <- block;
          Blocking.to_seq block Expand.expand_cst;
      end;
      ()

    (* NOTE: we use a list because it's lightweight, fast to iterate
       on, and we only add elements in it at the beginning *)
    let top_ : t list ref = ref []

    let mem_top_ (t:term): bool =
      List.exists (fun u -> Term.equal t u.root) !top_

    let add (t:term) =
      let lit, _ = Form.abs t in
      if not (mem_top_ lit) then (
        Log.debugf 3
          (fun k->k "(@[<1>@{<green>Top_terms.add@}@ %a@])" Term.pp lit);
        let top = {root=lit; block=Blocking.empty} in
        top_ := top :: !top_;
        (* also ensure it is watched properly *)
        update top;
      )

    let to_seq yield = List.iter yield !top_

    let size () = List.length !top_

    (* is the dependency updated, i.e. decided by the SAT solver? *)
    let dep_updated (c:cst): bool = match c.cst_kind with
      | Cst_undef i -> CCOpt.is_some i.cst_cur_case
      | _ -> assert false

    (* update all top terms (whose dependencies have been changed) *)
    let update_all () =
      to_seq
      |> Sequence.filter
        (fun top -> Blocking.to_seq top.block |> Sequence.exists dep_updated)
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
      let _, _, nf = Reduce.compute_nf t in
      Form.is_true nf

    let check () =
      if not (List.for_all is_true_ !toplevel_goals_)
      then (
        if Config.progress then flush_progress();
        Log.debugf 1
          (fun k->
             let pp_dep out c =
               let _, nf = Reduce.get_nf (Term.const c) in
               Format.fprintf out
                 "(@[%a@ nf:%a@ :expanded %B@])"
                 Cst.pp c Term.pp nf
                 (match Cst.as_undefined c with
                   | None -> assert false
                   | Some (_,_,i) -> i.cst_cases <> Lazy_none)
             in
             let pp_lit out l =
               let e, block, nf = Reduce.compute_nf l in
               Format.fprintf out
                 "(@[<hv1>%a@ nf: %a@ exp: %a@ deps: (@[<hv>%a@])@])"
                 Term.pp l Term.pp nf Explanation.pp e
                 (Utils.pp_list pp_dep) (Blocking.to_list block)
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

    (* assert [c := new_t] (which is, [lit]), or conflict *)
    let assert_choice ~lit (c:cst)(new_t:term) : unit =
      let _, _, info = Cst.as_undefined_exn c in
      begin match info.cst_cur_case with
        | None ->
          let e = Explanation.return lit in
          Backtrack.push_set_cst_case_ info;
          info.cst_cur_case <- Some (e, new_t);
        | Some (_,new_t') ->
          Log.debugf 1
            (fun k->k "(@[<hv1>assert_choice %a@ :to %a@ :cur %a@])"
                Cst.pp c Term.pp new_t Term.pp new_t');
          assert (Term.equal new_t new_t');
      end

    (* signal to the SAT solver that [lit --e--> false] *)
    let trigger_conflict (lit:lit) (e:explanation): unit =
      let cs =
        clause_guard_of_exp_ e
        |> Sequence.map
          (fun guard -> Lit.neg lit :: guard |> Clause.make)
      in
      Sequence.iter Clause.push_new cs

    (* handle a literal assumed by the SAT solver *)
    let assume_lit (lit:Lit.t) : unit =
      Log.debugf 2
        (fun k->k "(@[<1>@{<green>assume_lit@}@ @[%a@]@])" Lit.pp lit);
      (* check consistency first *)
      let e, _, lit' = Reduce.compute_nf_lit lit in
      begin match Lit.view lit' with
        | Lit_fresh _ -> ()
        | Lit_atom t when Form.is_true t -> ()
        | Lit_atom t when Form.is_false t ->
          (* conflict, the goal reduces to [false]! *)
          trigger_conflict lit e
        | Lit_atom {term_cell=Undefined_value ty; _} ->
          (* the literal will never be a boolean, we must try
             something else *)
          assert (ty_is_prop ty);
          has_met_undefined := true; (* incomplete *)
          trigger_conflict lit e
        | Lit_atom _ -> ()
        | Lit_assign(c, t) ->
          if Lit.sign lit then assert_choice ~lit c t
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
      |> Sequence.iter Top_terms.add;
    incr stat_num_clause_push;
    M.assume [Clause.lits c]

  (** {2 Conversion} *)

  (* list of constants we are interested in *)
  let model_support_ : Cst.t list ref = ref []

  let add_cst_support_ (c:cst): unit =
    CCList.Ref.push model_support_ c

  module Conv = struct
    (* for converting Ty into ty_h *)
    let ty_tbl_ : Ty_h.t lazy_t ID.Tbl.t = ID.Tbl.create 16

    (* for converting constants *)
    let decl_ty_ : cst lazy_t ID.Tbl.t = ID.Tbl.create 16

    module A = Rw_ast

    let rec conv_ty (ty:Ty.t): Ty_h.t = match ty with
      | Ty.Prop -> bool_ty
      | Ty.Const id ->
        begin try ID.Tbl.find ty_tbl_ id |> Lazy.force
          with Not_found -> errorf "type %a not in ty_tbl" ID.pp id
        end
      | Ty.Arrow (a,b) -> Ty_h.arrow (conv_ty a) (conv_ty b)

    type state = {
      var_tbl : IVar.t Var.Tbl.t; (* var -> ivar *)
      unknown_tbl : cst Var.Tbl.t; (* var -> unknown *)
      mutable var_n : int; (* to allocate ivars *)
    }

    let create() : state = {
      var_tbl = Var.Tbl.create 16;
      unknown_tbl = Var.Tbl.create 16;
      var_n=0;
    }

    let get_or_create_unknown ~st v : cst =
      Var.Tbl.get_or_add st.unknown_tbl ~k:v
        ~f:(fun _ ->
          Cst.make_undef ~depth:0 (Var.id v) (Var.ty v |> conv_ty))

    let rec conv_term_rec (st: state) (t:A.term): term =
      begin match A.T.view t with
        | A.Bool true -> Form.true_
        | A.Bool false -> Form.false_
        | A.Const {A.cst_id=id; _} ->
          begin
            try ID.Tbl.find decl_ty_ id |> Lazy.force |> Term.const
            with Not_found ->
              errorf "could not find constant `%a`" ID.pp id
          end
        | A.Unknown v ->
          (* get or find corresponding unknown *)
          get_or_create_unknown ~st v |> Term.const
        | A.If (a,b,c) ->
          Data_term.if_
            (conv_term_rec st a)
            (conv_term_rec st b)
            (conv_term_rec st c)
        | A.App (f, l) ->
          let f = conv_term_rec st f in
          let l = List.map (conv_term_rec st) l in
          Term.app f l
        | A.Var v ->
          let v =
            Var.Tbl.get_or_add st.var_tbl ~k:v
              ~f:(fun v ->
                let ty = Var.ty v |> conv_ty in
                st.var_n <- st.var_n + 1;
                IVar.mk st.var_n ty)
          in
          Term.var v
        | A.Unop (A.U_not, t) -> Form.not_ (conv_term_rec st t)
        | A.Binop (o, t, u) ->
          let t = conv_term_rec st t in
          let u = conv_term_rec st u in
          begin match o with
            | A.B_eq -> Term.eq t u
            | A.B_leq -> Term.leq t u
            | A.B_lt -> Term.lt t u
            | A.B_and -> Form.and_ t u
            | A.B_or -> Form.or_ t u
            | A.B_imply -> Form.imply t u
          end
        | A.Undefined ty -> Term.undefined_value (conv_ty ty)
      end

    let conv_term ~st t =
      let u = conv_term_rec st t in
      Log.debugf 2
        (fun k->k "(@[conv_term@ @[%a@]@ yields: %a@])" A.T.pp t Term.pp u);
      u

    let add_stmt ~st stmt =
      Log.debugf 2
        (fun k->k "(@[add_statement@ @[%a@]@])" A.Stmt.pp stmt);
      begin match stmt with
        | A.St_data l ->
          (* declare the type, and all the constructors *)
          List.iter
            (fun {Ty.data_id; data_cstors} ->
               let ty = lazy (
                 let cstors =
                   ID.Map.to_seq data_cstors
                   |> Sequence.map
                     (fun (id_c, ty_c0) ->
                        let c = lazy (
                          let ty_c = conv_ty ty_c0 in
                          Cst.make_cstor id_c ty_c
                            ~from:(A.Cst.mk_cstor id_c ty_c0 |> A.T.const)
                        ) in
                        ID.Tbl.add decl_ty_ id_c c; (* declare *)
                        c)
                   |> Sequence.to_rev_list
                 in
                 Ty_h.atomic data_id cstors
               ) in
               ID.Tbl.add ty_tbl_ data_id ty;
            )
            l;
          (* force evaluation *)
          List.iter
            (fun {Ty.data_id; _} ->
               ID.Tbl.find ty_tbl_ data_id |> Lazy.force |> ignore)
            l
        | A.St_def cs ->
          (* define the mutually recursive functions *)
          List.iter
            (fun ({A.cst_id=id; cst_ty=ty; cst_def=d} as c) ->
               let rules = match d with
                 | A.Cst_def (lazy l) -> l
                 | A.Cst_cstor _ -> assert false
               in
               let ty = conv_ty ty in
               let cst = lazy (
                 Cst.make_defined_fix id ty ~from:(A.T.const c)
                   (fun cst ->
                      List.map
                        (fun (args,rhs) ->
                           let args = List.map (conv_term ~st) args
                           and rhs = conv_term ~st rhs in
                           mk_rule cst args rhs)
                        rules)
               ) in
               ID.Tbl.add decl_ty_ id cst)
            cs;
        | A.St_goal t ->
          let t = conv_term ~st t in
          Top_goals.push t;
          push_clause (Clause.make [Lit.atom t])
        | A.St_in_model l ->
          List.iter
            (fun v -> add_cst_support_ (get_or_create_unknown ~st v))
            l
      end

    let add_stmt_l l =
      let st = create() in
      List.iter (add_stmt ~st) l
  end

  module To_ast = struct
    module A = Rw_ast

    type state = {
      var_tbl : A.term IVar.Tbl.t;
      unknown_tbl : A.term Cst.Tbl.t;
    }

    let create(): state = {
      var_tbl=IVar.Tbl.create 8;
      unknown_tbl=Cst.Tbl.create 8;
    }

    let rec ty_to_ast (ty:Ty_h.t): Ty.t = match ty.ty_cell with
      | _ when ty_is_prop ty -> Ty.Prop
      | Atomic (id,_) -> Ty.const id
      | Arrow (a,b) -> Ty.arrow (ty_to_ast a) (ty_to_ast b)

    let fresh_var =
      let n = ref 0 in
      fun ty ->
        let id = ID.makef "x%d" !n in
        incr n;
        Var.make id (ty_to_ast ty)

    let term_to_ast (st:state) (t:term): A.term =
      let rec aux t = match t.term_cell with
        | _ when Form.is_true t -> A.T.bool true
        | _ when Form.is_false t -> A.T.bool false
        | Var v ->
          IVar.Tbl.get_or_add st.var_tbl ~k:v
            ~f:(fun _ ->
              Var.makef ~ty:(ty_to_ast (IVar.ty v)) "x_%d" (IVar.id v)
              |> A.T.var)
        | Const cst ->
          begin match cst.cst_from, cst.cst_kind with
            | Some t, _ -> t
            | None, Cst_cstor _ -> assert false
            | None, Cst_undef _ ->
              let v = fresh_var (Cst.ty cst) in
              let u = A.T.unknown v in
              cst.cst_from <- Some u;
              u
            | None, Cst_defined (lazy (_,rules)) ->
              let rules = lazy (
                List.map
                  (fun {rule_args; rule_rhs; _} ->
                     List.map aux rule_args, aux rule_rhs)
                  rules
              ) in
              let u =
                A.Cst.mk_def cst.cst_id (ty_to_ast t.term_ty) rules
                |> A.T.const
              in
              cst.cst_from <- Some u;
              u
          end
        | App ({term_cell=Const f;_}, [t]) when f == Form.not_c ->
          A.T.unop A.U_not (aux t)
        | App ({term_cell=Const f;_}, [t;u]) when f == Form.and_c ->
          A.T.binop A.B_and (aux t) (aux u)
        | App ({term_cell=Const f;_}, [t;u]) when f == Form.or_c ->
          A.T.binop A.B_or (aux t) (aux u)
        | Binop (op,t,u) ->
          let t = aux t and u = aux u in
          let op = match op with
            | O_eq -> A.B_eq | O_leq -> A.B_leq | O_lt -> A.B_lt
          in
          A.T.binop op t u
        | App (f,l) -> A.T.app (aux f) (List.map aux l)
        | Undefined_value ty -> A.T.undefined (ty_to_ast ty)
      in
      aux t
  end

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

  type model = Rw_model.t

  type res =
    | Sat of model
    | Unsat (* TODO: proof *)
    | Unknown of unknown

  (* follow "normal form" pointers deeply in the term *)
  let deref_deep (t:term) : term =
    let rec aux t =
      let _, _, t = Reduce.compute_nf t in
      begin match t.term_cell with
        | Var _ | Const _ -> t
        | App (f,l) -> Term.app (aux f) (List.map aux l)
        | Binop (b,t,u) -> Term.binop b (aux t) (aux u)
        | Undefined_value _ -> t
      end
    in
    aux t

  let compute_model_ () : model =
    (* compute values of meta variables *)
    let st = To_ast.create() in
    let consts =
      !model_support_
      |> Sequence.of_list
      |> Sequence.map
        (fun c ->
           (* find normal form of [c] *)
           let t = Term.const c in
           let t = deref_deep t |> To_ast.term_to_ast st in
           c.cst_id, t)
      |> ID.Map.of_seq
    in
    Rw_model.make ~consts ()

  let model_check () =
    Log.debugf 1 (fun k->k "checking model…");
    Top_goals.check()

  let clause_of_mclause (c:M.St.clause): Clause.t =
    M.Proof.to_list c |> List.map (fun a -> a.M.St.lit) |> Clause.make

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
      (Top_terms.size())
      !stat_num_propagations
      !stat_num_unif

  let do_on_exit ~on_exit =
    List.iter (fun f->f()) on_exit;
    ()

  let add_stmt_l = Conv.add_stmt_l

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
    | PS_undefined_values
    | PS_incomplete

  let pp_proof_status out = function
    | PS_depth_limited lit ->
      Format.fprintf out "(@[depth_limited@ by: %a@])" Lit.pp lit
    | PS_complete -> CCFormat.string out "complete"
    | PS_undefined_values -> CCFormat.string out "undefined_values"
    | PS_incomplete -> CCFormat.string out "incomplete"

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
        if Config.check_proof then M.Proof.check p;
        if !has_met_undefined
        then PS_undefined_values
        else if !incomplete_expansion
        then PS_incomplete
        else PS_complete
    end

  let dump_dimacs () = match Config.dimacs_file with
    | None -> ()
    | Some file ->
      Log.debugf 2 (fun k->k "dump SAT problem into file `%s`" file);
      CCIO.with_out file
        (fun oc ->
           let out = Format.formatter_of_out_channel oc in
           Format.fprintf out "@[<v>%a@]@." M.export_dimacs ())

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
            Log.debugf 1
              (fun k->k "@{<Yellow>** found SAT@} at depth %a"
                  ID.pp cur_depth);
            let m = compute_model_ () in
            do_on_exit ~on_exit;
            if check then model_check ();
            Sat m
          | M.Unsat us ->
            (* check if [max depth] literal involved in proof;
               - if yes, try next level
               - if not but [has_met_undefined=true] or some expansion
                 was not exhaustive (e.g. functions), UNKNOWN
               - else, truly UNSAT
            *)
            let p = us.SI.get_proof () in
            Log.debugf 4 (fun k->k "proof: @[%a@]@." pp_proof p);
            if Config.check_proof then M.Proof.check p;
            let status = proof_status cur_lit in
            Log.debugf 1
              (fun k->k
                  "@{<Yellow>** found Unsat@} at depth %a;@ \
                   status: %a"
                  ID.pp cur_depth pp_proof_status status);
            begin match status with
              | PS_depth_limited _ ->
                (* negation of the previous limit *)
                push_clause (Clause.make [Lit.neg cur_lit]);
                iter (ID.next ()) (* deeper! *)
              | PS_undefined_values ->
                do_on_exit ~on_exit;
                Unknown U_undefined_values
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

