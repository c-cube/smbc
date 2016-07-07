
(* This file is free software. See file "license" for more details. *)

(** {1 Solver} *)

(** {2 The Main Solver} *)

module Make(Dummy : sig end) = struct
  exception Error of string

  let errorf msg = CCFormat.ksprintf msg ~f:(fun s -> raise (Error s))

  (* main term cell *)
  type term = {
    mutable term_id: int; (* unique ID *)
    term_ty: ty_h;
    term_cell: term_cell;
    mutable term_nf: (term * explanation) option;
      (* normal form + explanation of why *)
    mutable term_watchers: term list; (* terms watching this term's nf *)
  }

  (* term shallow structure *)
  and term_cell =
    | True
    | False
    | DB of db (* de bruijn indice *)
    | Const of cst
    | App of term * term list
    | Fun of ty_h * term
    | If of term * term * term
    | Match of term * (ty_h list * term) ID.Map.t
    | Builtin of builtin

  and db = int * ty_h

  and builtin =
    | B_not of term
    | B_eq of term * term
    | B_and of term * term
    | B_or of term * term
    | B_imply of term * term

  (* TODO: function [explanation -> level], using max *)

  (* FIXME: add a level in there *)
  (* explain why the normal form *)
  and explanation_atom =
    | E_choice of cst * term (* assertion [c --> t] *)
    | E_lit of term * bool (* decision [lit =/!= true] *)

  (* bag of atomic explanations. It is optimized for traversal
     and fast cons/snoc/append *)
  and explanation=
    | E_empty
    | E_leaf of explanation_atom
    | E_append of explanation * explanation

  and cst = {
    cst_id: ID.t;
    cst_kind: cst_kind;
  }

  and cst_kind =
    | Cst_bool
    | Cst_undef of ty_h * cst_info
    | Cst_cstor of ty_h
    | Cst_defined of ty_h * term lazy_t

  and cst_info = {
    cst_depth: int lazy_t;
    (* refinement depth, used for iterative deepening *)
    cst_parent: (cst * term) lazy_t option;
    (* if const was created as argument of another const in
       a given case *)
    mutable cst_cases : term list option;
    (* cover set (lazily evaluated) *)
    mutable cst_cases_blocked: term list;
    (* parts of cover set forbidden in current branch *)
  }

  (* Hashconsed type *)
  and ty_h = {
    ty_id: int;
    ty_cell: ty_cell;
  }

  and ty_def =
    | Uninterpreted (* uninterpreted type TODO *)
    | Data of cst lazy_t list (* set of constructors *)

  and ty_cell =
    | Prop
    | Atomic of ID.t * ty_def
    | Arrow of ty_h * ty_h

  module Ty = struct
    type t = ty_h

    let view t = t.ty_cell

    let equal a b = a.ty_id = b.ty_id
    let compare a b = CCOrd.int_ a.ty_id b.ty_id
    let hash a = a.ty_id

    module W = Weak.Make(struct
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
      end)

    (* hashcons terms *)
    let hashcons_ =
      let tbl_ = W.create 128 in
      let n_ = ref 0 in
      fun ty_cell ->
        let t = { ty_cell; ty_id = !n_; } in
        let t' = W.merge tbl_ t in
        if t == t' then incr n_;
        t'

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
      | Atomic (id, def) ->
        let s = match def with
          | Uninterpreted -> ""
          | Data _ -> " (data)"
        in
        Format.fprintf out "%a%s" ID.pp id s
      | Arrow (a, b) ->
        Format.fprintf out "(@[->@ %a@ %a@])" pp a pp b

    (* representation as a single identifier *)
    let rec mangle t : string = match t.ty_cell with
      | Prop -> "prop"
      | Atomic (id,_) -> ID.to_string id
      | Arrow (a,b) -> mangle a ^ "_" ^ mangle b
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
    type 'a t = {
      st: 'a option list;
      size: int;
    }

    let push x env = { size=env.size+1; st=Some x :: env.st }
    let push_l l env = List.fold_left (fun e x -> push x e) env l
    let push_none env = { size=env.size+1; st=None::env.st }
    let push_none_l l env = List.fold_left (fun e _ -> push_none e) env l
    let empty = {st=[]; size=0}
    let singleton x = {st=[Some x]; size=1}
    let size env = env.size
    let get ((n,_):DB.t) env : _ option =
      if n < env.size then List.nth env.st n else None
  end

  module Typed_cst = struct
    type t = cst
    type _cst_kind = cst_kind
    type _cst_info = cst_info
    type cst_kind = _cst_kind
    type cst_info = _cst_info

    let id t = t.cst_id
    let kind t = t.cst_kind

    let ty_of_kind = function
      | Cst_bool -> Ty.prop
      | Cst_defined (ty, _)
      | Cst_undef (ty, _)
      | Cst_cstor ty -> ty

    let ty t = ty_of_kind t.cst_kind

    let make cst_id cst_kind = {cst_id; cst_kind}
    let make_bool id = make id Cst_bool
    let make_cstor id ty =
      let _, ret = Ty.unfold ty in
      assert (Ty.is_data ret);
      make id (Cst_cstor ty)
    let make_defined id ty t = make id (Cst_defined (ty, t))

    let make_undef ?parent id ty =
      let info =
        let cst_depth = lazy (match parent with
          | Some (lazy ({cst_kind=Cst_undef (_, i); _}, _)) ->
            Lazy.force i.cst_depth + 1
          | Some _ ->
            invalid_arg "make_const: parent should be a constant"
          | None -> 0
        ) in
        { cst_depth; cst_parent=parent;
          cst_cases=None; cst_cases_blocked=[]; }
      in
      make id (Cst_undef (ty, info))

    let equal a b = ID.equal a.cst_id b.cst_id
    let compare a b = ID.compare a.cst_id b.cst_id
    let hash t = ID.hash t.cst_id
    let pp out a = ID.pp out a.cst_id

    module Map = CCMap.Make(struct
        type t = cst
        let compare = compare
      end)
  end

  module Backtrack = struct
    type level = int

    let dummy_level = -1

    type stack_cell =
      | S_nil
      | S_level of level * stack_cell
      | S_set_nf of
          term * (term * explanation) option * stack_cell
          (* t1.nf <- t2 *)
      | S_set_watcher of term * term list * stack_cell
          (* t1.watchers <- l2 *)
      | S_set_forbidden of cst_info * term list * stack_cell

    type stack = {
      mutable stack_level: int;
      mutable stack: stack_cell;
    }

    (* the global stack *)
    let st_ : stack = {
      stack_level = 0;
      stack = S_nil;
    }

    let backtrack (l:level): unit =
      let rec aux l st = match st with
        | S_level (l', st') ->
          if l=l'
          then st' (* stop *)
          else aux l st' (* continue *)
        | S_nil -> assert false
        | S_set_nf (t, nf, st') ->
          t.term_nf <- nf;
          aux l st'
        | S_set_watcher (t, ts, st') ->
          t.term_watchers <- ts;
          aux l st'
        | S_set_forbidden (c, ts, st') ->
          c.cst_cases_blocked <- ts;
          aux l st'
      in
      st_.stack <- aux l st_.stack

    let cur_level () = st_.stack_level

    let push_level () : level =
      let l = st_.stack_level in
      st_.stack_level <- l+1;
      st_.stack <- S_level (l, st_.stack);
      l

    let push_set_nf_ (t:term) =
      st_.stack <- S_set_nf (t, t.term_nf, st_.stack)

    let push_set_watcher_ (t:term) =
      st_.stack <- S_set_watcher (t, t.term_watchers, st_.stack)

    let push_set_forbidden (c:cst_info) =
      st_.stack <- S_set_forbidden (c, c.cst_cases_blocked, st_.stack)
  end

  module Term = struct
    type t = term

    let sub_hash (t:term): int = t.term_id

    (* shallow hash *)
    let term_hash_ (t:term) : int = match t.term_cell with
      | True -> 1
      | False -> 2
      | DB d -> Hash.combine DB.hash 3 d
      | Const c -> Hash.combine Typed_cst.hash 4 c
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
      | Builtin (B_not t) -> Hash.combine2 20 t.term_id
      | Builtin (B_and (t1,t2)) -> Hash.combine3 21 t1.term_id t2.term_id
      | Builtin (B_or (t1,t2)) -> Hash.combine3 22 t1.term_id t2.term_id
      | Builtin (B_imply (t1,t2)) -> Hash.combine3 23 t1.term_id t2.term_id
      | Builtin (B_eq (t1,t2)) -> Hash.combine3 24 t1.term_id t2.term_id

    (* equality that relies on physical equality of subterms *)
    let term_eq_ t1 t2 : bool = match t1.term_cell, t2.term_cell with
      | True, True
      | False, False -> true
      | DB x, DB y -> DB.equal x y
      | Const c1, Const c2 -> Typed_cst.equal c1 c2
      | App (f1, l1), App (f2, l2) ->
        f1 == f2 && CCList.equal (==) l1 l2
      | Fun (ty1,f1), Fun (ty2,f2) -> Ty.equal ty1 ty2 && f1 == f2
      | If (a1,b1,c1), If (a2,b2,c2) ->
        a1 == a2 && b1 == b2 && c1 == c2
      | Match (u1, m1), Match (u2, m2) ->
        u1 == u2 &&
        ID.Map.for_all
          (fun k1 v1 ->
             try v1 == (ID.Map.find k1 m2)
             with Not_found -> false)
          m1
        &&
        ID.Map.for_all (fun k2 _ -> ID.Map.mem k2 m1) m2
      | Builtin b1, Builtin b2 ->
        begin match b1, b2 with
          | B_not t1, B_not t2 -> t1 == t2
          | B_and (a1,b1), B_and (a2,b2)
          | B_or (a1,b1), B_or (a2,b2)
          | B_eq (a1,b1), B_eq (a2,b2)
          | B_imply (a1,b1), B_imply (a2,b2) -> a1 == a2 && b1 == b2
          | B_not _, _ | B_and _, _ | B_eq _, _
          | B_or _, _ | B_imply _, _ -> false
        end
      | True, _
      | False, _
      | DB _, _
      | Const _, _
      | App _, _
      | Fun _, _
      | If _, _
      | Match _, _
      | Builtin _, _ -> false

    module W = Weak.Make(struct
        type t = term
        let equal = term_eq_
        let hash = term_hash_
      end)

    (* hashconsing function *)
    let hashcons_ =
      let tbl_ : W.t = W.create 1024 in
      let term_count_ : int ref = ref 0 in
      fun t ->
        let t' = W.merge tbl_ t in
        if t == t' then (
          t.term_id <- !term_count_;
          incr term_count_

        ) else (
          assert (t'.term_id >= 0);
        );
        t'

    let mk_bool_ (b:bool) : term =
      let t = {
        term_id= -1;
        term_ty=Ty.prop;
        term_cell=if b then True else False;
        term_nf=None;
        term_watchers=[];
      } in
      hashcons_ t

    let true_ = mk_bool_ true
    let false_ = mk_bool_ false

    let mk_term_ cell ~ty : term =
      let t = {
        term_id= -1;
        term_ty=ty;
        term_cell=cell;
        term_nf=None;
        term_watchers=[];
      } in
      hashcons_ t

    let db d = mk_term_ (DB d) ~ty:(DB.ty d)

    let const c = mk_term_ (Const c) ~ty:(Typed_cst.ty c)

    let add_watcher ~watcher t =
      Backtrack.push_set_watcher_ t; (* upon backtrack *)
      t.term_watchers <- watcher :: t.term_watchers

    let add_watcher_l ~watcher l = List.iter (add_watcher ~watcher) l

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
        let ty = app_ty_ f.term_ty l in
        let t, f = match f.term_cell with
          | App (f1, l1) ->
            let l' = l1 @ l in
            let t = mk_term_ (App (f1, l')) ~ty in
            t, f1
          | _ -> mk_term_ (App (f,l)) ~ty, f
        in
        (* watch head, not arguments *)
        add_watcher ~watcher:t f;
        t

    let app_cst f l = app (const f) l

    let fun_ ty body =
      let ty' = Ty.arrow ty body.term_ty in
      (* do not add watcher: propagation under λ forbidden *)
      mk_term_ (Fun (ty, body)) ~ty:ty'

    (* TODO: check types *)

    let match_ u m =
      let ty =
        let _, (_,rhs) = ID.Map.choose m in
        rhs.term_ty
      in
      let t = mk_term_ (Match (u,m)) ~ty in
      add_watcher ~watcher:t u; (* propagate only from [u] *)
      t

    let if_ a b c =
      assert (Ty.equal b.term_ty c.term_ty);
      let t = mk_term_ (If (a,b,c)) ~ty:b.term_ty in
      add_watcher ~watcher:t a; (* propagate under test only *)
      t

    let builtin_ b =
      let t = mk_term_ (Builtin b) ~ty:Ty.prop in
      begin match b with
        | B_not u -> add_watcher ~watcher:t u
        | B_and (a,b)
        | B_or (a,b)
        | B_eq (a,b)
        | B_imply (a,b) -> add_watcher_l ~watcher:t [a;b]
      end;
      t

    let not_ t = match t.term_cell with
      | True -> false_
      | False -> true_
      | Builtin (B_not t') -> t'
      | _ -> builtin_ (B_not t)
    let and_ a b = builtin_ (B_and (a,b))
    let or_ a b = builtin_ (B_or (a,b))
    let imply a b = builtin_ (B_imply (a,b))
    let eq a b = builtin_ (B_eq (a,b))
    let neq a b = not_ (eq a b)

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
          acc, B_and (a, b)
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

    let builtin_to_seq b yield = match b with
      | B_not t -> yield t
      | B_and (a,b)
      | B_or (a,b)
      | B_imply (a,b)
      | B_eq (a,b) -> yield a; yield b

    let ty t = t.term_ty

    let equal a b = a==b
    let hash t = t.term_id
    let compare a b = CCOrd.int_ a.term_id b.term_id

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
          | Builtin b -> builtin_to_seq b aux
          | Fun (_, body) -> aux body
      in
      aux t

    let fpf = Format.fprintf
    let pp_list_ pp out l =
      CCFormat.list ~start:"" ~stop:"" ~sep:" " pp out l

    let rec pp out t = match t.term_cell with
      | True -> CCFormat.string out "true"
      | False -> CCFormat.string out "false"
      | DB d -> DB.pp out d
      | Const c -> Typed_cst.pp out c
      | App (f,l) ->
        fpf out "(@[%a %a@])" pp f (pp_list_ pp) l
      | Fun (ty,f) ->
        fpf out "(@[fun %a.@ %a@])" Ty.pp ty pp f
      | If (a, b, c) ->
        fpf out "(@[if %a@ %a@ %a@])" pp a pp b pp c
      | Match (t,m) ->
        let pp_bind out (id,(tys,rhs)) = match tys with
          | [] -> fpf out "(@[%a %a@])" ID.pp id pp rhs
          | _::_ ->
            fpf out "(@[(@[%a@ %a@])@ %a@])"
              ID.pp id (pp_list_ Ty.pp) tys pp rhs
        in
        let print_map = CCFormat.seq ~start:"" ~stop:"" ~sep:" " pp_bind in
        fpf out "(@[match %a@ (@[<hv>%a@])@])"
          pp t print_map (ID.Map.to_seq m)
      | Builtin (B_not t) -> fpf out "(@[not@ %a@])" pp t
      | Builtin (B_and (a,b)) -> fpf out "(@[and@ %a@ %a@])" pp a pp b
      | Builtin (B_or (a,b)) -> fpf out "(@[or@ %a@ %a@])" pp a pp b
      | Builtin (B_imply (a,b)) -> fpf out "(@[imply@ %a@ %a@])" pp a pp b
      | Builtin (B_eq (a,b)) -> fpf out "(@[=@ %a@ %a@])" pp a pp b
  end

  let exp_empty = E_empty
  let exp_singleton e = E_leaf e
  let exp_append s1 s2 = match s1, s2 with
    | E_empty, _ -> s2
    | _, E_empty -> s1
    | _ -> E_append (s1, s2)

  let rec exp_to_seq e yield = match e with
    | E_empty -> ()
    | E_leaf x -> yield x
    | E_append (a,b) -> exp_to_seq a yield; exp_to_seq b yield

  let pp_explanation_atom out = function
    | E_choice (c,t) ->
      Format.fprintf out "(@[choice %a@ -> %a@])" Typed_cst.pp c Term.pp t
    | E_lit (t,b) ->
      Format.fprintf out "(@[lit %a@ -> %B@])" Term.pp t b

  let pp_explanation out e =
    Format.fprintf out "@[%a@]"
      (CCFormat.seq ~start:"" ~stop:"" ~sep:", " pp_explanation_atom)
      (exp_to_seq e)

  (* return [Some] iff the term is an undefined constant *)
  let as_cst_undef (t:term): (cst * Ty.t * cst_info) option =
    match t.term_cell with
      | Const ({cst_kind=Cst_undef (ty,info); _} as c) ->
        Some (c,ty,info)
      | _ -> None

  (* retrieve the normal form of [t], and the explanation
     of why [t -> normal_form(t) *)
  let normal_form (t:term) : explanation * term =
    let rec aux set t = match t.term_nf with
      | None -> set, t
      | Some (t',set') -> aux (exp_append set set') t'
    in
    match t.term_nf with
      | None -> exp_empty, t
      | Some (t',set) -> aux set t'

  let normal_form_append (e:explanation) (t:term) : explanation * term =
    let e', t' = normal_form t in
    exp_append e e', t'

  let check_eq t1 t2 =
    let _, t1' = normal_form t1 in
    let _, t2' = normal_form t2 in
    Term.equal t1' t2'

  exception Inconsistent of explanation * term
  (* semantically equivalent to [explanation => term], where
     the term evaluates to [false] *)

  (* set the normal form of [t], propagate to watchers *)
  let rec set_nf_ t new_t (e_set:explanation) : unit =
    if Term.equal t new_t then ()
    else (
      assert (t.term_nf = None);
      assert (e_set <> E_empty);
      Backtrack.push_set_nf_ t;
      t.term_nf <- Some (new_t, e_set);
      (* we just changed [t]'s normal form, ensure that [t]'s
         watching terms are up-to-date *)
      List.iter
        (fun watcher -> match watcher.term_nf with
           | Some _ -> ()   (* already reduced *)
           | None -> ignore (compute_nf DB_env.empty watcher))
        t.term_watchers;
    )

  (* compute the normal form of this term. We know at least one of its
     subterm(s) has been reduced *)
  and compute_nf
      (env:(explanation * term) lazy_t DB_env.t)
      (t:term)
    : explanation * term
    = match t.term_cell with
      | DB d ->
        begin match DB_env.get d env with
          | None -> exp_empty, t (* trivial *)
          | Some (lazy (e', t')) ->
            (* replace *)
            e', t'
        end
      | True | False | Const _ -> exp_empty, t (* always trivial *)
      | Fun _ -> exp_empty, t (* no eval under lambda *)
      | Builtin b ->
        let e, b' =
          Term.fold_map_builtin (compute_nf_add env) exp_empty b
        in
        (* try boolean reductions *)
        let t' = match b' with
          | B_not a ->
            begin match a.term_cell with
              | True -> Term.false_
              | False -> Term.true_
              | _ -> Term.not_ a
            end
          | B_and (a,b) ->
            begin match a.term_cell, b.term_cell with
              | True, _ -> b
              | _, True -> a
              | False, _
              | _, False -> Term.false_
              | _ -> Term.and_ a b
            end
          | B_or (a,b) ->
            begin match a.term_cell, b.term_cell with
              | True, _
              | _, True -> Term.true_
              | False, _ -> b
              | _, False -> a
              | _ -> Term.or_ a b
            end
          | B_imply (a,b) ->
            begin match a.term_cell, b.term_cell with
              | _, True
              | False, _ -> Term.true_
              | True, _ -> b
              | _, False -> Term.not_ a
              | _ -> Term.imply a b
            end
          | B_eq (a,b) ->
            begin match a.term_cell, b.term_cell with
              | False, False
              | True, True -> Term.true_
              | True, False
              | False, True -> Term.false_
              | _ when Term.equal a b -> Term.true_ (* syntactic *)
              | App (
                  {term_cell=Const ({cst_kind=Cst_cstor _; _} as c1); _},
                  _),
                App (
                  {term_cell=Const ({cst_kind=Cst_cstor _; _} as c2); _},
                  _)
                when not (Typed_cst.equal c1 c2) ->
                (* [c1 ... = c2 ...] --> false, as distinct constructors
                   can never be equal *)
                Term.false_
              | _ -> Term.eq a b
            end
        in
        assert (not (Term.equal t t'));
        set_nf_ t t' e;
        e, t'
      | If (a,b,c) ->
        let e_a, a' = normal_form a in
        assert (not (Term.equal a a'));
        let t' = Term.if_ a' b c in
        let e_branch, t' = match a'.term_cell with
          | True -> compute_nf env b
          | False -> compute_nf env c
          | _ -> exp_empty, t'
        in
        (* merge evidence from [a]'s normal form and [b/c]'s normal form *)
        let e = exp_append e_a e_branch in
        set_nf_ t t' e;
        e, t'
      | Match (u, m) ->
        let e_u, u' = normal_form u in
        assert (not (Term.equal u u'));
        let t' = Term.match_ u' m in
        let e_branch, t' = match u'.term_cell with
          | App ({term_cell=Const c; _}, l) ->
            begin
              try
                let tys, rhs = ID.Map.find (Typed_cst.id c) m in
                if List.length tys = List.length l
                then
                  (* evaluate arguments *)
                  let l =
                    List.map
                      (fun t -> lazy (compute_nf env t))
                      l
                  in
                  let new_env = DB_env.push_l l env in
                  compute_nf new_env rhs
                else exp_empty, t'
              with Not_found -> exp_empty, t'
            end
          | _ -> exp_empty, t'
        in
        let e = exp_append e_u e_branch in
        set_nf_ t t' e;
        e, t'
      | App (f, l) ->
        let e_f, f' = normal_form f in
        let e_reduce, new_t = match f'.term_cell, l with
          | Fun (_ty, body), arg :: other_args ->
            (* beta-reduce *)
            assert (Ty.equal _ty arg.term_ty);
            let new_env =
              DB_env.push
                (lazy (compute_nf env arg))
                env
            in
            (* eval [body], then apply it to [other_args] *)
            let e_body, body' = compute_nf new_env body in
            compute_nf_add env e_body (Term.app body' other_args)
          | _ ->
            let t' = Term.app f' l in
            exp_empty, t'
        in
        let e = exp_append e_reduce e_f in
        set_nf_ t new_t e;
        e, new_t

  and compute_nf_add
      (env:(explanation * term) lazy_t DB_env.t)
      (e : explanation)
      (t:term)
    : explanation * term
    = let e', t' = compute_nf env t in
      exp_append e e', t'

  (** {2 Literals} *)
  module Lit = struct
    type t = term
    let not_ = Term.not_

    type view =
      | V_true
      | V_false
      | V_assert of term * bool
      | V_cst_choice of cst * term * bool

    let view (t:t): view = match t.term_cell with
      | False -> V_false
      | True -> V_true
      | Builtin (B_eq (a, b)) ->
        begin match as_cst_undef a, as_cst_undef b with
          | Some (c,_,_), _ -> V_cst_choice (c,b,true)
          | None, Some (c,_,_) -> V_cst_choice (c,a,true)
          | None, None -> V_assert (t, true)
        end
      | Builtin (B_not t') ->
        begin match t'.term_cell with
          | Builtin (B_eq (a,b)) ->
              begin match as_cst_undef a, as_cst_undef b with
                | Some (c,_,_), _ -> V_cst_choice (c,b,false)
                | None, Some (c,_,_) -> V_cst_choice (c,a,false)
                | _ -> V_assert (t', false)
              end
          | _ -> V_assert (t', false)
        end
      | _ -> V_assert (t, true)

    let fresh =
      let n = ref 0 in
      fun () ->
        let id = ID.makef "#fresh_%d" !n in
        let c = Typed_cst.make_bool id in
        let res = Term.const c in
        incr n;
        res

    let dummy = fresh()

    let atom ?(sign=true) t = if sign then t else not_ t
    let eq a b = Term.eq a b
    let neq a b = Term.neq a b
    let cst_choice c t = Term.eq (Term.const c) t

    let equal = Term.equal
    let hash = Term.hash
    let compare = Term.compare
    let pp = Term.pp
    let print = pp

    (** {2 Normalization} *)

    let norm l = l, false (* TODO? *)
  end

  let explain t1 t2 : explanation =
    let e1, t1 = normal_form t1 in
    let e2, t2 = normal_form t2 in
    if not (Term.equal t1 t2)
    then invalid_arg "term.explain: not equal";
    (* merge the two explanations *)
    exp_append e1 e2

  (* build a clause that explains that [c] must be one of its
     cases *)
  let clause_of_cases (c:cst) : Lit.t list = match c.cst_kind with
    | Cst_undef (_, {cst_cases=Some l; _}) ->
      List.map (fun t -> Lit.cst_choice c t) l
    | _ -> assert false

  (** {2 Iterative Deepening} *)

  module Depth_limit : sig
    type t = private int
    val current : unit -> t
    val next : unit -> t
  end = struct
    type t = int

    let cur_ = ref 5

    let current () = !cur_

    let next () =
      cur_ := !cur_ + 5;
      !cur_

  end

  (** {2 MCSat Solver} *)

  (* terms/formulas for mcsat *)
  module M_expr
    : Msat.Expr_intf.S
      with type Term.t = term
       and type Formula.t = Lit.t
       and type proof = unit
  = struct
    module Term = struct
      type t = term
      let equal = Term.equal
      let hash = Term.hash
      let compare = Term.compare
      let print = Term.pp
    end
    module Formula = Lit

    type proof = unit (* TODO later *)
    let dummy = Lit.dummy
    let fresh = Lit.fresh
    let neg = Lit.not_
    let norm = Lit.norm
  end

  (* the "theory" part: propagations *)
  module M_th = struct
    type term = M_expr.Term.t
    type formula = M_expr.Formula.t
    type proof = M_expr.proof
    type assumption =
      | Lit of formula
      | Assign of term * term
    type slice = {
      start : int;
      length : int;
      get : int -> assumption * int;
      push : formula list -> proof -> unit;
      propagate : formula -> int -> unit;
    }

    type level = Backtrack.level

    type res =
      | Sat
      | Unsat of formula list * proof

    type eval_res =
      | Valued of bool * int
      | Unknown

    let dummy = Backtrack.dummy_level

    let current_level = Backtrack.cur_level

    let backtrack = Backtrack.backtrack

    let lit_of_exp_ (e:explanation_atom): Lit.t = match e with
      | E_lit (t, b) ->
        Lit.atom ~sign:b t
      | E_choice (cst,t) ->
        (* NOTE: hack, because mcsat doesn't accept an assignment
           in conflict clauses *)
        Lit.eq (Term.const cst) t

    let clause_of_exp_ (e:explanation): Lit.t list =
      exp_to_seq e
      |> Sequence.map lit_of_exp_
      |> Sequence.to_rev_list

    (* TODO: a good way of finding whether, during evaluation,
       some prop-typed terms reduced to true/false, so we can
       turn them into literals and propagate them via [slice] *)

    (* assert [c := new_t] and propagate *)
    let assert_choice _slice _lev (c:cst) (new_t:term) : unit =
      let t_c = Term.const c in
      assert (t_c.term_nf = None);
      (* set normal form, then compute *)
      set_nf_ t_c new_t (exp_singleton (E_choice (c, new_t)));
      ()

    (* forbid the choice [c := t];
       - propagate if only one choice remains *)
    let assert_not_choice slice level (c:cst) (t:term) : unit =
      match c.cst_kind with
        | Cst_undef (_, info) ->
          (* list of cases *)
          let cases = match info.cst_cases with
            | None -> assert false
            | Some l -> l
          in
          (* forbid [t] *)
          Backtrack.push_set_forbidden info;
          let blocked = t :: info.cst_cases_blocked in
          info.cst_cases_blocked <- blocked;
          (* find the cases not blocked yet *)
          let nonblocked =
            List.filter
              (fun t -> not (List.memq t blocked))
              cases
          in
          begin match nonblocked with
            | [] -> assert false (* should have propagated earlier *)
            | [t] ->
              (* unit propagation *)
              (* FIXME: should level be given as param? *)
              slice.propagate (Lit.cst_choice c t) level
            | _::_::_ -> ()
          end;
          ()
        | _ -> assert false

    let assert_lit slice level (l:Lit.t) : unit = match Lit.view l with
      | Lit.V_false -> assert false
      | Lit.V_true -> ()
      | Lit.V_assert (_, _) -> () (* TODO? *)
      | Lit.V_cst_choice (c, t, true) ->
        assert_choice slice level c t
      | Lit.V_cst_choice (c, t, false) ->
        assert_not_choice slice level c t

    (* propagation from the bool solver *)
    let assume slice =
      let start = slice.start in
      try
        (* TODO: propagate/use level in explanations *)
        for i = start to start + slice.length - 1 do
          let assum, level = slice.get i in
          match assum with
            | Lit lit ->
              Log.debugf 3 (fun k->k "assert_lit %a" Lit.pp lit);
              assert_lit slice level lit
            | Assign (t,u) ->
              begin match as_cst_undef t with
                | None -> assert false
                | Some (c, _, _) ->
                  Log.debugf 3
                    (fun k->k "assert_choice %a -> %a"
                        Typed_cst.pp c Term.pp u);
                  assert_choice slice level c u
              end
        done;
        Sat
      with Inconsistent (e, concl) ->
        (* conflict clause: [e => concl] *)
        let guard = clause_of_exp_ e |> List.map Lit.not_ in
        let conflict_clause = Lit.atom ~sign:true concl :: guard in
        Unsat (conflict_clause, ())

    (* make a fresh constant, with a unique name *)
    let new_cst_ =
      let n = ref 0 in
      fun ?parent name ty ->
        let id = ID.makef "?%s_%d" name !n in
        incr n;
        Typed_cst.make_undef ?parent id ty

    (* find an assignment for [t], where [t] should be an
       undefined constant *)
    let assign t = match as_cst_undef t with
      | None -> assert false
      | Some (cst, ty, info) ->
        (* develop the list of cases, if needed, and pick one *)
        let cases = match info.cst_cases with
          | Some l -> l
          | None ->
            (* expand the given type *)
            let l = match Ty.view ty with
              | Atomic (_, Data cstors) ->
                  List.map
                    (fun (lazy c) ->
                       let rec case = lazy (
                         let ty_args, _ = Typed_cst.ty c |> Ty.unfold in
                         let args =
                           List.map
                             (fun ty_arg ->
                                let basename = Ty.mangle ty_arg in
                                new_cst_ basename ty_arg
                                  ~parent:(lazy (cst, Lazy.force case))
                                |> Term.const
                             )
                             ty_args
                         in
                         Term.app_cst c args
                       ) in
                       Lazy.force case
                    )
                    cstors
              | Atomic (_, Uninterpreted) ->
                assert false (* TODO, but how? *)
              | Arrow _ ->
                assert false (* TODO: refine with fold/case/if *)
              | Prop ->
                assert false (* TODO: try true or false? *)
            in
            (* TODO: if depth is limited??? *)
            info.cst_cases <- Some l;
            l
        in
        (* find the cases not blocked yet *)
        let nonblocked =
          List.filter
            (fun t -> not (List.memq t info.cst_cases_blocked))
            cases
        in
        let res = match nonblocked with
          | [] -> assert false (* TODO: conflict *)
          | t :: _ ->
            t (* pick first available case *)
        in
        Log.debugf 3
          (fun k->k "@[assign %a -> %a@]" Typed_cst.pp cst Term.pp res);
        res

    let iter_assignable (yield:term->unit) (lit:Lit.t): unit =
      (* return the undefined sub-constants *)
      Term.to_seq lit
      |> Sequence.filter
        (fun t -> match as_cst_undef t with
           | None -> false
           | Some _ -> true)
      |> Sequence.iter yield

    let eval t : eval_res =
      let e, new_t = compute_nf DB_env.empty t in
      let level = assert false in (* FIXME: use level of e *)
      begin match new_t.term_cell with
        | True -> Valued (true, level)
        | False -> Valued (false, level)
        | _ -> Unknown
      end

    let if_sat _slice = ()
  end

  module M = Msat.Mcsolver.Make(M_expr)(M_th)(struct end)

  (** {2 Conversion} *)

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

  (* list of constants we are interested in *)
  let model_support_ : Typed_cst.t list ref = ref []

  (* TODO: transform into terms, blabla *)
  let add_statement st =
    Log.debugf 2 (fun k->k "add statement `@[%a@]`" Ast.pp_statement st);
    match st with
    | Ast.Assert t ->
      let t = conv_term [] t in
      M.assume [[t]]
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
      CCList.Ref.push_list model_support_ consts;
      let t = conv_term env t in
      M.assume [[t]]
    | Ast.TyDecl id ->
      let ty = Ty.atomic id Uninterpreted in
      ID.Tbl.add ty_tbl_ id (Lazy.from_val ty)
    | Ast.Decl (id, ty) ->
      assert (not (ID.Tbl.mem decl_ty_ id));
      let ty = conv_ty ty in
      let cst = match ty.ty_cell with
        | Arrow _
        | Atomic (_, _) ->
          Typed_cst.make_undef id ty
        | Prop -> Typed_cst.make_bool id
      in
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
           ID.Tbl.find decl_ty_ id |> Lazy.force |> ignore)
        l

  let add_statement_l = List.iter add_statement

  (** {2 Main} *)

  (* TODO: literals for iterative deepening
     TODO: main iterative deepening loop (checking unsat-core to
     see if  really unsat) *)

  type unknown =
    | U_timeout
    | U_max_depth

  type model = term Typed_cst.Map.t
  (** Map from constants to their value *)

  type res =
    | Sat of model
    | Unsat (* TODO: proof *)
    | Unknown of unknown

  let pp_model out m =
    let pp_pair out (c,t) =
      Format.fprintf out "(@[%a %a@])" ID.pp (Typed_cst.id c) Term.pp t
    in
    Format.fprintf out "(@[%a@])"
      (CCFormat.list ~start:"" ~stop:"" ~sep:" " pp_pair)
      (Typed_cst.Map.to_list m)

  let compute_model_ () : model =
    !model_support_
    |> Sequence.of_list
    |> Sequence.map
      (fun c ->
         (* find normal form of [c] *)
         let t = Term.const c in
         let _, t = normal_form t in
         c, t)
    |> Typed_cst.Map.of_seq

  (* TODO: iterative deepening *)
  let check () =
    try
      M.solve ();
      let m = compute_model_ () in
      Sat m
    with M.Unsat ->
      Unsat (* TODO: check if max depth involved *)
end

