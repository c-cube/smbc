
(* This file is free software. See file "license" for more details. *)

(** {1 Solver} *)

(** {2 Typed De Bruijn indices} *)
module DB = struct
  type t = int * Ty.t
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

(** {2 The Main Solver} *)

(* TODO: remove term_explain, except the "choice" part
   TODO: big step semantics for reduction, computing WHNF
   TODO: pointer to normal form: (term * explanation_set) option
   TODO: explanation_set as unbalanced tree with O(1) append *)

module Make(Dummy : sig end) = struct
  (* main term cell *)
  type term = {
    mutable term_id: int; (* unique ID *)
    term_ty: Ty.t;
    term_cell: term_cell;
    mutable term_nf: (term * explanation) option;
      (* normal form + explanation of why *)
    mutable term_watchers: term list; (* terms watching this term's nf *)
    mutable term_distinct: term list; (* cannot be equal to those *)
  }

  (* term shallow structure *)
  and term_cell =
    | True
    | False
    | DB of DB.t (* de bruijn indice *)
    | Const of cst
    | App of term * term list
    | Fun of Ty.t * term
    | If of term * term * term
    | Match of term * (Ty.t list * term) ID.Map.t
    | Builtin of builtin

  and builtin =
    | B_not of term
    | B_eq of term * term
    | B_and of term * term
    | B_or of term * term
    | B_imply of term * term

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
    | Cst_undef of Ty.t * cst_info
    | Cst_cstor of Ty.t * Ty.data
    | Cst_defined of Ty.t * term

  and cst_info = {
    cst_depth: int;
    (* refinement depth, used for iterative deepening *)
    cst_parent: cst option;
    (* if const was created as argument of another const *)
    mutable cst_cases : term list option;
    (* cover set (lazily evaluated) *)
  }

  module Typed_cst = struct
    type t = cst
    type _cst_kind = cst_kind
    type _cst_info = cst_info
    type cst_kind = _cst_kind
    type cst_info = _cst_info

    let id t = t.cst_id
    let kind t = t.cst_kind

    let ty_of_kind = function
      | Cst_defined (ty, _)
      | Cst_undef (ty, _)
      | Cst_cstor (ty,_) -> ty

    let ty t = ty_of_kind t.cst_kind

    let make cst_id cst_kind = {cst_id; cst_kind}
    let make_cstor id ty data = make id (Cst_cstor (ty,data))
    let make_defined id ty t = make id (Cst_defined (ty, t))

    let make_undef ?parent id ty =
      let info = match parent with
        | None -> { cst_depth=0; cst_parent=None; cst_cases=None }
        | Some p ->
          let depth = match p.cst_kind with
            | Cst_undef (_, i) -> i.cst_depth + 1
            | _ -> invalid_arg "make_const: parent should be a constant"
          in
          { cst_depth=depth; cst_parent=Some p; cst_cases=None }
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
      | S_set_distinct of term * term list * stack_cell
          (* t1.distinct <- l2 *)
      | S_set_watcher of term * term list * stack_cell
          (* t1.watchers <- l2 *)

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
        | S_set_nf (t, nf, st') -> t.term_nf <- nf; aux l st'
        | S_set_distinct (t, ts, st') -> t.term_distinct <- ts; aux l st'
        | S_set_watcher (t, ts, st') -> t.term_watchers <- ts; aux l st'
      in
      st_.stack <- aux l st_.stack

    let cur_level () = st_.stack_level

    let push_level () : level =
      let l = st_.stack_level in
      st_.stack_level <- l+1;
      st_.stack <- S_level (l, st_.stack);
      l

    let push_set_distinct_ (t:term) =
      st_.stack <- S_set_distinct (t, t.term_distinct, st_.stack)

    let push_set_nf_ (t:term) =
      st_.stack <- S_set_nf (t, t.term_nf, st_.stack)

    let push_set_watcher_ (t:term) =
      st_.stack <- S_set_watcher (t, t.term_watchers, st_.stack)
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
        term_distinct=[];
      } in
      hashcons_ t

    let true_ = mk_bool_ true
    let false_ = mk_bool_ false

    (* true and false: incompatible *)
    let () =
      true_.term_distinct <- [false_];
      false_.term_distinct <- [true_];
      ()

    let mk_term_ cell ~ty : term =
      let t = {
        term_id= -1;
        term_ty=ty;
        term_cell=cell;
        term_nf=None;
        term_watchers=[];
        term_distinct=[];
      } in
      hashcons_ t

    let db d = mk_term_ (DB d) ~ty:(DB.ty d)

    let const c = mk_term_ (Const c) ~ty:(Typed_cst.ty c)

    let add_watcher ~watcher t =
      Backtrack.push_set_watcher_ t; (* upon backtrack *)
      t.term_watchers <- watcher :: t.term_watchers

    let add_watcher_l ~watcher l = List.iter (add_watcher ~watcher) l

    (* type of an application *)
    let rec app_ty_ ty l : Ty.t = match ty, l with
      | _, [] -> ty
      | Ty.Arrow (ty_a,ty_rest), a::tail ->
        if Ty.equal ty_a a.term_ty
        then app_ty_ ty_rest tail
        else
          Ty.ill_typed "expected `@[%a@]`,@ got `@[%a@]`"
            Ty.pp ty_a Ty.pp a.term_ty
      | (Ty.Prop | Ty.Const _), a::_ ->
        Ty.ill_typed "cannot apply ty `@[%a@]`@ to `@[%a@]`"
          Ty.pp ty Ty.pp a.term_ty

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

    let not_ t = builtin_ (B_not t)
    let and_ a b = builtin_ (B_and (a,b))
    let or_ a b = builtin_ (B_or (a,b))
    let imply a b = builtin_ (B_imply (a,b))
    let eq a b = builtin_ (B_eq (a,b))

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

    (* evaluate the De Bruijn indices *)
    let rec eval_db (env:term DB_env.t) (t:term) : term =
      match t.term_cell with
      | DB d ->
        begin match DB_env.get d env with
          | None -> t
          | Some t' -> t'
        end
      | Const _
      | True
      | False -> t
      | Fun (ty, body) ->
        let body' = eval_db (DB_env.push_none env) body in
        fun_ ty body'
      | Match (u, m) ->
        let u = eval_db env u in
        let m =
          ID.Map.map
            (fun (tys,rhs) -> tys, eval_db (DB_env.push_none_l tys env) rhs)
            m
        in
        match_ u m
      | If (a,b,c) -> if_ (eval_db env a) (eval_db env b) (eval_db env c)
      | App (f, l) -> app (eval_db env f) (eval_db_l env l)
      | Builtin b -> builtin_ (map_builtin (eval_db env) b)

    and eval_db_l env l = List.map (eval_db env) l

    let ty t = t.term_ty

    let equal a b = a==b
    let hash t = t.term_id
    let compare a b = CCOrd.int_ a.term_id b.term_id

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

  exception Inconsistent of term * term * term * term

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
        let t' = Term.builtin_ b' in
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

  (* assert [c := new_t] and propagate *)
  let assert_choice (c:cst) (new_t:term) : unit =
    let t_c = Term.const c in
    assert (t_c.term_nf = None);
    set_nf_ t_c new_t (exp_singleton (E_choice (c, new_t)));
    ()

  let assert_neq t1 t2 : unit =
    let _, t1 = normal_form t1 in
    let _, t2 = normal_form t2 in
    if Term.equal t1 t2
    then raise (Inconsistent (t1, t2, t1, t2))
    else (
      Backtrack.push_set_distinct_ t1;
      Backtrack.push_set_distinct_ t2;
      t1.term_distinct <- t2 :: t1.term_distinct;
      t2.term_distinct <- t1 :: t2.term_distinct;
    )

  let pp_explanation out = function
    | E_choice (c,t) ->
      Format.fprintf out "(@[choice %a@ -> %a@])" Typed_cst.pp c Term.pp t
    | E_lit (t,b) ->
      Format.fprintf out "(@[lit %a@ -> %B@])" Term.pp t b

  let explain t1 t2 : explanation =
    let e1, t1 = normal_form t1 in
    let e2, t2 = normal_form t2 in
    if not (Term.equal t1 t2)
    then invalid_arg "term.explain: not equal";
    (* merge the two explanations *)
    exp_append e1 e2

  (** {2 Literals} *)
  module Lit = struct
    type cell =
      | Fresh of int (* fresh atomic lits *)
      | Atom of term (* signed atom *)

    type t = {
      cell: cell;
      sign: bool;
    }

    let not_ t = { t with sign = not t.sign }

    let fresh =
      let n = ref 0 in
      fun () ->
        let res = {cell=Fresh !n; sign=true} in
        incr n;
        res

    let dummy = fresh()

    let atom ?(sign=true) t = {sign; cell=Atom t}
    let eq a b = atom ~sign:true (Term.eq a b)
    let neq a b = atom ~sign:false (Term.eq a b)

    let to_int_ c = match c with
      | Fresh _ -> 0
      | Atom _ -> 1

    let (<?>) = CCOrd.(<?>)

    let compare_cell l1 l2 = match l1, l2 with
      | Fresh i1, Fresh i2 -> CCOrd.int_ i1 i2
      | Atom t1, Atom t2 -> Term.compare t1 t2
      | Fresh _, _
      | Atom _, _
        -> CCOrd.int_ (to_int_ l1) (to_int_ l2)

    let compare l1 l2 =
      CCOrd.bool_ l1.sign l2.sign
      <?> (compare_cell, l1.cell, l2.cell)

    let equal a b = compare a b = 0

    let hash_cell = function
      | Fresh i -> Hash.combine2 0 i
      | Atom t ->
        Hash.combine2 1 (Term.hash t)

    let hash l = Hash.combine2 (Hash.bool l.sign) (hash_cell l.cell)

    let pp out l =
      let pp_cell out = function
        | Fresh i -> Format.fprintf out "<fresh %d>" i
        | Atom t -> Term.pp out t
      in
      if l.sign
      then pp_cell out l.cell
      else Format.fprintf out "[@<1>¬@[%a@]]" pp_cell l.cell

    let print = pp

    (** {2 Normalization} *)

    let norm l = l, false (* TODO? *)
  end

  (** {2 MCSat Solver} *)

  (* terms/formulas for mcsat *)
  module M_expr
    : Msat.Expr_intf.S
      with type Term.t = term
       and type Formula.t = Lit.t
  = struct
    module Term = struct
      type t = term
      let equal = Term.equal
      let hash = Term.hash
      let compare = Term.compare
      let print = Term.pp
    end
    module Formula = Lit

    type proof = explanation list
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
        Lit of formula
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

    let assume slice = assert false (* TODO *)

      (* TODO
    val assume : slice -> res
    val backtrack : level -> unit
    val assign : term -> term
    val iter_assignable :
      (term -> unit) -> formula -> unit
    val eval : formula -> eval_res
    val if_sat : slice -> unit
         *)


  end

  module M = Msat.Mcsolver.Make(M_expr)(M_th)

  (** {2 Main} *)

  (* TODO: literals for iterative deepening
     TODO: main iterative deepening loop (checking unsat-core to
     see if  really unsat) *)

  (* TODO
  val add_statement : Ast.statement -> unit

  val add_statement_l : Ast.statement list -> unit

  type model = term R.CstMap.t
  (** Map from constants to their value *)

  type unknown =
    | U_timeout
    | U_max_depth

  type res =
    | Sat of model
    | Unsat (* TODO: proof *)
    | Unknown of unknown

  val check : ?max_depth:int -> unit -> res
  (** [check ()] checks the satisfiability of the current set of statements *)


  *)
end

