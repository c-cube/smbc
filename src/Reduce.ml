
(* This file is free software. See file "license" for more details. *)

(** {1 Functional Congruence Closure} *)

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

(** {2 Congruence Closure} *)

module Make(Dummy : sig end) = struct
  (* main term cell *)
  type term = {
    mutable term_id: int; (* unique ID *)
    term_ty: Ty.t;
    term_cell: term_cell;
    mutable term_nf: term option; (* normal form *)
    mutable term_nf_why: term_explain list; (* proof for normal form *)
    mutable term_parents: term list; (* immediate superterms *)
    mutable term_distinct: term list; (* cannot be equal to those *)
  }

  (* term shallow structure *)
  and term_cell =
    | True
    | False
    | DB of DB.t (* de bruijn indice *)
    | Const of term Typed_cst.t
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
  and term_explain =
    | E_congruence of term * term (* this immediate subterm did reduce into that term*)
    | E_beta of term * term (* beta-reduct (fun/arg) *)
    | E_if of term * term * term (* if-reduction (full term/test/branch) *)
    | E_match of term * term * term (* match-reduction (full term/matched/branch) *)
    | E_choice of term Typed_cst.t * term (* assertion [c --> t] *)

  type level = int

  type stack_cell =
    | S_nil
    | S_level of level * stack_cell
    | S_set_nf of
        term * term option * term_explain list * stack_cell (* t1.nf <- t2 *)
    | S_set_distinct of term * term list * stack_cell (* t1.distinct <- l2 *)
    | S_set_parent of term * term list * stack_cell (* t1.parents <- l2 *)

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
      | S_set_nf (t, nf, e, st') -> t.term_nf <- nf; t.term_nf_why <- e; aux l st'
      | S_set_distinct (t, ts, st') -> t.term_distinct <- ts; aux l st'
      | S_set_parent (t, ts, st') -> t.term_parents <- ts; aux l st'
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
    st_.stack <- S_set_nf (t, t.term_nf, t.term_nf_why, st_.stack)

  let push_set_parent_ (t:term) =
    st_.stack <- S_set_parent (t, t.term_parents, st_.stack)

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
        let hash_m = Hash.seq (Hash.pair ID.hash hash_case) (ID.Map.to_seq m) in
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
        term_nf_why=[];
        term_parents=[];
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
        term_nf_why=[];
        term_parents=[];
        term_distinct=[];
      } in
      hashcons_ t

    let db d = mk_term_ (DB d) ~ty:(DB.ty d)

    let const c = mk_term_ (Const c) ~ty:(Typed_cst.ty c)

    let add_parent ~parent t =
      push_set_parent_ t; (* upon backtrack *)
      t.term_parents <- parent :: t.term_parents

    let add_parent_l ~parent l = List.iter (add_parent ~parent) l

    (* type of an application *)
    let rec app_ty_ ty l : Ty.t = match ty, l with
      | _, [] -> ty
      | Ty.Arrow (ty_a,ty_rest), a::tail ->
        if Ty.equal ty_a a.term_ty
        then app_ty_ ty_rest tail
        else
          Ty.ill_typed "expected `@[%a@]`,@ got `@[%a@]`" Ty.pp ty_a Ty.pp a.term_ty
      | (Ty.Prop | Ty.Const _), a::_ ->
        Ty.ill_typed "cannot apply ty `@[%a@]`@ to `@[%a@]`" Ty.pp ty Ty.pp a.term_ty

    let app f l = match l with
      | [] -> f
      | _ ->
        let ty = app_ty_ f.term_ty l in
        let t, sub = match f.term_cell with
          | App (f1, l1) ->
            let l' = l1 @ l in
            let t = mk_term_ (App (f1, l')) ~ty in
            t, f1 :: l'
          | _ -> mk_term_ (App (f,l)) ~ty, f :: l
        in
        add_parent_l ~parent:t sub;
        t

    let fun_ ty body =
      let ty' = Ty.arrow ty body.term_ty in
      (* do not add parent: propagation under λ forbidden *)
      mk_term_ (Fun (ty, body)) ~ty:ty'

    (* TODO: check types *)

    let match_ u m =
      let ty =
        let _, (_,rhs) = ID.Map.choose m in
        rhs.term_ty
      in
      let t = mk_term_ (Match (u,m)) ~ty in
      add_parent ~parent:t u; (* propagate only from [u] *)
      t

    let if_ a b c =
      assert (Ty.equal b.term_ty c.term_ty);
      let t = mk_term_ (If (a,b,c)) ~ty:b.term_ty in
      add_parent ~parent:t a; (* propagate under test only *)
      t

    let builtin_ b =
      let t = mk_term_ (Builtin b) ~ty:Ty.prop in
      begin match b with
        | B_not u -> add_parent ~parent:t u
        | B_and (a,b)
        | B_or (a,b)
        | B_eq (a,b)
        | B_imply (a,b) -> add_parent_l ~parent:t [a;b]
      end;
      t

    let not_ t = builtin_ (B_not t)
    let and_ a b = builtin_ (B_and (a,b))
    let or_ a b = builtin_ (B_or (a,b))
    let imply a b = builtin_ (B_imply (a,b))
    let eq a b = builtin_ (B_eq (a,b))

    let map_builtin f = function
      | B_not t -> B_not (f t)
      | B_and (a,b) -> B_and (f a, f b)
      | B_or (a,b) -> B_or (f a, f b)
      | B_eq (a,b) -> B_eq (f a, f b)
      | B_imply (a,b) -> B_imply (f a, f b)

    (* evaluate the De Bruijn indices *)
    let rec eval_db (env:term DB_env.t) (t:term) : term = match t.term_cell with
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

    (* TODO: meta-variables? *)

    let ty t = t.term_ty

    let equal a b = a==b

    let compare a b = CCOrd.int_ a.term_id b.term_id

    let fpf = Format.fprintf
    let pp_list_ pp out l = CCFormat.list ~start:"" ~stop:"" ~sep:" " pp out l

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

    (* TODO: most of the interface, interning, etc.
       be careful to exploit DAG structure as much as possible *)
  end

  (* retrieve the normal form of [t] *)
  let normal_form (t:term) : term =
    let rec aux t = match t.term_nf with
      | None -> t
      | Some t' -> aux t'
    in
    match t.term_nf with
      | None -> t
      | Some t' -> aux t'

  let check_eq t1 t2 =
    Term.equal (normal_form t1) (normal_form t2)

  exception Inconsistent of term * term * term * term

  (* set the normal form of [t] *)
  let set_nf_ t new_t e : unit =
    if Term.equal t new_t then ()
    else (
      assert (t.term_nf = None);
      assert (t.term_nf_why = []);
      assert (e <> []);
      push_set_nf_ t;
      t.term_nf <- Some new_t;
      t.term_nf_why <- e;
    )

  (* we just changed [t]'s normal form, propagate to parent terms *)
  let rec propagate_ t new_t : unit =
    let e = E_congruence (t, new_t) in
    (* now iterate on parents *)
    List.iter
      (fun parent -> match parent.term_nf with
         | Some _ -> ()   (* already reduced *)
         | None ->
           let parent' = compute_nf parent [e] in
           propagate_ parent parent')
      t.term_parents;
    ()

  (* compute the normal form of this term. We know at least one of its
     subterm(s) has been reduced *)
  and compute_nf t e : term = match t.term_cell with
    | DB _ | True | False | Const _ -> assert false
    | Fun _ -> t
    | Builtin b ->
      let t' = Term.builtin_ (Term.map_builtin normal_form b) in
      assert (not (Term.equal t t'));
      set_nf_ t t' e;
      t'
    | If (a,b,c) ->
      let a' = normal_form a in
      assert (not (Term.equal a a'));
      let t' = Term.if_ a' b c in
      let t', e' = match a'.term_cell with
        | True -> compute_nf b [], E_if (t', a', b) :: e
        | False -> compute_nf c [], E_if (t', a', c) :: e
        | _ -> t', e
      in
      set_nf_ t t' e';
      t'
    | Match (u, m) ->
      let u' = normal_form u in
      assert (not (Term.equal u u'));
      let t' = Term.match_ (normal_form u) m in
      let t', e' = match u'.term_cell with
        | App ({term_cell=Const c; _}, l) ->
          begin
            try
              let tys, rhs = ID.Map.find (Typed_cst.id c) m in
              if List.length tys = List.length l
              then
                let env = DB_env.empty |> DB_env.push_l l in
                Term.eval_db env rhs, E_match (t', u', rhs) :: e
              else t', e
            with Not_found -> t', e
          end
        | _ -> t', e
      in
      set_nf_ t t' e';
      t'
    | App (f, l) ->
      let f' = normal_form f in
      let l' = List.map normal_form l in
      let t' = Term.app f' l' in
      let t', e' = match f'.term_cell, l with
        | Fun (_ty, body), arg :: other_args ->
          (* beta-reduce *)
          assert (Ty.equal _ty arg.term_ty);
          let body' = Term.eval_db (DB_env.singleton arg) body in
          let body' = compute_nf body' [] in
          Term.app body' other_args, E_beta (f', arg) :: e
        | _ -> t', e
      in
      set_nf_ t t' e';
      t'

  (* assert [c := new_t] and propagate *)
  let assert_choice c new_t : unit =
    let t_c = Term.const c in
    if t_c.term_nf <> None then invalid_arg "assert_choice";
    set_nf_ t_c new_t [E_choice (c, new_t)];
    propagate_ t_c new_t;
    ()

  let assert_neq t1 t2 : unit =
    let t1 = normal_form t1 in
    let t2 = normal_form t2 in
    if Term.equal t1 t2
    then raise (Inconsistent (t1, t2, t1, t2))
    else (
      push_set_distinct_ t1;
      push_set_distinct_ t2;
      t1.term_distinct <- t2 :: t1.term_distinct;
      t2.term_distinct <- t1 :: t2.term_distinct;
    )

  type explanation =
    | By_choice of term Typed_cst.t * term (* assertion [c --> t] *)

  let pp_explanation out = function
    | By_choice (c,t) ->
      Format.fprintf out "(@[choice %a@ -> %a@])" Typed_cst.pp c Term.pp t

  let explain t1 t2 =
    let t1 = normal_form t1 in
    let t2 = normal_form t2 in
    if not (Term.equal t1 t2)
    then invalid_arg "term.explain: not equal";
    (* recurse through the explanations *)
    let rec aux t acc = match t.term_nf_why with
      | [] -> acc
      | l -> aux_e_l l acc

    (* add given explanation to [acc] *)
    and aux_e e acc = match e with
      | E_congruence (a,b) -> aux_until a b acc
      | E_if (t,a,b) -> acc |> aux t |> aux a |> aux b
      | E_match (t,u,rhs) -> acc |> aux t |> aux u |> aux rhs
      | E_beta (f, arg) -> acc |> aux f |> aux arg
      | E_choice (c,t) -> By_choice (c,t) :: acc

    and aux_e_l l acc = List.fold_right aux_e l acc

    (* recurse until t1==t2 *)
    and aux_until t1 t2 acc =
      if Term.equal t1 t2
      then acc
      else begin match t1.term_nf, t1.term_nf_why with
        | None, _
        | _, [] -> assert false
        | Some t1', e ->
          let acc = aux_e_l e acc in
          aux_until t1' t2 acc
      end
    in
    aux t1 [] |> aux t2
end
