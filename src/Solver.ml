
(* This file is free software. See file "license" for more details. *)

(** {1 Solver} *)

module type CONFIG = sig
  val max_depth: int
end

(** {2 The Main Solver} *)

module Make(Config : CONFIG)(Dummy : sig end) = struct
  exception Error of string

  let errorf msg = CCFormat.ksprintf msg ~f:(fun s -> raise (Error s))

  type level = int

  (* main term cell *)
  type term = {
    mutable term_id: int; (* unique ID *)
    term_ty: ty_h;
    term_cell: term_cell;
    mutable term_nf: (term * explanation) option;
      (* normal form + explanation of why *)
    mutable term_watchers: term list; (* terms watching this term's nf *)
  }
  (* TODO: use a weak array for watchers *)

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
      | Atomic (id, _) -> ID.pp out id
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
        { cst_depth; cst_parent=parent; cst_cases=None; }
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
    type _level = level
    type level = _level

    let dummy_level = -1

    type stack_cell =
      | S_nil
      | S_level of level * stack_cell
      | S_set_nf of
          term * (term * explanation) option * stack_cell
          (* t1.nf <- t2 *)

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
          then st (* stop *)
          else aux l st' (* continue *)
        | S_nil -> st
        | S_set_nf (t, nf, st') ->
          t.term_nf <- nf;
          aux l st'
      in
      Log.debugf 2 (fun k->k "@{<Yellow>** now at level %d@}" l);
      st_.stack <- aux l st_.stack

    let cur_level () = st_.stack_level

    let push_level () : level =
      let l = st_.stack_level + 1 in
      st_.stack_level <- l;
      st_.stack <- S_level (l, st_.stack);
      Log.debugf 2 (fun k->k "@{<Yellow>** now at level %d@}" l);
      l

    (* TODO: use weak resizable array instead *)
    let push_set_nf_ (t:term) =
      st_.stack <- S_set_nf (t, t.term_nf, st_.stack)
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
          | B_not a1, B_not a2 -> a1 == a2
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

    (* hashconsing function + iterating on all terms *)
    let hashcons_, all_terms_ =
      let tbl_ : W.t = W.create 1024 in
      let term_count_ : int ref = ref 0 in
      let hashcons t =
        let t' = W.merge tbl_ t in
        if t == t' then (
          t.term_id <- !term_count_;
          incr term_count_

        ) else (
          assert (t'.term_id >= 0);
        );
        t'
      and iter yield =
        W.iter yield tbl_
      in
      hashcons, iter

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

    let add_watcher ~watcher t =
      t.term_watchers <- watcher :: t.term_watchers

    let add_watcher_l ~watcher l = List.iter (add_watcher ~watcher) l

    (* build a term. If it's new, add it to the watchlist
       of every member of [watching] *)
    let mk_term_ ~(watching:term list) cell ~ty : term =
      let t = {
        term_id= -1;
        term_ty=ty;
        term_cell=cell;
        term_nf=None;
        term_watchers=[];
      } in
      let t' = hashcons_ t in
      if t==t' then (
        List.iter (fun u -> add_watcher ~watcher:t u) watching;
      );
      t'

    let db d =
      mk_term_ ~watching:[] (DB d) ~ty:(DB.ty d)

    let const c =
      mk_term_ ~watching:[] (Const c) ~ty:(Typed_cst.ty c)

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
        (* watch head, not arguments *)
        let t = match f.term_cell with
          | App (f1, l1) ->
            let l' = l1 @ l in
            mk_term_ ~watching:[f1] (App (f1, l')) ~ty
          | _ -> mk_term_ ~watching:[f] (App (f,l)) ~ty
        in
        t

    let app_cst f l = app (const f) l

    let fun_ ty body =
      let ty' = Ty.arrow ty body.term_ty in
      (* do not add watcher: propagation under λ forbidden *)
      mk_term_ ~watching:[] (Fun (ty, body)) ~ty:ty'

    (* TODO: check types *)

    let match_ u m =
      let ty =
        let _, (_,rhs) = ID.Map.choose m in
        rhs.term_ty
      in
      (* propagate only from [u] *)
      let t = mk_term_ ~watching:[u] (Match (u,m)) ~ty in
      t

    let if_ a b c =
      assert (Ty.equal b.term_ty c.term_ty);
      (* propagate under test only *)
      let t = mk_term_ ~watching:[a] (If (a,b,c)) ~ty:b.term_ty in
      t

    let builtin_ ~watching b =
      let t = mk_term_ ~watching (Builtin b) ~ty:Ty.prop in
      t

    let builtin b =
      let watching = match b with
        | B_not u -> [u]
        | B_and (a,b) | B_or (a,b)
        | B_eq (a,b) | B_imply (a,b) -> [a;b]
      in
      builtin_ ~watching b

    let not_ t = match t.term_cell with
      | True -> false_
      | False -> true_
      | Builtin (B_not t') -> t'
      | _ -> builtin_ ~watching:[t] (B_not t)

    let and_ a b = builtin_ ~watching:[a;b] (B_and (a,b))
    let or_ a b = builtin_ ~watching:[a;b] (B_or (a,b))
    let imply a b = builtin_ ~watching:[a;b] (B_imply (a,b))
    let eq a b = builtin_ ~watching:[a;b] (B_eq (a,b))
    let neq a b = not_ (eq a b)

    let and_l = function
      | [] -> false_
      | [t] -> t
      | a :: l -> List.fold_left and_ a l

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

    let is_const t = match t.term_cell with
      | Const _ -> true
      | _ -> false

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

    (* return [Some] iff the term is an undefined constant *)
    let as_cst_undef (t:term): (cst * Ty.t * cst_info) option =
      match t.term_cell with
        | Const ({cst_kind=Cst_undef (ty,info); _} as c) ->
          Some (c,ty,info)
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
        let pp_bind out (id,(_tys,rhs)) =
          fpf out "(@[%a %a@])" ID.pp id pp rhs
        in
        let print_map = CCFormat.seq ~start:"" ~stop:"" ~sep:" " pp_bind in
        fpf out "(@[match %a@ (@[<hv>%a@])@])"
          pp t print_map (ID.Map.to_seq m)
      | Builtin (B_not t) -> fpf out "(@[not@ %a@])" pp t
      | Builtin (B_and (a,b)) -> fpf out "(@[and@ %a@ %a@])" pp a pp b
      | Builtin (B_or (a,b)) -> fpf out "(@[or@ %a@ %a@])" pp a pp b
      | Builtin (B_imply (a,b)) -> fpf out "(@[imply@ %a@ %a@])" pp a pp b
      | Builtin (B_eq (a,b)) -> fpf out "(@[=@ %a@ %a@])" pp a pp b

    type graph_edge =
      | GE_sub of int (* n-th subterm *)
      | GE_nf (* pointer to normal_form *)
      | GE_watch (* watched term *)

    let as_graph : (term, term * graph_edge * term) CCGraph.t =
      CCGraph.make_labelled_tuple
        (fun t ->
           let sub =
             begin match t.term_cell with
               | True | False | Const _ | DB _ -> Sequence.empty
               | App (f,l) when is_const f -> Sequence.of_list l
               | App (f,l) -> Sequence.cons f (Sequence.of_list l)
               | Fun (_, body) -> Sequence.return body
               | If (a,b,c) -> Sequence.of_list [a;b;c]
               | Builtin b -> builtin_to_seq b
               | Match (u,m) ->
                 Sequence.cons u (ID.Map.values m |> Sequence.map snd)
             end
             |> Sequence.mapi (fun i t' -> GE_sub i, t')
           and watched =
             t.term_watchers
             |> Sequence.of_list
             |> Sequence.map (fun t' -> GE_watch, t')
           and nf = match t.term_nf with
             | None -> Sequence.empty
             | Some (t',_) -> Sequence.return (GE_nf, t')
           in
           Sequence.of_list [sub; watched; nf] |> Sequence.flatten)

    (* print this set of terms (and their subterms) in DOT *)
    let pp_dot out terms =
      let pp_node out t = match t.term_cell with
        | True -> CCFormat.string out "true"
        | False -> CCFormat.string out "false"
        | DB d -> DB.pp out d
        | Const c -> Typed_cst.pp out c
        | App (f,_) ->
          begin match f.term_cell with
            | Const c -> Typed_cst.pp out c (* no boxing *)
            | _ -> CCFormat.string out "@"
          end
        | If _ -> CCFormat.string out "if"
        | Match _ -> CCFormat.string out "match"
        | Fun (ty,_) -> Format.fprintf out "fun %a" Ty.pp ty
        | Builtin b ->
          CCFormat.string out
            begin match b with
              | B_not _ -> "not" | B_and _ -> "and"
              | B_or _ -> "or" | B_imply _ -> "=>" | B_eq _ -> "="
            end
      in
      let attrs_v t =
        [`Label (CCFormat.to_string pp_node t); `Shape "box"]
      and attrs_e (_,e,_) = match e with
        | GE_sub i -> [`Label (string_of_int i); `Weight 15]
        | GE_nf ->
          [`Label "nf"; `Style "dashed"; `Weight 0; `Color "green"]
        | GE_watch ->
          [`Style  "dotted"; `Weight 0; `Color "grey"]
      in
      let pp_ out terms =
        CCGraph.Dot.pp_seq
          ~tbl:(CCGraph.mk_table ~eq:equal ~hash:hash 256)
          ~eq:equal
          ~attrs_v
          ~attrs_e
          ~graph:as_graph
          out
          terms
      in
      Format.fprintf out "@[%a@]@." pp_ terms

    let pp_dot_all out () = pp_dot out all_terms_
  end

  module Explanation = struct
    type t = explanation
    let empty = E_empty
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

    let pp_explanation_atom out = function
      | E_choice (c,t) ->
        Format.fprintf out
          "(@[choice %a@ -> %a@])" Typed_cst.pp c Term.pp t
      | E_lit (t,b) ->
        Format.fprintf out "(@[lit %a@ -> %B@])" Term.pp t b

    let pp out e =
      Format.fprintf out "@[%a@]"
        (CCFormat.seq ~start:"" ~stop:"" ~sep:", " pp_explanation_atom)
        (to_seq e)
  end

  (** {2 Literals} *)
  module Lit = struct
    type t = term
    let neg = Term.not_

    type view =
      | V_true
      | V_false
      | V_assert of term * bool
      | V_cst_choice of cst * term

    let view (t:t): view = match t.term_cell with
      | False -> V_false
      | True -> V_true
      | Builtin (B_eq (a, b)) ->
        begin match Term.as_cst_undef a, Term.as_cst_undef b with
          | Some (c,_,_), _ -> V_cst_choice (c,b)
          | None, Some (c,_,_) -> V_cst_choice (c,a)
          | None, None -> V_assert (t, true)
        end
      | Builtin (B_not t') -> V_assert (t', false)
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

    let atom ?(sign=true) t = if sign then t else neg t
    let eq a b = Term.eq a b
    let neq a b = Term.neq a b
    let cst_choice c t = Term.eq (Term.const c) t

    let equal = Term.equal
    let hash = Term.hash
    let compare = Term.compare
    let pp = Term.pp
    let print = pp

    (** {2 Normalization} *)

    let norm l =
      Log.debugf 5 (fun k->k "Lit.norm `@[%a@]`" pp l);
      l, false (* TODO? *)
  end

  module Clause = struct
    type t = Lit.t list

    let pp out c = match c with
      | [] -> CCFormat.string out "false"
      | [lit] -> Lit.pp out lit
      | _ ->
        Format.fprintf out "(@[or@ %a@])"
          (CCFormat.list ~start:"" ~stop:"" ~sep:" " Lit.pp) c

    (* list of clauses that have been newly generated, waiting
       to be propagated to Msat.
       invariant: those clauses must be tautologies *)
    let new_ : t list ref = ref []

    let pop_new () : t list =
      let l = !new_ in
      new_ := [];
      l

    let push_new (c:t): unit =
      Log.debugf 5 (fun k->k "new tautology: `@[%a@]`" pp c);
      new_ := c :: !new_;
      ()

    let push_new_l = List.iter push_new
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
    val next : unit -> state
    val lit_of_depth : int -> Lit.t option
    val pp: t CCFormat.printer
  end = struct
    type t = int

    let pp = CCFormat.int

    (* truncate at powers of 5 *)
    let max_depth =
      if Config.max_depth < 5
      then invalid_arg "max-depth should be >= 5";
      let rem = Config.max_depth mod 5 in
      let res = Config.max_depth - rem in
      Log.debugf 1 (fun k->k "max depth = %d" res);
      res

    type state =
      | At of t * Lit.t
      | Exhausted

    (* create a literal standing for [max_depth = d] *)
    let mk_lit_ d : Lit.t =
      ID.makef "max_depth_leq_%d" d
      |> Typed_cst.make_bool
      |> Term.const
      |> Lit.atom ~sign:true

    let lits_ : (int, Lit.t) Hashtbl.t = Hashtbl.create 32

    (* get the literal correspond to depth [d], if any *)
    let lit_of_depth d : Lit.t option =
      if d < 5 || (d mod 5 <> 0) || d > max_depth
      then None
      else match CCHashtbl.get lits_ d with
        | Some l -> Some l
        | None ->
          let lit = mk_lit_ d in
          Hashtbl.add lits_ d lit;
          Some lit

    (* initial state *)
    let start_ = At (5, mk_lit_ 5)

    let cur_ = ref start_
    let reset () = cur_ := start_
    let current () = !cur_

    (* next state *)
    let next () = match !cur_ with
      | Exhausted -> assert false
      | At (l_old, _) ->
        (* update level and current lit *)
        let l = l_old + 5 in
        let st =
          if l > max_depth
          then Exhausted
          else (
            let lit =
              match lit_of_depth l with
                | Some lit -> lit
                | None -> errorf "increased depth to %d, but not lit" l
            in
            At (l, lit)
          )
        in
        cur_ := st;
        st
  end

  (** {2 Case Expansion} *)

  (* build clause(s) that explains that [c] must be one of its
     cases *)
  let clauses_of_cases (c:cst) : Clause.t list = match c.cst_kind with
    | Cst_undef (_, {cst_cases=Some l; cst_depth=lazy d; _}) ->
      (* guard for non-constant cases (depth limit) *)
      let lit_guard = Iterative_deepening.lit_of_depth d in
      let guard_is_some = CCOpt.is_some lit_guard in
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
                    | Const {cst_kind=Cst_undef (_,info); _} ->
                      (* is [sub] a constant deeper than [d]? *)
                      Lazy.force info.cst_depth > d
                    | _ -> false)
             in
             lit, needs_guard)
          l
      in
      (* at least one case *)
      let c_choose =
        List.map
          (fun (lit,needs_guard) ->
             match lit_guard, needs_guard with
               | None, true -> assert false
               | Some guard, true ->
                 Term.and_ lit guard (* this branch might be too deep *)
               | _ -> lit)
          lits

      (* at most one case *)
      and cs_once =
        CCList.diagonal lits
        |> List.map
          (fun ((l1,_),(l2,_)) -> [Term.not_ l1; Term.not_ l2])
      in
      c_choose :: cs_once
    | _ -> assert false

  (* make a fresh constant, with a unique name *)
  let new_cst_ =
    let n = ref 0 in
    fun ?parent name ty ->
      let id = ID.makef "?%s_%d" name !n in
      incr n;
      Typed_cst.make_undef ?parent id ty

  (* build the disjunction of cases for [info] *)
  let expand_cases (cst:cst) (ty:Ty.t) (info:cst_info): term list =
    assert (info.cst_cases = None);
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
    Log.debugf 4
      (fun k->k "@[<2>expand cases `@[%a@]` into:@ @[%a@]@]"
          Typed_cst.pp cst (CCFormat.list Term.pp) l);
    info.cst_cases <- Some l;
    l

  (* retrieve the normal form of [t], and the explanation
     of why [t -> normal_form(t) *)
  let normal_form (t:term) : explanation * term =
    let rec aux set t = match t.term_nf with
      | None -> set, t
      | Some (t',set') -> aux (Explanation.append set set') t'
    in
    match t.term_nf with
      | None -> Explanation.empty, t
      | Some (t',set) -> aux set t'

  let normal_form_append (e:explanation) (t:term) : explanation * term =
    let e', t' = normal_form t in
    Explanation.append e e', t'

  exception Inconsistent of explanation * term
  (* semantically equivalent to [explanation => term], where
     the term evaluates to [false] *)

  (* environment for evaluation: not-yet-evaluated terms *)
  type eval_env = (explanation * term) lazy_t DB_env.t

  (* just evaluate the De Bruijn indices, and return
     the explanations used to evaluate subterms *)
  let eval_db (env:eval_env) (t:term) : explanation * term =
    if DB_env.size env = 0
    then Explanation.empty, t (* trivial *)
    else (
      let e = ref Explanation.empty in
      let rec aux env t : term = match t.term_cell with
        | DB d ->
          begin match DB_env.get d env with
            | None -> t
            | Some (lazy (e', t')) ->
              e := Explanation.append !e e'; (* save explanation *)
              t'
          end
        | Const _
        | True
        | False -> t
        | Fun (ty, body) ->
          let body' = aux (DB_env.push_none env) body in
          Term.fun_ ty body'
        | Match (u, m) ->
          let u = aux env u in
          let m =
            ID.Map.map
              (fun (tys,rhs) ->
                 tys, aux (DB_env.push_none_l tys env) rhs)
              m
          in
          Term.match_ u m
        | If (a,b,c) ->
          Term.if_ (aux env a) (aux env b) (aux env c)
        | App (f, l) -> Term.app (aux env f) (aux_l env l)
        | Builtin b -> Term.builtin (Term.map_builtin (aux env) b)
      and aux_l env l =
        List.map (aux env) l
      in
      let t = aux env t in
      !e, t
    )

  (* find the set of constants potentially blocking
     the evaluation of [t] *)
  let find_blocking_undef (t:term): (cst * Ty.t * cst_info) Sequence.t =
    let rec aux t yield = match t.term_cell with
      | Const c ->
        begin match c.cst_kind with
          | Cst_undef (ty, info) -> yield (c, ty, info)
          | Cst_bool
          | Cst_cstor _
          | Cst_defined _ -> ()
        end
      | App (f, _) -> aux f yield
      | Builtin b ->
        Term.builtin_to_seq b
        |> Sequence.flat_map aux
        |> Sequence.iter yield
      | Fun _ (* in normal form *)
      | True
      | False
      | DB _ -> ()
      | Match (u,_) -> aux u yield
      | If (a,_,_) -> aux a yield
    in
    aux t

  (* find blocking undefined constants, and expand their list of cases *)
  let expand_blocking_undef (t:term) : unit =
    find_blocking_undef t
    |> Sequence.iter
      (fun (c,ty,info) -> match info.cst_cases with
         | Some _ -> ()
         | None ->
           let _ = expand_cases c ty info in
           assert (info.cst_cases <> None);
           (* also push new tautologies to force a choice in [l] *)
           let new_c = clauses_of_cases c in
           Clause.push_new_l new_c)

  (* set the normal form of [t], propagate to watchers *)
  let rec set_nf_ t new_t (e:explanation) : unit =
    if Term.equal t new_t then ()
    else begin match t.term_nf with
      | Some (new_t', _) -> assert (Term.equal new_t new_t')
      | None ->
        Backtrack.push_set_nf_ t;
        t.term_nf <- Some (new_t, e);
        Log.debugf 5
          (fun k->k "@[<hv2>set_nf@ `@[%a@]` :=@ `@[%a@]`@ with exp %a@]"
              Term.pp t Term.pp new_t Explanation.pp e);
        (* we just changed [t]'s normal form, ensure that [t]'s
           watching terms are up-to-date *)
        List.iter
          (fun watcher -> match watcher.term_nf with
             | Some _ -> ()   (* already reduced *)
             | None -> ignore (compute_nf watcher))
          t.term_watchers;
        ()
    end

  (* compute the normal form of this term. We know at least one of its
     subterm(s) has been reduced *)
  and compute_nf (t:term) : explanation * term =
    Log.debugf 5 (fun k->k "compute_nf `@[%a@]`" Term.pp t);
    (* follow the "normal form" pointer *)
    match t.term_nf with
      | Some (t', e) ->
        let e', nf = compute_nf t' in
        (* NOTE path compression here, maybe *)
        Explanation.append e e', nf
      | None -> compute_nf_noncached t

  and compute_nf_noncached t =
    assert (t.term_nf = None);
    match t.term_cell with
      | DB _ -> assert false (* non closed! *)
      | True | False | Const _ ->
        Explanation.empty, t (* always trivial *)
      | Fun _ -> Explanation.empty, t (* no eval under lambda *)
      | Builtin b ->
        let e, b' =
          Term.fold_map_builtin compute_nf_add Explanation.empty b
        in
        (* try boolean reductions *)
        let t' = compute_builtin b' in
        set_nf_ t t' e;
        e, t'
      | If (a,b,c) ->
        let e_a, a' = normal_form a in
        assert (not (Term.equal a a'));
        let default() = Term.if_ a' b c in
        let e_branch, t' = match a'.term_cell with
          | True -> compute_nf b
          | False -> compute_nf c
          | _ -> Explanation.empty, default()
        in
        (* merge evidence from [a]'s normal form and [b/c]'s normal form *)
        let e = Explanation.append e_a e_branch in
        set_nf_ t t' e;
        e, t'
      | Match (u, m) ->
        let e_u, u' = normal_form u in
        let default() = Term.match_ u' m in
        let e_branch, t' = match u'.term_cell with
          | App ({term_cell=Const c; _}, l) ->
            begin
              try
                let tys, rhs = ID.Map.find (Typed_cst.id c) m in
                if List.length tys = List.length l
                then (
                  (* evaluate arguments *)
                  let l =
                    List.map
                      (fun t -> lazy (compute_nf t))
                      l
                  in
                  let env = DB_env.push_l l DB_env.empty in
                  (* replace in [rhs] *)
                  let e', rhs = eval_db env rhs in
                  (* evaluate new [rhs] *)
                  compute_nf_add e' rhs
                )
                else Explanation.empty, Term.match_ u' m
              with Not_found ->
                Explanation.empty, Term.match_ u' m
            end
          | _ -> Explanation.empty, default()
        in
        let e = Explanation.append e_u e_branch in
        set_nf_ t t' e;
        e, t'
      | App (f, l) ->
        let e_f, f' = normal_form f in
        (* now beta-reduce if needed *)
        let e_reduce, new_t =
          compute_nf_app DB_env.empty Explanation.empty f' l
        in
        (* merge explanations *)
        let e = Explanation.append e_reduce e_f in
        set_nf_ t new_t e;
        e, new_t

  (* apply [f] to [l], until no beta-redex is found *)
  and compute_nf_app env e f l = match f.term_cell, l with
    | Const {cst_kind=Cst_defined (_, lazy def_f); _}, l ->
      assert (l <> []);
      (* reduce [f l] into [def_f l] when [f := def_f] *)
      compute_nf_app env e def_f l
    | Fun (_ty, body), arg :: other_args ->
      (* beta-reduce *)
      assert (Ty.equal _ty arg.term_ty);
      let new_env = DB_env.push (lazy (compute_nf arg)) env in
      (* apply [body] to [other_args] *)
      compute_nf_app new_env e body other_args
    | _ ->
      (* cannot reduce; substitute in [f] and re-apply *)
      let e', f = eval_db env f in
      let t' = Term.app f l in
      Explanation.append e e', t'

  (* compute nf of [t], append [e] to the explanation *)
  and compute_nf_add (e : explanation) (t:term) : explanation * term =
    let e', t' = compute_nf t in
    Explanation.append e e', t'

  (* compute the builtin, assuming its components are
     already reduced *)
  and compute_builtin bu: term = match bu with
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
        | _ ->
          begin match Term.as_cstor_app a, Term.as_cstor_app b with
            | Some (c1,_,l1), Some (c2,_,l2) ->
              if not (Typed_cst.equal c1 c2)
              then Term.false_
                  (* [c1 ... = c2 ...] --> false, as distinct constructors
                     can never be equal *)
              else if Typed_cst.equal c1 c2
                   && List.length l1 = List.length l2
              then (
                (* injectivity: arguments are equal *)
                List.map2 Term.eq l1 l2
                |> Term.and_l
              )
              else Term.eq a b
            | _ -> Term.eq a b
          end
      end

  (** {2 Sat Solver} *)

  (* formulas for msat *)
  module M_expr
    : Msat.Formula_intf.S
      with type t = Term.t
       and type proof = unit
  = struct
    include Lit
    type proof = unit (* TODO later *)
    let label _ = assert false
    let add_label _ _ = assert false
    let print = Lit.pp
  end

  (* the "theory" part: propagations *)
  module M_th :
    Msat.Theory_intf.S
    with type formula = M_expr.t
     and type proof = M_expr.proof
  = struct
    type formula = M_expr.t
    type proof = M_expr.proof

    type slice = {
      start : int;
      length : int;
      get : int -> formula;
      push : formula list -> proof -> unit;
    }

    type level = Backtrack.level

    type res =
      | Sat of level
      | Unsat of formula list * proof

    let dummy = Backtrack.dummy_level

    let current_level = Backtrack.cur_level

    let backtrack = Backtrack.backtrack

    let lit_of_exp_ (e:explanation_atom): Lit.t = match e with
      | E_lit (t, b) -> Lit.atom ~sign:b t
      | E_choice (cst, t) -> Lit.cst_choice cst t

    let clause_of_exp_ (e:explanation): Clause.t =
      Explanation.to_seq e
      |> Sequence.map lit_of_exp_
      |> Sequence.to_rev_list

    (* TODO: a good way of finding whether, during evaluation,
       some prop-typed terms reduced to true/false, so we can
       turn them into literals and propagate them via [slice] *)

    (* assert [c := new_t] and propagate *)
    let assert_choice _slice (c:cst) (new_t:term) : unit =
      let t_c = Term.const c in
      assert (t_c.term_nf = None);
      (* set normal form, then compute *)
      set_nf_ t_c new_t (Explanation.return (E_choice (c, new_t)));
      ()

    let assert_lit slice (l:Lit.t) : unit = match Lit.view l with
      | Lit.V_false -> assert false
      | Lit.V_true -> ()
      | Lit.V_assert (_, _) -> () (* TODO? *)
      | Lit.V_cst_choice (c, t) ->
        assert_choice slice c t

    (* propagation from the bool solver *)
    let assume slice =
      let start = slice.start in
      assert (slice.length > 0);
      (* increase level *)
      let _ = Backtrack.push_level () in
      let lev = Backtrack.cur_level () in
      try
        for i = start to start + slice.length - 1 do
          let lit = slice.get i in
          Log.debugf 3 (fun k->k "assert_lit `@[%a@]`" Lit.pp lit);
          assert_lit slice lit;
          (* also assert the new tautologies *)
          let new_clauses = Clause.pop_new () in
          List.iter
            (fun c -> slice.push c ())
            new_clauses
        done;
        Sat lev
      with Inconsistent (e, concl) ->
        (* conflict clause: [e => concl] *)
        let guard = clause_of_exp_ e |> List.map Lit.neg in
        let conflict_clause = Lit.atom ~sign:true concl :: guard in
        Unsat (conflict_clause, ())
end

  module M = Msat.Solver.Make(M_expr)(M_th)(struct end)

  (* push one clause into [M] *)
  let push_clause (c:Clause.t): unit =
    Log.debugf 3 (fun k->k "@[<2>push clause `@[%a@]`@]" Clause.pp c);
    (* ensure that all constants that might block the evaluation
       of [c] are expanded *)
    List.iter expand_blocking_undef c;
    M.assume [c]

  (** {2 Conversion} *)

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

    let add_cst_support_ (c:cst): unit =
      CCList.Ref.push model_support_ c

    (* normalize [c], at toplevel only (no assumption) *)
    let push_normalized_clause c =
      let c =
        List.map
          (fun t ->
             let e, t' = compute_nf t in
             assert (Explanation.is_empty e);
             t')
          c
      in
      push_clause c

    let add_statement st =
      Log.debugf 2 (fun k->k "add statement `@[%a@]`" Ast.pp_statement st);
      match st with
        | Ast.Assert t ->
          let t = conv_term [] t in
          push_normalized_clause [t]
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
          push_normalized_clause [t]
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
               ID.Tbl.find decl_ty_ id |> Lazy.force |> ignore)
            l

    let add_statement_l = List.iter add_statement
  end

  (** {2 Main} *)

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
    !Conv.model_support_
    |> Sequence.of_list
    |> Sequence.map
      (fun c ->
         (* find normal form of [c] *)
         let t = Term.const c in
         let _, t = normal_form t in
         c, t)
    |> Typed_cst.Map.of_seq

  (* convert unsat-core *)
  let conv_unsat_core (core:M.St.clause list): Clause.t Sequence.t =
    Sequence.of_list core
    |> Sequence.map
      (fun c ->
         M.Proof.to_list c |> List.map (fun a -> a.M.St.lit))

  (* NOTE: would be nice to just iterate over
     all literals instead *)
  let pp_term_graph = Term.pp_dot_all

  (* safe push/pop in msat *)
  let with_push_ ~on_exit f =
    let lev = M.push () in
    Iterative_deepening.reset ();
    CCFun.finally
      ~f
      ~h:(fun () ->
        List.iter (fun f->f()) on_exit;
        M.pop lev)

  let check ?(on_exit=[]) l =
    let module ID = Iterative_deepening in
    (* iterated deepening *)
    let rec iter state = match state with
      | ID.Exhausted -> Unknown U_max_depth
      | ID.At (cur_depth, cur_lit) ->
        let lev = M.push () in
        (* restrict depth *)
        push_clause [cur_lit];
        match M.solve () with
          | M.Sat ->
            let m = compute_model_ () in
            Log.debugf 1
              (fun k->k "@{<Yellow>** found SAT@} at depth %a"
                  ID.pp cur_depth);
            M.pop lev; (* remove clause *)
            Sat m
          | M.Unsat ->
            (* check if [max depth] literal involved in unsat-core;
               - if not, truly UNSAT
               - if yes, try next level
            *)
            let core = M.get_proof () |> M.unsat_core in
            let cur_lit_neg = Lit.neg cur_lit in
            let depth_limited =
              conv_unsat_core core
              |> Sequence.flat_map Sequence.of_list
              |> Sequence.exists
                (fun lit ->
                   Lit.equal lit cur_lit || Lit.equal lit cur_lit_neg)
            in
            Log.debugf 1
              (fun k->k
                  "@{<Yellow>** found Unsat@} at depth %a;@ \
                   depends on %a: %B"
                  ID.pp cur_depth Lit.pp cur_lit depth_limited);
            (* remove depth limiting clause in any case*)
            M.pop lev;
            if depth_limited
            then ID.next () |> iter (* deeper! *)
            else Unsat
    in
    (* in a stack frame, do the solving *)
    with_push_ ~on_exit
      (fun () ->
         Conv.add_statement_l l;
         ID.current () |> iter
      )
end

