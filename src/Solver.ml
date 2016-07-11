
(* This file is free software. See file "license" for more details. *)

let (<?>) = CCOrd.(<?>)

let get_time : unit -> float =
  let start = Unix.gettimeofday() in
  fun () ->
    Unix.gettimeofday() -. start

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
  let stat_num_clause_push = ref 0
  let stat_num_clause_tautology = ref 0

  (* main term cell *)
  type term = {
    mutable term_id: int; (* unique ID *)
    term_ty: ty_h;
    term_cell: term_cell;
    mutable term_nf: (term * explanation) option;
      (* normal form + explanation of why *)
    mutable term_deps: cst list;
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
    cst_watched: term Hash_set.t;
    (* set of (bool) literals terms that depend on this constant for evaluation.

       A literal [lit] can watch several typed constants. If
       [lit.nf = t], and [t]'s evaluation is blocked by [c1,...,ck],
       then [lit] will watch [c1,...,ck].

       Watch list only grow, they never shrink. *)
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

    let is_empty e = e.size = 0
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

  let term_equal_ a b = a==b
  let term_hash_ a = a.term_id

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
          cst_cases=None;
          cst_watched=
            Hash_set.create ~eq:term_equal_ ~hash:term_hash_ 16;
        }
      in
      make id (Cst_undef (ty, info))

    let as_undefined (c:t): (t * Ty.t * cst_info) option =
      match c.cst_kind with
        | Cst_undef (ty,i) -> Some (c,ty,i)
        | Cst_bool | Cst_defined _ | Cst_cstor _ -> None

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
        | S_nil -> st
        | S_level (l', st') ->
          if l=l'
          then st (* stop *)
          else aux l st' (* continue *)
        | S_set_nf (t, nf, st') ->
          t.term_nf <- nf;
          aux l st'
      in
      Log.debugf 2
        (fun k->k "@{<Yellow>** now at level %d (backtrack)@}" l);
      let st' = aux l st_.stack in
      st_.stack <- st';
      st_.stack_level <- l;
      ()

    let cur_level () = st_.stack_level

    let push_level () : unit =
      let l = st_.stack_level + 1 in
      st_.stack_level <- l;
      st_.stack <- S_level (l, st_.stack);
      Log.debugf 2 (fun k->k "@{<Yellow>** now at level %d (push)@}" l);
      ()

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
      | Builtin (B_not a) -> Hash.combine2 20 a.term_id
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
             try v1 == ID.Map.find k1 m2
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
        term_deps=[];
      } in
      hashcons_ t

    let true_ = mk_bool_ true
    let false_ = mk_bool_ false

    type deps =
      | Dep_cst of cst (* the term itself is a constant *)
      | Dep_none
      | Dep_sub of term
      | Dep_subs of term list

    (* build a term. If it's new, add it to the watchlist
       of every member of [watching] *)
    let mk_term_ ~(deps:deps) cell ~ty : term =
      let t = {
        term_id= -1;
        term_ty=ty;
        term_cell=cell;
        term_nf=None;
        term_deps=[];
      } in
      let t' = hashcons_ t in
      if t==t' then (
        (* compute evaluation dependencies *)
        let deps = match deps with
          | Dep_none -> []
          | Dep_cst c -> [c]
          | Dep_sub t -> t.term_deps
          | Dep_subs l ->
            l
            |> CCList.flat_map (fun sub -> sub.term_deps)
            |> CCList.sort_uniq ~cmp:Typed_cst.compare
        in
        t'.term_deps <- deps
      );
      t'

    let db d =
      mk_term_ ~deps:Dep_none (DB d) ~ty:(DB.ty d)

    let const c =
      let deps = match c.cst_kind with
        | Cst_undef _ -> Dep_cst c (* depends on evaluation! *)
        | Cst_bool | Cst_defined _ | Cst_cstor _ -> Dep_none
      in
      mk_term_ ~deps (Const c) ~ty:(Typed_cst.ty c)

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
            mk_term_ ~deps:(Dep_sub f1) (App (f1, l')) ~ty
          | _ -> mk_term_ ~deps:(Dep_sub f) (App (f,l)) ~ty
        in
        t

    let app_cst f l = app (const f) l

    let fun_ ty body =
      let ty' = Ty.arrow ty body.term_ty in
      (* do not add watcher: propagation under λ forbidden *)
      mk_term_ ~deps:Dep_none (Fun (ty, body)) ~ty:ty'

    (* TODO: check types *)

    let match_ u m =
      let ty =
        let _, (_,rhs) = ID.Map.choose m in
        rhs.term_ty
      in
      (* propagate only from [u] *)
      let t = mk_term_ ~deps:(Dep_sub u) (Match (u,m)) ~ty in
      t

    let if_ a b c =
      assert (Ty.equal b.term_ty c.term_ty);
      (* propagate under test only *)
      let t = mk_term_ ~deps:(Dep_sub a) (If (a,b,c)) ~ty:b.term_ty in
      t

    let builtin_ ~deps b =
      (* normalize a bit *)
      let b = match b with
        | B_eq (a,b) when a.term_id > b.term_id -> B_eq (b,a)
        | B_and (a,b) when a.term_id > b.term_id -> B_and (b,a)
        | B_or (a,b) when a.term_id > b.term_id -> B_or (b,a)
        | _ -> b
      in
      let t = mk_term_ ~deps (Builtin b) ~ty:Ty.prop in
      t

    let builtin b =
      let deps = match b with
        | B_not u -> Dep_sub u
        | B_and (a,b) | B_or (a,b)
        | B_eq (a,b) | B_imply (a,b) -> Dep_subs [a;b]
      in
      builtin_ ~deps b

    let not_ t = match t.term_cell with
      | True -> false_
      | False -> true_
      | Builtin (B_not t') -> t'
      | _ -> builtin_ ~deps:(Dep_sub t) (B_not t)

    let and_ a b = builtin_ ~deps:(Dep_subs [a;b]) (B_and (a,b))
    let or_ a b = builtin_ ~deps:(Dep_subs [a;b]) (B_or (a,b))
    let imply a b = builtin_ ~deps:(Dep_subs [a;b]) (B_imply (a,b))
    let eq a b = builtin_ ~deps:(Dep_subs [a;b]) (B_eq (a,b))
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

    let rec pp out t =
      pp_rec out t;
      if Config.pp_hashcons then Format.fprintf out "/%d" t.term_id;
      ()

    and pp_rec out t = match t.term_cell with
      | True -> CCFormat.string out "true"
      | False -> CCFormat.string out "false"
      | DB d -> DB.pp out d
      | Const c -> Typed_cst.pp out c
      | App (f,l) ->
        fpf out "(@[<1>%a@ %a@])" pp f (Utils.pp_list pp) l
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
      | Builtin (B_not t) -> fpf out "(@[<hv1>not@ %a@])" pp t
      | Builtin (B_and (a,b)) -> fpf out "(@[<hv1>and@ %a@ %a@])" pp a pp b
      | Builtin (B_or (a,b)) -> fpf out "(@[<hv1>or@ %a@ %a@])" pp a pp b
      | Builtin (B_imply (a,b)) ->
        fpf out "(@[<hv1>=>@ %a@ %a@])" pp a pp b
      | Builtin (B_eq (a,b)) ->
        fpf out "(@[<hv1>=@ %a@ %a@])" pp a pp b

    type graph_edge =
      | GE_sub of int (* n-th subterm *)
      | GE_nf (* pointer to normal_form *)
      | GE_dep  (* dependencies on constants *)

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
             t.term_deps
             |> Sequence.of_list
             |> Sequence.map (fun c -> GE_dep, const c)
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
        | GE_dep ->
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
          "(@[choice@ %a@ %a@])" Typed_cst.pp c Term.pp t
      | E_lit (t,b) ->
        Format.fprintf out "(@[assert_lit@ %a@ %B@])" Term.pp t b

    let pp out e =
      Format.fprintf out "(@[%a@])"
        (CCFormat.seq ~start:"" ~stop:"" ~sep:" " pp_explanation_atom)
        (to_seq e)
  end

  (** {2 Literals} *)
  module Lit = struct
    type t = term

    let neg = Term.not_

    (* unsigned lit *)
    let abs t = match t.term_cell with
      | False -> Term.true_
      | Builtin (B_not t) -> t
      | _ -> t

    type view =
      | V_true
      | V_false
      | V_assert of term * bool
      | V_cst_choice of cst * term

    let view (t:t): view = match t.term_cell with
      | False -> V_false
      | True -> V_true
      | Builtin (B_eq (a, b)) ->
        (* is [t] one of the cases for this constant? *)
        let is_case info t = match info.cst_cases with
          | Some l -> List.memq t l
          | None -> false
        in
        begin match Term.as_cst_undef a, Term.as_cst_undef b with
          | Some (c,_,info), _ when is_case info b -> V_cst_choice (c,b)
          | _, Some (c,_,info) when is_case info a -> V_cst_choice (c,a)
          | _ -> V_assert (t, true)
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

    module Map = Term.Map
    module Tbl = Term.Tbl

    (** {6 Normalization} *)

    let norm l = match l.term_cell with
      | False -> Term.true_, true
      | Builtin (B_not t') -> t', true
      | _ -> l, false
  end

  (** {2 Clauses} *)

  module Clause : sig
    type t = private Lit.t list
    val make : Lit.t list -> t
    val conflicts : t Queue.t
    val lemma_queue : t Queue.t
    val push_new : t -> unit
    val push_new_l : t list -> unit
    val push_conflict : t -> unit
    val iter : (Lit.t -> unit) -> t -> unit
    val to_seq : t -> Lit.t Sequence.t
    val pp : t CCFormat.printer
  end = struct
    type t = Lit.t list

    let pp out c = match c with
      | [] -> CCFormat.string out "false"
      | [lit] -> Lit.pp out lit
      | _ ->
        Format.fprintf out "(@[<hv1>or@ %a@])" (Utils.pp_list Lit.pp) c

    (* canonical form: sorted list *)
    let make l = CCList.sort_uniq ~cmp:Lit.compare l

    let equal_ c1 c2 = CCList.equal Lit.equal c1 c2
    let hash_ c = Hash.list Lit.hash c

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
      begin match c with
        | [a;b] when Lit.equal (Lit.neg a) b -> () (* trivial *)
        | _ when Tbl.mem all_lemmas_ c -> () (* already asserted *)
        | _ ->
          Log.debugf 4
            (fun k->k "(@[<1>@{<green>new_tautology@}@ @[%a@]@])" pp c);
          incr stat_num_clause_tautology;
          Tbl.add all_lemmas_ c ();
          Queue.push c lemma_queue
      end;
      ()

    let push_new_l = List.iter push_new

    let iter = List.iter
    let to_seq = Sequence.of_list
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
      ID.makef "max_depth_leq_%d" d
      |> Typed_cst.make_bool
      |> Term.const

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

  (* make a fresh constant, with a unique name *)
  let new_cst_ =
    let n = ref 0 in
    fun ?parent name ty ->
      let id = ID.makef "?%s_%d" name !n in
      incr n;
      Typed_cst.make_undef ?parent id ty

  (* build the disjunction [l] of cases for [info]. No side effect. *)
  let expand_cases (cst:cst) (ty:Ty.t) (info:cst_info): term list =
    assert (info.cst_cases = None);
    (* expand the given type *)
    let l = match Ty.view ty with
      | Atomic (_, Data cstors) ->
        (* datatype: refine by picking the head constructor *)
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
    l

  (** {2 Reduction to Normal Form} *)

  module Reduce = struct
    (* environment for evaluation: not-yet-evaluated terms *)
    type eval_env = term DB_env.t

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
        aux env t
      )

    (* set the normal form of [t], propagate to watchers *)
    let set_nf_ t new_t (e:explanation) : unit =
      if Term.equal t new_t then ()
      else (
        Backtrack.push_set_nf_ t;
        t.term_nf <- Some (new_t, e);
        Log.debugf 5
          (fun k->k
              "(@[<hv1>set_nf@ @[%a@]@ @[%a@]@ :explanation @[<v>%a@}@])"
              Term.pp t Term.pp new_t Explanation.pp e);
      )

    let get_nf t : explanation * term =
      match t.term_nf with
        | None -> Explanation.empty, t
        | Some (new_t,e) -> e, new_t

    (* compute the normal form of this term. We know at least one of its
       subterm(s) has been reduced *)
    let rec compute_nf (t:term) : explanation * term =
      (* follow the "normal form" pointer *)
      match t.term_nf with
        | Some (t', e) ->
          let e', nf = compute_nf t' in
          let exp = Explanation.append e e' in
          (* path compression here *)
          set_nf_ t nf exp;
          exp, nf
        | None -> compute_nf_noncached t

    and compute_nf_noncached t =
      assert (t.term_nf = None);
      match t.term_cell with
        | DB _ -> assert false (* non closed! *)
        | True | False ->
          Explanation.empty, t (* always trivial *)
        | Const c ->
          begin match c.cst_kind with
            | Cst_defined (ty, rhs) when not (Ty.is_arrow ty) ->
              (* expand defined constants *)
              compute_nf (Lazy.force rhs)
            | _ -> Explanation.empty, t
          end
        | Fun _ -> Explanation.empty, t (* no eval under lambda *)
        | Builtin b ->
          let e, b' =
            Term.fold_map_builtin compute_nf_add Explanation.empty b
          in
          (* try boolean reductions *)
          let e', t' = compute_builtin b' in
          let e = Explanation.append e' e in
          set_nf_ t t' e;
          e, t'
        | If (a,b,c) ->
          let e_a, a' = compute_nf a in
          assert (not (Term.equal a a'));
          let default() = Term.if_ a' b c in
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
          let default() = Term.match_ u' m in
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

    (* apply [f] to [l], until no beta-redex is found *)
    and compute_nf_app env e f l = match f.term_cell, l with
      | Const {cst_kind=Cst_defined (_, lazy def_f); _}, l ->
        assert (l <> []);
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
    and compute_builtin bu: explanation * term = match bu with
      | B_not a ->
        begin match a.term_cell with
          | True -> Explanation.empty, Term.false_
          | False -> Explanation.empty, Term.true_
          | _ -> Explanation.empty, Term.not_ a
        end
      | B_and (a,b) ->
        begin match a.term_cell, b.term_cell with
          | True, _ -> Explanation.empty, b
          | _, True -> Explanation.empty, a
          | False, _
          | _, False -> Explanation.empty, Term.false_
          | _ -> Explanation.empty, Term.and_ a b
        end
      | B_or (a,b) ->
        begin match a.term_cell, b.term_cell with
          | True, _
          | _, True -> Explanation.empty, Term.true_
          | False, _ -> Explanation.empty, b
          | _, False -> Explanation.empty, a
          | _ -> Explanation.empty, Term.or_ a b
        end
      | B_imply (a,b) ->
        begin match a.term_cell, b.term_cell with
          | _, True
          | False, _ -> Explanation.empty, Term.true_
          | True, _ -> Explanation.empty, b
          | _, False -> Explanation.empty, Term.not_ a
          | _ -> Explanation.empty, Term.imply a b
        end
      | B_eq (a,b) ->
        begin match a.term_cell, b.term_cell with
          | False, False
          | True, True -> Explanation.empty, Term.true_
          | True, False
          | False, True -> Explanation.empty, Term.false_
          | _ when Term.equal a b -> Explanation.empty, Term.true_ (* syntactic *)
          | _ ->
            begin match Term.as_cstor_app a, Term.as_cstor_app b with
              | Some (c1,ty1,l1), Some (c2,_,l2) ->
                if not (Typed_cst.equal c1 c2)
                then
                  (* [c1 ... = c2 ...] --> false, as distinct constructors
                     can never be equal *)
                  Explanation.empty, Term.false_
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
                  |> compute_nf
                )
                else Explanation.empty, Term.eq a b
              | _ -> Explanation.empty, Term.eq a b
            end
        end
  end

  let lit_of_exp_ (e:explanation_atom): Lit.t = match e with
    | E_lit (t, b) -> Lit.atom ~sign:b t
    | E_choice (cst, t) -> Lit.cst_choice cst t

  (* from explanation [e1, e2, ..., en] build the guard
         [e1 & e2 & ... & en => …], that is, the clause
         [not e1 | not e2 | ... | not en] *)
  let clause_guard_of_exp_ (e:explanation): Lit.t list =
    Explanation.to_seq e
    |> Sequence.map lit_of_exp_
    |> Sequence.map Lit.neg (* this is a guard! *)
    |> Sequence.to_rev_list
    |> CCList.sort_uniq ~cmp:Lit.compare

  (** {2 A literal asserted to SAT}

      We watch those literals depending on the set of constants
      that block their current normal form *)

  module Watched_lit : sig
    type t = Lit.t

    val watch : t -> unit
    val update_watches_of : t -> unit
    val update_all : unit -> unit
    val is_watched : t -> bool
    val size : unit -> int
    val to_seq : t Sequence.t
  end = struct
    type t = Lit.t

    let propagate_lit_ (l:t) (e:explanation): unit =
      let c = l :: clause_guard_of_exp_ e |> Clause.make in
      Log.debugf 4
        (fun k->k
            "(@[<hv1>@{<green>propagate_lit@}@ %a@ nf: %a@ clause: %a@])"
            Lit.pp l Lit.pp (snd (Reduce.compute_nf l)) Clause.pp c);
      Clause.push_new c;
      ()

    (* build clause(s) that explains that [c] must be one of its
       cases *)
    let clauses_of_cases (c:cst) (l:term list) (depth:int) : Clause.t list =
      (* guard for non-constant cases (depth limit) *)
      let lit_guard = Iterative_deepening.lit_of_depth depth in
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
                      Lazy.force info.cst_depth > depth
                    | _ -> false)
             in
             lit, needs_guard)
          l
      in
      (* at least one case *)
      let c_choose : Clause.t =
        List.map fst lits |> Clause.make
      (* at most one case *)
      and cs_once : Clause.t list =
        CCList.diagonal lits
        |> List.map
          (fun ((l1,_),(l2,_)) -> Clause.make [Term.not_ l1; Term.not_ l2])
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
      c_choose :: cs_limit @ cs_once

    (* add [t] to the list of literals that watch the constant [c] *)
    let watch_cst_ (c:cst) (t:t): unit =
      assert (Ty.is_prop t.term_ty);
      Log.debugf 2
        (fun k->k "(@[<1>watch_cst@ %a@ %a@])" Typed_cst.pp c Term.pp t);
      let ty, info = match c.cst_kind with
        | Cst_undef (ty,i) -> ty,i
        | Cst_bool | Cst_defined _ | Cst_cstor _ -> assert false
      in
      Hash_set.add info.cst_watched t;
      (* ensure [c] is expanded, unless it is currently too deep *)
      let not_too_deep l : bool =
        l <= (Iterative_deepening.current_depth() :> int)
      in
      (* check whether [c] is expanded *)
      begin match info.cst_cases with
        | None ->
          let depth = Lazy.force info.cst_depth in
          if not_too_deep depth
          then (
            (* [c] is blocking, not too deep, but not expanded *)
            let l = expand_cases c ty info in
            Log.debugf 4
              (fun k->k "(@[<1>expand_cases@ @[%a@]@ :into (@[%a@])@])"
                  Typed_cst.pp c (Utils.pp_list Term.pp) l);
            info.cst_cases <- Some l;
            incr stat_num_cst_expanded;
            Clause.push_new_l (clauses_of_cases c l depth)
          ) else (
            Log.debugf 3
              (fun k->k "cannot expand %a: too deep" Typed_cst.pp c);
          );
        | Some _ -> ()
      end;
      ()

    (* ensure that [t] is on the watchlist of all the
       constants it depends on;
       also ensure those constants are expanded *)
    let update_watches_of (t:t): unit =
      assert (Ty.is_prop t.term_ty);
      let e, new_t = Reduce.compute_nf t in
      (* if [new_t = true/false], propagate literal *)
      begin match new_t.term_cell with
        | True -> propagate_lit_ t e
        | False -> propagate_lit_ (Lit.neg t) e
        | _ ->
          (* partially evaluated literal: add [t] (not its
             temporary normal form) to the watch list of every
             blocking constant *)
          Log.debugf 4
            (fun k->k
                "(@[<1>update_watches@ %a@ :normal_form %a@ \
                 :deps (@[%a@])@])"
                Term.pp t Term.pp new_t
                (Utils.pp_list Typed_cst.pp) new_t.term_deps);
          List.iter (fun c -> watch_cst_ c t) new_t.term_deps;
      end;
      ()

    let watched_ : unit Lit.Tbl.t = Lit.Tbl.create 256

      (* TODO: if [lit] is new, do on-the-fly CNF of its inner formula
         (break not/and/or, maybe explore a bit the equalities eagerly?).
      *)

    let watch (lit:t) =
      let lit = Lit.abs lit in
      if not (Lit.Tbl.mem watched_ lit) then (
        Log.debugf 3
          (fun k->k "(@[<1>@{<green>watch_lit@}@ %a@])" Lit.pp lit);
        Lit.Tbl.add watched_ lit ();
        (* also ensure it is watched properly *)
        update_watches_of lit;
      )

    let is_watched lit : bool =
      let lit = Lit.abs lit in
      Lit.Tbl.mem watched_ lit

    let to_seq = Lit.Tbl.keys watched_

    let size () = Lit.Tbl.length watched_

    let update_all (): unit =
      to_seq |> Sequence.iter update_watches_of
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
          slice.push (c:>Lit.t list) ();
        done
      else (
        let c = Queue.pop Clause.conflicts in
        Queue.clear Clause.conflicts;
        raise (Conflict c)
      )

    (* assert [c := new_t], or conflict *)
    let assert_choice (c:cst) (new_t:term) : unit =
      let t_c = Term.const c in
      begin match t_c.term_nf with
        | None ->
          (* set normal form *)
          Reduce.set_nf_ t_c new_t (Explanation.return (E_choice (c, new_t)));
          (* re-compute every watching literal *)
          begin match c.cst_kind with
            | Cst_undef (_, info) ->
              Hash_set.iter Watched_lit.update_watches_of info.cst_watched
            | Cst_defined _ | Cst_bool | Cst_cstor _  -> assert false
          end;
        | Some (c_nf, e) ->
          (* compute current normal forms, to be sure *)
          let e, c_nf = Reduce.compute_nf_add e c_nf in
          let _, new_t = Reduce.compute_nf new_t in
          if Term.equal new_t c_nf
          then ()
          else (
            (* incompatible assignments: fail *)
            let concl = Lit.neg (Lit.cst_choice c new_t) in
            let c = concl :: clause_guard_of_exp_ e |> Clause.make in
            Clause.push_conflict c
          )
      end

    (* handle a literal assumed by the SAT solver *)
    let assume_lit (lit:Lit.t) : unit =
      Log.debugf 2
        (fun k->k "(@[<1>@{<green>assume_lit@}@ @[%a@]@])" Lit.pp lit);
      Watched_lit.watch lit;
      (* check consistency first *)
      let e, lit' = Reduce.compute_nf lit in
      begin match lit'.term_cell with
        | True -> ()
        | False ->
          (* conflict! *)
          let c = Lit.neg lit :: clause_guard_of_exp_ e |> Clause.make in
          Clause.push_conflict c
        | _ ->
          (* otherwise, see if it's an assignment *)
          begin match Lit.view lit with
            | Lit.V_false -> assert false
            | Lit.V_true
            | Lit.V_assert _ -> ()
            | Lit.V_cst_choice (c, t) -> assert_choice c t
          end;
      end

    (* propagation from the bool solver *)
    let assume slice =
      let start = slice.start in
      assert (slice.length > 0);
      (* do the propagations in a local frame *)
      if Config.progress then print_progress();
      try
        (* first, empty the tautology queue *)
        flush_new_clauses_into_slice slice;
        for i = start to start + slice.length - 1 do
          let lit = slice.get i in
          assume_lit lit;
        done;
        flush_new_clauses_into_slice slice;
        let lev = Backtrack.cur_level () in
        Sat lev
      with Conflict conflict_clause ->
        Log.debugf 3
          (fun k->k "(@[<1>raise_inconsistent@ %a@])"
              Clause.pp conflict_clause);
        Unsat ((conflict_clause :> Lit.t list), ())
  end

  module M = Msat.Solver.Make(M_expr)(M_th)(struct end)

  (* push one clause into [M], in the current level (not a lemma but
     an axiom) *)
  let push_clause (c:Clause.t): unit =
    Log.debugf 2 (fun k->k "(@[<1>push_clause@ @[%a@]@])" Clause.pp c);
    (* reduce to normal form the literals, ensure they
         are added to the proper constant watchlist(s) *)
    Clause.iter Watched_lit.watch c;
    incr stat_num_clause_push;
    M.assume [(c :> Lit.t list)]

  (** {2 Main Loop}

      - expand constants that block some literal
      - do some SAT solving
      - if there remain non-true goals, repeat
  *)

  module Main_loop : sig
    val push_toplevel_goal : Lit.t -> unit
    val solve : unit -> M.res
  end = struct
    (* list of terms to fully evaluate *)
    let toplevel_goals_ : term list ref = ref []

    (* add [t] to the set of terms that must be evaluated *)
    let push_toplevel_goal (t:term): unit =
      toplevel_goals_ := t :: !toplevel_goals_;
      ()

    (* check that this term fully evaluates to [true] *)
    let is_true_ (t:term): bool =
      let _, t' = Reduce.compute_nf t in
      assert (Term.equal t' (Reduce.get_nf t |> snd));
      match t'.term_cell with
        | True -> true
        | _ -> false

    (* main solve function *)
    let solve () : M.res = match M.solve () with
      | M.Unsat ->
        if Config.progress then flush_progress();
        M.Unsat
      | M.Sat ->
        assert (List.for_all Watched_lit.is_watched !toplevel_goals_);
        if List.for_all is_true_ !toplevel_goals_
        then (
          if Config.progress then flush_progress();
          M.Sat
        )
        else (
          Log.debugf 4
            (fun k->
               let pp_dep out c =
                 let _, nf = Reduce.get_nf (Term.const c) in
                 Format.fprintf out
                   "(@[%a@ nf:%a@ xpanded: %B@])"
                   Typed_cst.pp c Term.pp nf
                   (match Typed_cst.as_undefined c with
                     | None -> assert false
                     | Some (_,_,i) -> i.cst_cases <> None)
               in
               let pp_lit out l =
                 let e, nf = Reduce.get_nf l in
                 Format.fprintf out
                   "(@[<hv1>%a@ nf: %a@ exp: %a@ deps: (@[<hv>%a@])@])"
                   Lit.pp l Lit.pp nf Explanation.pp e
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

  let add_cst_support_ (c:cst): unit =
    CCList.Ref.push model_support_ c

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

    let add_statement st =
      Log.debugf 2
        (fun k->k "(@[add_statement@ @[%a@]@])" Ast.pp_statement st);
      match st with
        | Ast.Assert t ->
          let t = conv_term [] t in
          Main_loop.push_toplevel_goal t;
          push_clause (Clause.make [t])
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
          Main_loop.push_toplevel_goal t;
          push_clause (Clause.make [t])
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
    Format.fprintf out "(@[<v>%a@])"
      (Utils.pp_list pp_pair)
      (Typed_cst.Map.to_list m)

  (* follow "normal form" pointers deeply in the term *)
  let deref_deep (t:term) : term =
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
        | Fun (ty,body) -> Term.fun_ ty (aux body)
        | Builtin b -> Term.builtin (Term.map_builtin aux b)
    in
    aux t

  let compute_model_ () : model =
    !model_support_
    |> Sequence.of_list
    |> Sequence.map
      (fun c ->
         (* find normal form of [c] *)
         let t = Term.const c in
         let t = deref_deep t in
         c, t)
    |> Typed_cst.Map.of_seq

  let clause_of_mclause (c:M.St.clause): Clause.t =
    M.Proof.to_list c |> List.map (fun a -> a.M.St.lit) |> Clause.make

  (* convert unsat-core *)
  let clauses_of_unsat_core (core:M.St.clause list): Clause.t Sequence.t =
    Sequence.of_list core
    |> Sequence.map clause_of_mclause

  (* print all terms reachable from watched literals *)
  let pp_term_graph out () = Term.pp_dot out Watched_lit.to_seq

  let pp_stats out () : unit =
    Format.fprintf out
      "(@[<hv1>stats@ \
       :num_expanded %d@ \
       :num_clause_push %d@ \
       :num_clause_tautology %d@ \
       :num_lits %d\
       @])"
      !stat_num_cst_expanded
      !stat_num_clause_push
      !stat_num_clause_tautology
      (Watched_lit.size())

  let do_on_exit ~on_exit =
    List.iter (fun f->f()) on_exit;
    ()

  let add_statement_l = Conv.add_statement_l

  let rec pp_proof out p =
    let pp_step out = function
      | M.Proof.Hypothesis -> CCFormat.string out "hypothesis"
      | M.Proof.Lemma () -> Format.fprintf out "(@[<1>lemma@ ()@])"
      | M.Proof.Resolution (p1, p2, _) ->
        Format.fprintf out "(@[<1>resolution@ %a@ %a@])" pp_proof p1 pp_proof p2
    in
    let {M.Proof.conclusion; step } = M.Proof.expand p in
    let conclusion = clause_of_mclause conclusion in
    Format.fprintf out "(@[<hv1>step@ %a@ @[<1>from:@ %a@]@])"
      Clause.pp conclusion pp_step step

  let check ?(on_exit=[]) () =
    let module ID = Iterative_deepening in
    (* create a base level, just to be sure *)
    let base_level =
      ignore (M.push ());
      M.current_level ()
    in
    (* iterated deepening *)
    let rec iter state = match state with
      | ID.Exhausted ->
        do_on_exit ~on_exit;
        Unknown U_max_depth
      | ID.At (cur_depth, cur_lit) ->
        let _ = M.push () in
        (* restrict depth *)
        push_clause (Clause.make [cur_lit]);
        match Main_loop.solve () with
          | M.Sat ->
            let m = compute_model_ () in
            Log.debugf 1
              (fun k->k "@{<Yellow>** found SAT@} at depth %a"
                  ID.pp cur_depth);
            do_on_exit ~on_exit;
            Sat m
          | M.Unsat ->
            (* check if [max depth] literal involved in proof;
               - if not, truly UNSAT
               - if yes, try next level
            *)
            let core = M.get_proof () |> M.unsat_core in
            assert (Lit.equal (Lit.abs cur_lit) cur_lit);
            let depth_limited =
              clauses_of_unsat_core core
              |> Sequence.flat_map Clause.to_seq
              |> Sequence.exists
                (fun lit -> Lit.equal cur_lit (Lit.abs lit ))
            in
            Log.debugf 1
              (fun k->k
                  "@{<Yellow>** found Unsat@} at depth %a;@ \
                   depends on %a: %B"
                  ID.pp cur_depth Lit.pp cur_lit depth_limited);
            if depth_limited
            then (
              (* negation of the previous limit *)
              M.pop base_level;
              push_clause (Clause.make [Lit.neg cur_lit]);
              iter (ID.next ()) (* deeper! *)
            )
            else (
              do_on_exit ~on_exit;
              M.pop base_level;
              Unsat
            )
    in
    ID.reset ();
    Backtrack.backtrack 0;
    CCFun.finally
      ~h:(fun () -> M.pop M.base_level)
      ~f:(fun () -> iter (ID.current ()))
end

