
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

  (* for objects that are expanded on demand only *)
  type 'a lazily_expanded =
    | Lazy_some of 'a
    | Lazy_none

  (* main term cell *)
  type term = {
    mutable term_id: int; (* unique ID *)
    mutable term_ty: ty_h;
    term_cell: term_cell;
    mutable term_nf: (term * explanation) option;
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
    | Match of term * (ty_h list * term) ID.Map.t
    | Builtin of builtin
    | Check_assign of cst * term (* check a literal *)

  and db = int * ty_h

  (* what can block evaluation of a term *)
  and term_dep = cst

  and builtin =
    | B_not of term
    | B_eq of term * term
    | B_and of term * term * term * term (* parallel and *)
    | B_or of term * term
    | B_imply of term * term

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

  and cst = {
    cst_id: ID.t;
    cst_kind: cst_kind;
  }

  and cst_kind =
    | Cst_undef of ty_h * cst_info
    | Cst_cstor of ty_h
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

    let is_arrow t = match t.ty_cell with Arrow _ -> true | _ -> false

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

  module Typed_cst = struct
    type t = cst

    let id t = t.cst_id

    let ty_of_kind = function
      | Cst_defined (ty, _)
      | Cst_undef (ty, _)
      | Cst_cstor ty -> ty

    let ty t = ty_of_kind t.cst_kind

    let make cst_id cst_kind = {cst_id; cst_kind}
    let make_cstor id ty =
      let _, ret = Ty.unfold ty in
      assert (Ty.is_data ret);
      make id (Cst_cstor ty)
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

    let as_undefined (c:t) : (t * Ty.t * cst_info) option =
      match c.cst_kind with
        | Cst_undef (ty,i) -> Some (c,ty,i)
        | Cst_defined _ | Cst_cstor _ -> None

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
          ->
          CCOrd.int_ (int_of_cell_ a.lit_view) (int_of_cell_ b.lit_view)

  let hash_lit a =
    let sign = a.lit_sign in
    match a.lit_view with
      | Lit_fresh i -> Hash.combine3 1 (Hash.bool sign) (ID.hash i)
      | Lit_atom t -> Hash.combine3 2 (Hash.bool sign) (term_hash_ t)
      | Lit_assign (c,t) ->
        Hash.combine4 3 (Hash.bool sign) (Typed_cst.hash c) (term_hash_ t)

  let pp_dep = Typed_cst.pp

  module Backtrack = struct
    type _level = level
    type level = _level

    let dummy_level = -1

    type stack_cell =
      | S_set_nf of
          term * (term * explanation) option
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
          | Builtin (B_and (t1,t2,t3,t4)) ->
            Hash.list sub_hash [t1;t2;t3;t4]
          | Builtin (B_or (t1,t2)) -> Hash.combine3 22 t1.term_id t2.term_id
          | Builtin (B_imply (t1,t2)) -> Hash.combine3 23 t1.term_id t2.term_id
          | Builtin (B_eq (t1,t2)) -> Hash.combine3 24 t1.term_id t2.term_id
          | Mu sub -> Hash.combine sub_hash 30 sub
          | Check_assign (c,t) ->
            Hash.combine3 31 (Typed_cst.hash c) (sub_hash t)

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
          | Mu t1, Mu t2 -> t1==t2
          | Check_assign (c1,t1), Check_assign (c2,t2) ->
            Typed_cst.equal c1 c2 && term_equal_ t1 t2
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
          | Check_assign _, _
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
      } in
      H.hashcons t

    let true_ = mk_bool_ true
    let false_ = mk_bool_ false

    type deps =
      | Term_dep_cst of cst (* the term itself is a constant *)
      | Term_dep_none
      | Term_dep_sub of term
      | Term_dep_sub2 of term * term

    type delayed_ty =
      | DTy_direct of ty_h
      | DTy_lazy of (unit -> ty_h)

    let sorted_merge_ l1 l2 = CCList.sorted_merge_uniq ~cmp:compare l1 l2

    let cmp_term_dep_ a b = Typed_cst.compare a b

    (* build a term. If it's new, add it to the watchlist
       of every member of [watching] *)
    let mk_term_ ~(deps:deps) cell ~(ty:delayed_ty) : term =
      let t = {
        term_id= -1;
        term_ty=Ty.prop; (* will be changed *)
        term_cell=cell;
        term_nf=None;
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
          | Term_dep_cst c -> [c]
          | Term_dep_sub t -> t.term_deps
          | Term_dep_sub2 (a,b) ->
            CCList.sorted_merge_uniq
              ~cmp:cmp_term_dep_ a.term_deps b.term_deps
        in
        t'.term_deps <- deps
      );
      t'

    let db d =
      mk_term_ ~deps:Term_dep_none (DB d) ~ty:(DTy_direct (DB.ty d))

    let const c =
      let deps = match c.cst_kind with
        | Cst_undef _ -> Term_dep_cst c (* depends on evaluation! *)
        | Cst_defined _ | Cst_cstor _ -> Term_dep_none
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

    let check_assign c t : term =
      mk_term_ (Check_assign (c, t))
        ~deps:(Term_dep_cst c) ~ty:(DTy_direct Ty.prop)

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
      | Builtin (B_not t') -> t'
      | _ -> builtin_ ~deps:(Term_dep_sub t) (B_not t)

    (* might need to tranfer the negation from [t] to [sign] *)
    let abs t : t * bool = match t.term_cell with
      | False -> true_, false
      | Builtin (B_not t) -> t, false
      | _ -> t, true

    let and_ a b = builtin_ ~deps:(Term_dep_sub2 (a,b)) (B_and (a,b,a,b))
    let or_ a b = builtin_ ~deps:(Term_dep_sub2 (a,b)) (B_or (a,b))
    let imply a b = builtin_ ~deps:(Term_dep_sub2 (a,b)) (B_imply (a,b))
    let eq a b = builtin_ ~deps:(Term_dep_sub2 (a,b)) (B_eq (a,b))
    let neq a b = not_ (eq a b)

    let and_par a b c d =
      builtin_ ~deps:(Term_dep_sub2 (c,d)) (B_and (a,b,c,d))

    (* "eager" and, evaluating [a] first *)
    let and_eager a b = if_ a b false_

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
      | B_and (a,b,c,d) -> yield a; yield b; yield c; yield d

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

    let to_seq_depth t (yield:t*int ->unit): unit =
      let rec aux k t =
        yield (t,k);
        match t.term_cell with
          | DB _ | Const _ | True | False -> ()
          | App (f,l) -> aux k f; List.iter (aux k) l
          | If (a,b,c) -> aux k a; aux k b; aux k c
          | Match (t, m) ->
            aux k t;
            ID.Map.iter (fun _ (tys,rhs) -> aux (k+List.length tys) rhs) m
          | Builtin b -> builtin_to_seq b (aux k)
          | Mu body
          | Fun (_, body) -> aux (k+1) body
          | Check_assign _ -> ()
      in
      aux 0 t

    let to_seq t : t Sequence.t = to_seq_depth t |> Sequence.map fst

    (* return [Some] iff the term is an undefined constant *)
    let as_cst_undef (t:term): (cst * Ty.t * cst_info) option =
      match t.term_cell with
        | Const c -> Typed_cst.as_undefined c
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

    (* typical view for unification/equality *)
    type unif_form =
      | Unif_cst of cst * Ty.t * cst_info
      | Unif_cstor of cst * Ty.t * term list
      | Unif_none

    let as_unif (t:term): unif_form = match t.term_cell with
      | Const ({cst_kind=Cst_undef (ty,info); _} as c) ->
        Unif_cst (c,ty,info)
      | Const ({cst_kind=Cst_cstor ty; _} as c) -> Unif_cstor (c,ty,[])
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
        | Match (t,m) ->
          let pp_bind out (id,(_tys,rhs)) =
            fpf out "(@[<1>%a@ %a@])" ID.pp id pp rhs
          in
          let print_map =
            CCFormat.seq ~start:"" ~stop:"" ~sep:" " pp_bind
          in
          fpf out "(@[match %a@ (@[<hv>%a@])@])"
            pp t print_map (ID.Map.to_seq m)
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
      in
      pp out t

    let pp = pp_top ~ids:true

    (* environment for evaluation: not-yet-evaluated terms *)
    type eval_env = term DB_env.t

    (* shift open De Bruijn indices by [k] *)
    let shift_db k (t:term) : term =
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
          | Match (u, m) ->
            let u = aux depth u in
            let m =
              ID.Map.map
                (fun (tys,rhs) ->
                   tys, aux (depth + List.length tys) rhs)
                m
            in
            match_ u m
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
          | Check_assign _
            -> t (* closed *)
        and aux_l d l =
          List.map (aux d) l
        in
        aux 0 t
      )

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
          | Match (u, m) ->
            let u = aux env u in
            let m =
              ID.Map.map
                (fun (tys,rhs) ->
                   tys, aux (DB_env.push_none_l tys env) rhs)
                m
            in
            match_ u m
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
          | Check_assign _
            -> t (* closed *)
        and aux_l env l =
          List.map (aux env) l
        in
        aux env t
      )
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
    let cons e s = append (return e) s

    let is_empty = function
      | E_empty -> true
      | E_leaf _ | E_or _ | E_append _ -> false (* by smart cstor *)

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

    let to_lists_l e: lit list list = to_lists e |> Sequence.to_rev_list

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

    let iter f c = List.iter f c.lits
    let to_seq c = Sequence.of_list c.lits
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

  (** {2 Case Expansion} *)

  let declare_defined_cst _ = ()

  module Expand = struct
    (* make a fresh constant, with a unique name *)
    let new_cst_ =
      let n = ref 0 in
      fun ?exist_if ~parent name ty ->
        let id = ID.makef "?%s_%d" name !n in
        incr n;
        Typed_cst.make_undef ?exist_if ~parent id ty

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

    (* build clause(s) that explains that [c] must be one of its
       cases *)
    let clauses_of_cases (c:cst) (l:term list) (depth:int): Clause.t list =
      (* guard for non-constant cases (depth limit) *)
      let lit_guard = Iterative_deepening.lit_of_depth depth in
      let guard_is_some = CCOpt.is_some lit_guard in
      let info = match Typed_cst.as_undefined c with
        | None -> assert false
        | Some (_,_,info) -> info
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
                    | Const {cst_kind=Cst_undef (_,info); _} ->
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
      let mk_sub_cst ?exist_if ~parent ty_arg =
        let basename = Ty.mangle ty_arg in
        new_cst_ ?exist_if basename ty_arg ~parent
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
        | Cst_undef (ty,i) -> ty,i
        | Cst_defined _ | Cst_cstor _ ->
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
  end

  let pp_dep_full out c =
    let i = match Typed_cst.as_undefined c with
      | None -> assert false
      | Some (_,_,i) -> i
    in
    let nf = match i.cst_cur_case with
      | None -> Term.const c
      | Some (_, t') -> t'
    in
    Format.fprintf out
      "(@[%a@ nf:%a@ :expanded %B@])"
      Typed_cst.pp c Term.pp nf
      (match Typed_cst.as_undefined c with
        | None -> assert false
        | Some (_,_,i) -> i.cst_cases <> Lazy_none)

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
            | Cst_undef (_, {cst_cur_case=Some (e,new_t); _}) ->
              (* c := new_t, we can reduce *)
              compute_nf_add e new_t
            | Cst_undef _ | Cst_cstor _ ->
              Explanation.empty, t
          end
        | Fun _ -> Explanation.empty, t (* no eval under lambda *)
        | Mu body ->
          (* [mu x. body] becomes [body[x := mu x. body]] *)
          let env = DB_env.singleton t in
          Explanation.empty, Term.eval_db env body
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
                    let rhs = Term.eval_db env rhs in
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
            | Cst_undef (_, {cst_cur_case=None;_}) ->
              Explanation.empty, t
            | Cst_undef (_, ({cst_cur_case=Some (_,case');_} as info)) ->
              assert (match info.cst_cases with
                | Lazy_some l -> List.memq case l | Lazy_none -> false);
              (* NOTE: instead of saying [c=c10 --> false] because [c:=c1],
                 or because [c:=c2], etc. we can cut more search space by
                 explaining it by [not (c=c10)]  *)
              let lit = Lit.cst_choice c case in
              if Term.equal case case'
              then Explanation.return lit, Term.true_
              else Explanation.return (Lit.neg lit), Term.false_
            | Cst_cstor _ | Cst_defined _ ->
              assert false
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
          | Term.Unif_cstor (cstor, _, args), Term.Unif_cst (c, _, info)
          | Term.Unif_cst (c, _, info), Term.Unif_cstor (cstor, _, args) ->
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
          | _ -> e_ab, default()
        end

    let compute_nf_lit (lit:lit): explanation * lit =
      match Lit.view lit with
        | Lit_fresh _
        | Lit_assign (_,_) -> Explanation.empty, lit
        | Lit_atom t ->
          let e, t' = compute_nf t in
          e, Lit.atom ~sign:(Lit.sign lit) t'
  end

  (** {2 A literal asserted to SAT}

      A set of terms that must be evaluated (and their value, propagated)
      in the current partial model. *)

  module Top_terms : sig
    type t = private term

    val to_lit : t -> Lit.t
    val pp : t CCFormat.printer
    val watch : term -> unit
    val update : t -> unit (** re-check value, maybe propagate *)
    val is_top_term : term -> bool
    val size : unit -> int
    val to_seq : t Sequence.t
    val update_all : unit -> unit (** update all top terms *)
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

    let expand_cst_ (t:t)(c:cst) : unit =
      assert (Ty.is_prop t.term_ty);
      Log.debugf 2
        (fun k->k "(@[<1>watch_cst@ %a@ %a@])" Typed_cst.pp c Term.pp t);
      Expand.expand_cst c;
      ()

    let expand_dep (t:t) (d:term_dep) : unit = expand_cst_ t d

    (* evaluate [t] in current partial model, and expand the constants
       that block it *)
    let update (t:t): unit =
      assert (Ty.is_prop t.term_ty);
      let e, new_t = Reduce.compute_nf t in
      (* if [new_t = true/false], propagate literal *)
      begin match new_t.term_cell with
        | True -> propagate_lit_ t e
        | False -> propagate_lit_ (Term.not_ t) e
        | _ ->
          Log.debugf 4
            (fun k->k
                "(@[<1>update@ %a@ @[<1>:normal_form@ %a@]@ \
                 :deps (@[%a@])@ :exp @[<hv>%a@]@])"
                Term.pp t Term.pp new_t
                (Utils.pp_list pp_dep) new_t.term_deps
                Explanation.pp e);
          List.iter (expand_dep t) new_t.term_deps;
      end;
      ()

    (* NOTE: we use a list because it's lightweight, fast to iterate
       on, and we only add elements in it at the beginning *)
    let top_ : term list ref = ref []

    let mem_top_ (t:term): bool =
      List.exists (Term.equal t) !top_

    let watch (lit:term) =
      let lit, _ = Term.abs lit in
      if not (mem_top_ lit) then (
        Log.debugf 3
          (fun k->k "(@[<1>@{<green>watch_lit@}@ %a@])" pp lit);
        top_ := lit :: !top_;
        (* also ensure it is watched properly *)
        update lit;
      )

    let is_top_term (lit:t) : bool =
      let lit, _ = Term.abs lit in
      mem_top_ lit

    let to_seq yield = List.iter yield !top_

    let size () = List.length !top_

    (* is the dependency updated, i.e. decided by the SAT solver? *)
    let dep_updated (d:term_dep): bool = match d with
      | {cst_kind=Cst_undef (_, i); _} ->
        CCOpt.is_some i.cst_cur_case
      | _ -> assert false

    (* update all top terms (whose dependencies have been changed) *)
    let update_all () =
      to_seq
      |> Sequence.filter
        (fun t ->
           let _, nf = Reduce.get_nf t in
           List.exists dep_updated nf.term_deps)
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
    val push : ?internal:bool -> term -> unit
    (** [push g] registers [g] as a goal to be checked.
        @param part_of_encoding (default false) if true, goal is internal
        and will not be returned by {!to_seq} *)

    val to_seq : term Sequence.t
    (** Sequence of non-internal goals *)

    val check: unit -> unit
  end = struct
    type internal = bool

    (* list of terms to fully evaluate *)
    let toplevel_goals_ : (term * internal) list ref = ref []

    (* add [t] to the set of terms that must be evaluated *)
    let push ?(internal=false) (t:term): unit =
      toplevel_goals_ := (t, internal) :: !toplevel_goals_;
      ()

    let to_seq yield =
      List.iter (fun (goal,int) -> if not int then yield goal) !toplevel_goals_

    (* check that this term fully evaluates to [true] *)
    let is_true_ (t,_int): bool =
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
             let pp_dep out c =
               let _, nf = Reduce.get_nf (Term.const c) in
               Format.fprintf out
                 "(@[%a@ nf:%a@ :expanded %B@])"
                 Typed_cst.pp c Term.pp nf
                 (match Typed_cst.as_undefined c with
                   | None -> assert false
                   | Some (_,_,i) -> i.cst_cases <> Lazy_none)
             in
             let pp_goal out (g,_) =
               let e, nf = Reduce.get_nf g in
               Format.fprintf out
                 "(@[<hv1>%a@ nf: %a@ exp: %a@ deps: (@[<hv>%a@])@])"
                 Term.pp g Term .pp nf Explanation.pp e
                 (Utils.pp_list pp_dep) nf.term_deps
             in
             k "(@[<hv1>status_watched_lit@ (@[<v>%a@])@])"
               (Utils.pp_list pp_goal) !toplevel_goals_);
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

    (* assert [c := new_t], or conflict *)
    let assert_choice (c:cst)(new_t:term) : unit =
      let _, _, info = Typed_cst.as_undefined_exn c in
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
      |> Sequence.iter Top_terms.watch;
    incr stat_num_clause_push;
    M.assume [Clause.lits c]

  (** {2 Conversion} *)

  (* list of constants we are interested in *)
  let model_support_ : Typed_cst.t list ref = ref []

  let model_env_ : Ast.env ref = ref Ast.env_empty

  let add_cst_support_ (c:cst): unit =
    CCList.Ref.push model_support_ c

  (* encoding of an uninterpreted type, as a datatype + builtin forall/exist *)
  type uty_encoding = {
    uty_id: ID.t; (* the ID of the type *)
    uty_ty: ty_h; (* the type *)
    uty_card: cst; (* cardinality bound *)
    uty_zero: cst; (* the [zero] constructor *)
    uty_succ: cst; (* the [succ] constructor *)
    uty_forall: cst;
    uty_exists: cst;
  }

  (* map a uty to its encoding *)
  let tbl_uty : uty_encoding ID.Tbl.t = ID.Tbl.create 64

  (* list of (uninterpreted) types we are interested in *)
  let model_utys : uty_encoding list ref = ref []

  let add_ty_support_ (ty:uty_encoding): unit =
    CCList.Ref.push model_utys ty

  (* find the encoding of this uninterpreted type *)
  let uty_find_encoding (uty_id:ID.t) : uty_encoding =
    try ID.Tbl.find tbl_uty uty_id
    with Not_found ->
      errorf "could not find encoding of type %a" ID.pp uty_id

  module Conv = struct
    (* for converting Ast.Ty into Ty *)
    let ty_tbl_ : Ty.t lazy_t ID.Tbl.t = ID.Tbl.create 16

    (* for converting constants *)
    let decl_ty_ : cst lazy_t ID.Tbl.t = ID.Tbl.create 16

    (* environment for variables *)
    type conv_env = {
      let_bound: (term * int) ID.Map.t;
      (* let-bound variables, to be replaced. int=depth at binding position *)
      bound: int ID.Map.t; (* set of bound variables. int=depth at binding position *)
      depth: int;
    }

    let empty_env : conv_env =
      {let_bound=ID.Map.empty; bound=ID.Map.empty; depth=0}

    let add_bound env v =
      { env with
        depth=env.depth+1;
        bound=ID.Map.add (Ast.Var.id v) env.depth env.bound }

    (* add [v := t] to bindings. Depth is not increment (there will be no binders) *)
    let add_let_bound env v t =
      { env with
        let_bound=ID.Map.add (Ast.Var.id v) (t,env.depth) env.let_bound }

    let find_env env v =
      let id = Ast.Var.id v in
      ID.Map.get id env.let_bound, ID.Map.get id env.bound

    let uty_find_encoding_ty (ty:Ast.Ty.t) : uty_encoding =
      match ty with
        | Ast.Ty.Const id -> uty_find_encoding id
        | _ ->
          errorf "type %a is not a constant type, cannot be uninterpreted" Ast.Ty.pp ty

    let rec conv_ty (ty:Ast.Ty.t): Ty.t = match ty with
      | Ast.Ty.Prop -> Ty.prop
      | Ast.Ty.Const id ->
        begin try ID.Tbl.find ty_tbl_ id |> Lazy.force
          with Not_found -> errorf "type %a not in ty_tbl" ID.pp id
        end
      | Ast.Ty.Arrow (a,b) -> Ty.arrow (conv_ty a) (conv_ty b)

    let rec conv_term_rec
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
        let f = conv_term_rec env f in
        let l = List.map (conv_term_rec env) l in
        Term.app f l
      | Ast.Var v ->
        begin match find_env env v with
          | Some (t', depth_t'), _ ->
            assert (env.depth >= depth_t');
            let t' = Term.shift_db (env.depth - depth_t') t' in
            t'
          | None, Some d ->
            let ty = Ast.Var.ty v |> conv_ty in
            let level = env.depth - d - 1 in
            Term.db (DB.make level ty)
          | None, None -> errorf "could not find var `%a`" Ast.Var.pp v
        end
      | Ast.Fun (v,body) ->
        let env' = add_bound env v in
        let body = conv_term_rec env' body in
        let ty = Ast.Var.ty v |> conv_ty in
        Term.fun_ ty body
      | Ast.Forall (v,body) ->
        let env' = add_bound env v in
        let body = conv_term_rec env' body in
        let uty = uty_find_encoding_ty (Ast.Var.ty v) in
        Term.app_cst uty.uty_forall
          [Term.const uty.uty_zero; Term.fun_ uty.uty_ty body]
      | Ast.Exists (v,body) ->
        let env' = add_bound env v in
        let body = conv_term_rec env' body in
        let uty = uty_find_encoding_ty (Ast.Var.ty v) in
        Term.app_cst uty.uty_exists
          [Term.const uty.uty_zero; Term.fun_ uty.uty_ty body]
      | Ast.Mu (v,body) ->
        let env' = add_bound env v in
        let body = conv_term_rec env' body in
        Term.mu body
      | Ast.Match (u,m) ->
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
                 |> Sequence.exists
                   (fun (t,k) -> match t.term_cell with
                      | DB db ->
                        DB.level db < n_vars + k (* [k]: number of intermediate binders *)
                      | _ -> false)
               in
               if depends_on_vars then any_rhs_depends_vars := true;
               tys, rhs)
            m
        in
        (* optim: check whether all branches return the same term, that
           does not depend on matched variables *)
        (* TODO: do the closedness check during conversion, above *)
        let rhs_l =
          ID.Map.values m
          |> Sequence.map snd
          |> Sequence.sort_uniq ~cmp:Term.compare
          |> Sequence.to_rev_list
        in
        begin match rhs_l with
          | [x] when not (!any_rhs_depends_vars) ->
            (* every branch yields the same [x], which does not depend
               on the argument: remove the match and return [x] instead *)
            x
          | _ ->
            let u = conv_term_rec env u in
            Term.match_ u m
        end
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
          | Ast.Eq -> Term.eq a b
        end

    let conv_term t =
      let t' = conv_term_rec empty_env t in
      Log.debugf 2
        (fun k->k "(@[conv_term@ @[%a@]@ yields: %a@])" Ast.pp_term t Term.pp t');
      t'

    (* handle the given definitions *)
    let add_define l =
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
             | Cst_defined  (ty, lazy rhs) ->
               (* also force definition *)
               Log.debugf 5
                 (fun k->k "(@[def of @[%a : %a@]@ := %a@])"
                     Typed_cst.pp c Ty.pp ty Term.pp rhs);
               ()
             | _ -> assert false
           end;
           (* also register the constant for expansion *)
           declare_defined_cst c)
        l

    let add_assert ?internal (t:term) =
      Top_goals.push ?internal t;
      push_clause (Clause.make [Lit.atom t])

    (* declare a datatype corresponding to [uty_id] *)
    let add_ty_decl uty_id =
      let id_succ = ID.makef "S_%a" ID.pp_name uty_id in
      let id_zero = ID.makef "Z_%a" ID.pp_name uty_id in
      let rec ty = lazy (
        let cstors = [zero; succ] in
        Ty.atomic uty_id (Data cstors)
      ) and zero = lazy (
          Typed_cst.make_cstor id_zero (Lazy.force ty)
        ) and succ = lazy (
          let lazy uty = ty in
          let ty_succ = Ty.arrow uty uty in
          Typed_cst.make_cstor id_succ ty_succ
        ) in
      (* now, declare the type *)
      ID.Tbl.add ty_tbl_ uty_id ty;
      ID.Tbl.add decl_ty_ id_zero zero;
      ID.Tbl.add decl_ty_ id_succ succ;
      let lazy uty = ty in
      let lazy zero = zero in
      (* declare constant for cardinal *)
      let uty_card_id = ID.makef "card_%a" ID.pp_name uty_id in
      let uty_card = Typed_cst.make_undef uty_card_id uty in
      ID.Tbl.add decl_ty_ uty_card_id (Lazy.from_val uty_card);
      (* assert [card != 0] *)
      add_assert ~internal:true
        (Term.not_
           (Term.eq (Term.const uty_card) (Term.const zero)));
      (* define forall and exist *)
      let id_forall = ID.makef "forall_%a" ID.pp_name uty_id in
      let id_exists = ID.makef "exists_%a" ID.pp_name uty_id in
      (* [fun n f .
           if n=card
           then base
           else conn (f n) (self (succ n) f)]
         n is the first argument because we will replace [forall x. p]
         everywhere by [forall Z (fun x. p)] *)
      let mk_def (id_self:ID.t) (base:Ast.term) (conn:Ast.term->Ast.term->Ast.term) =
        let open Ast in
        let ty_n = Ty.const uty_id in
        let ty_f = Ty.(arrow ty_n prop) in
        let ty_succ = Ty.arrow ty_n ty_n in
        let ty_self = Ty.arrow_l [ty_n; ty_f] Ty.prop in
        let succ = const id_succ ty_succ in
        let self = const id_self ty_self in
        let card = const uty_card_id ty_n in
        let f = Var.make (ID.make "f") ty_f in
        let n = Var.make (ID.make "n") ty_n in
        let def =
          fun_l [n;f]
            (if_
               (eq (var n) card)
               base
               (conn
                  (app (var f) [var n])
                  (app self [app succ [var n]; var f])))
        in
        id_self, ty_self, def
      in
      let forall_def = mk_def id_forall Ast.true_ Ast.and_ in
      let exists_def = mk_def id_exists Ast.false_ Ast.or_ in
      add_define [forall_def];
      add_define [exists_def];
      let uty_forall = ID.Tbl.find decl_ty_ id_forall |> Lazy.force in
      let uty_exists = ID.Tbl.find decl_ty_ id_exists |> Lazy.force in
      let uty = {
        uty_id;
        uty_ty=uty;
        uty_card;
        uty_zero=zero;
        uty_succ=Lazy.force succ;
        uty_forall;
        uty_exists;
      } in
      ID.Tbl.add tbl_uty uty_id uty;
      (* model should contain domain of [ty] *)
      add_ty_support_ uty;
      ()

    let add_statement st =
      Log.debugf 2
        (fun k->k "(@[add_statement@ @[%a@]@])" Ast.pp_statement st);
      model_env_ := Ast.env_add_statement !model_env_ st;
      match st with
        | Ast.Assert t ->
          let t = conv_term t in
          add_assert  t
        | Ast.Goal (vars, t) ->
          (* skolemize *)
          let env, consts =
            CCList.fold_map
              (fun env v ->
                 let ty = Ast.Var.ty v |> conv_ty in
                 let c = Typed_cst.make_undef (Ast.Var.id v) ty in
                 add_let_bound env v (Term.const c), c)
              empty_env
              vars
          in
          (* model should contain values of [consts] *)
          List.iter add_cst_support_ consts;
          let t = conv_term_rec env t in
          add_assert t
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
        | Ast.Define l -> add_define l
        | Ast.TyDecl uty_id ->
          add_ty_decl uty_id

    let add_statement_l = List.iter add_statement
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

  (** {2 Build a Model} *)
  module Model_build = struct
    (* constants from [0] to [card uty - 1] *)
    type domain = {
      dom_uty: uty_encoding;
      dom_csts: ID.t array;
    }

    type domains = domain Ty.Tbl.t

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
          | Mu body -> Term.mu (aux body)
          | Builtin b -> Term.builtin (Term.map_builtin aux b)
          | Check_assign _
            -> assert false
      in
      aux t

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

    (* conversion from a nat-like datatype to an integer *)
    let t_as_n (uty_enc:uty_encoding) (t:term): int option =
      let rec aux n t = match t.term_cell with
        | Const c when Typed_cst.equal c uty_enc.uty_zero -> Some n
        | App ({term_cell=Const c; _}, [sub]) when Typed_cst.equal c uty_enc.uty_succ ->
          aux (n+1) sub
        | _ -> None
      in
      aux 0 (deref_deep t)

    let t_as_n_exn uty_enc t = match t_as_n uty_enc t with
      | Some n -> n
      | None -> errorf "cannot interpret term `@[%a@]`@ as a domain element" Term.pp t

    let is_db_0 (t:term): bool = match t.term_cell with
      | DB (0,_) -> true | _ -> false

    let const_of_dom (dom:domain) (i:int): Ast.term =
      if not (i>=0 && i < Array.length dom.dom_csts) then (
        errorf "cannot access the %d-th constant in dom(%a) (card %d)"
          i Ty.pp dom.dom_uty.uty_ty (Array.length dom.dom_csts)
      );
      A.const dom.dom_csts.(i) (ty_to_ast dom.dom_uty.uty_ty)

    type special =
      | S_dom_elt of domain * int
      | S_forall of uty_encoding * ty_h * term
      | S_exist of uty_encoding * ty_h * term
      | S_none

    let is_forall_ doms ty_arg f z = match Ty.Tbl.get doms ty_arg, f.term_cell with
      | Some dom, Const c ->
        Typed_cst.equal c dom.dom_uty.uty_forall && Typed_cst.equal z dom.dom_uty.uty_zero
      | _ -> false

    let is_exists_ doms ty_arg f z = match Ty.Tbl.get doms ty_arg, f.term_cell with
      | Some dom, Const c ->
        Typed_cst.equal c dom.dom_uty.uty_exists && Typed_cst.equal z dom.dom_uty.uty_zero
      | _ -> false

    let as_special (doms:domains) (t:term): special = match t.term_cell with
      | App (f, [{term_cell=Const z;_};{term_cell=Fun (ty_arg,body);_}])
        when is_forall_ doms ty_arg f z ->
        let dom = Ty.Tbl.find doms ty_arg in
        S_forall (dom.dom_uty, ty_arg, body)
      | App (f, [{term_cell=Const z;_};{term_cell=Fun (ty_arg,body);_}])
        when is_exists_ doms ty_arg f z ->
        let dom = Ty.Tbl.find doms ty_arg in
        S_exist (dom.dom_uty, ty_arg, body)
      | App _
      | Const _ ->
        begin match Ty.Tbl.get doms t.term_ty with
          | Some dom ->
            (* try to convert [t] as a domain constant *)
            begin match t_as_n dom.dom_uty t with
              | Some i ->
                S_dom_elt (dom,i)
              | None -> S_none
            end
          | None -> S_none
        end
      | _ -> S_none

    let term_to_ast (doms:domains) (t:term): Ast.term =
      (* toplevel decoder *)
      let rec aux env t = match as_special doms t with
        | S_dom_elt (dom,i) ->
          Log.debugf 5
            (fun k->k "@[<2>converting `@[%a@]`@ into dom constant %d@])"
                Term.pp t i);
          const_of_dom dom i
        | S_forall (_uty, ty_arg, body) ->
          Log.debugf 5
            (fun k->k "@[<2>converting `@[%a@]`@ into `forall`@])" Term.pp t);
          with_var ty_arg env
            ~f:(fun v env -> A.forall v (aux env body))
        | S_exist (_uty, ty_arg, body) ->
          Log.debugf 5
            (fun k->k "@[<2>converting `@[%a@]`@ into `exists`@])" Term.pp t);
          with_var ty_arg env
            ~f:(fun v env -> A.exists v (aux env body))
        | S_none -> aux_normal env t

      (* "normal" cases *)
      and aux_normal env t = match t.term_cell with
        | True -> A.true_
        | False -> A.false_
        | DB d ->
          begin match DB_env.get d env with
            | Some t' -> t'
            | None -> errorf "cannot find DB %a in env" Term.pp t
          end
        | Const cst ->
          A.const cst.cst_id (ty_to_ast t.term_ty)
        | App (f,l) ->
          A.app (aux env f) (List.map (aux env) l)
        | Fun (ty,bod) ->
          with_var ty env
            ~f:(fun v env -> A.fun_ v (aux env bod))
        | Mu _ -> assert false
        | If (a,b,c) -> A.if_ (aux env a)(aux env b) (aux env c)
        | Match (u,_) when Ty.Tbl.mem doms u.term_ty ->
          (* convert pattern matching on uninterpreted types into decision trees *)
          let dom = Ty.Tbl.find doms u.term_ty in
          match_to_ite env dom t
        | Match (u,m) ->
          let u = aux env u in
          let m =
            ID.Map.map
              (fun (tys,rhs) ->
                 with_vars tys env ~f:(fun vars env -> vars, aux env rhs))
              m
          in
          A.match_ u m
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

      (* convert a [match] on this uninterpreted type (given by its domain)
         into a nested if-then-else testing against [dom.dom_csts] *)
      and match_to_ite env (dom:domain) (top_t:term): Ast.term =
        (* @param n the number of successors already seen *)
        let rec aux_match n u0 m : Ast.term =
          Format.printf "at %d@." n;
          (* unfold match further *)
          assert (ID.Map.cardinal m = 2);
          let case_zero =
            match ID.Map.get (Typed_cst.id dom.dom_uty.uty_zero) m with
              | Some ([], rhs) -> aux env rhs
              | None | Some _ ->
                errorf "in `@[%a@]`,@ no case for Zero" Term.pp t
          and case_succ =
            match ID.Map.get (Typed_cst.id dom.dom_uty.uty_succ) m with
              | Some ([_],rhs) ->
                begin match rhs.term_cell with
                  | Match (u1, m1)
                    when Ty.equal t.term_ty dom.dom_uty.uty_ty
                      && is_db_0 u1
                      && n+1 < Array.length dom.dom_csts ->
                    (* recurse in subtree *)
                    aux_match (n+1) u0 m1
                  | _ ->
                    aux env rhs (* the "else" case *)
                end
              | None | Some _ ->
                errorf "in `@[%a@]`,@ no case for Succ" Term.pp top_t
          in
          Ast.if_
            (Ast.eq u0 (const_of_dom dom n))
            case_zero
            case_succ
        in
        match top_t.term_cell with
          | Match (u0, m) ->
            let u0 = aux env u0 in
            aux_match 0 u0 m
          | _ -> assert false
      in
      Log.debugf 5 (fun k->k "(@[<2>convert_term `@[%a@]`@])" Term.pp t);
      aux DB_env.empty t

    (* build a domain of the appropriate size for this uninterpreted type *)
    let compute_domain (uty_enc:uty_encoding): domain =
      let uty_id = uty_enc.uty_id in
      (* compute cardinal *)
      let card = t_as_n_exn uty_enc (Term.const uty_enc.uty_card) in
      Log.debugf 3
        (fun k->k "@[<2>uninterpreted type %a@ has cardinality %d@]" ID.pp uty_id card);
      assert (card > 0);
      (* now build constants from [0] to [card-1] *)
      let dom =
        Array.init card
          (fun i -> ID.makef "$%a_%d" ID.pp_name uty_id i)
      in
      {dom_uty=uty_enc; dom_csts=dom}

    let build () : model =
      Log.debug 2 "building model…";
      let env = !model_env_ in
      (* compute domains of uninterpreted types *)
      let doms : domains =
        !model_utys
        |> Sequence.of_list
        |> Sequence.map
          (fun uty -> uty.uty_ty, compute_domain uty)
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
             let t = deref_deep t |> term_to_ast doms in
             c.cst_id, t)
        |> ID.Map.of_seq
      and top_goals =
        Top_goals.to_seq
        |> Sequence.map (term_to_ast doms)
        |> Sequence.to_list
      in
      (* now we can convert domains *)
      let domains =
        Ty.Tbl.to_seq doms
        |> Sequence.map
          (fun (ty,dom) ->
             let dom = Array.to_list dom.dom_csts in
             ty_to_ast ty, dom)
        |> Ast.Ty.Map.of_seq
      in
      Model.make ~env ~consts ~domains ~top_goals

    let check m =
      Log.debugf 1 (fun k->k "checking model…");
      Log.debugf 5 (fun k->k "(@[<1>candidate model: %a@])" Model.pp m);
      Model.check m
  end

  (*
    FIXME: constraint on every toplevel constant of every uninterpreted type [u],
    forcing it to be smaller than card_u (how exactly? special builtin `<`, that
    propagates properly then?)
     *)

  let clause_of_mclause (c:M.St.clause): Clause.t =
    M.Proof.to_list c |> List.map (fun a -> a.M.St.lit) |> Clause.make

  (* convert unsat-core *)
  let clauses_of_unsat_core (core:M.St.clause list): Clause.t Sequence.t =
    Sequence.of_list core
    |> Sequence.map clause_of_mclause

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
        let core = p |> M.unsat_core in
        let incomplete =
          clauses_of_unsat_core core
          |> Sequence.flat_map Clause.to_seq
          |> Sequence.exists
            (fun lit -> match Lit.view lit with
               | Lit_assign (c,_) ->
                 begin match c.cst_kind with
                   | Cst_undef (_, i) when not i.cst_complete -> true
                   | _ -> false
                 end
               | _ -> false)
        in
        if incomplete then PS_incomplete else PS_complete
    end

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
            let m = Model_build.build () in
            Log.debugf 1
              (fun k->k "@{<Yellow>** found SAT@} at depth %a"
                  ID.pp cur_depth);
            do_on_exit ~on_exit;
            if check then Model_build.check m;
            Sat m
          | M.Unsat us ->
            (* check if [max depth] literal involved in proof;
               - if not, truly UNSAT
               - if yes, try next level
            *)
            let p = us.SI.get_proof () in
            Log.debugf 4 (fun k->k "proof: @[%a@]@." pp_proof p);
            let status = proof_status cur_lit in
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

