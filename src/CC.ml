
(* This file is free software. See file "license" for more details. *)

(** {1 Functional Congruence Closure} *)

(** {2 Typed Constant} *)

module TypedConst = struct
  type kind =
    | Const of Ty.t
    | Cstor of Ty.t * Ty.data
    (* TODO: defined function (how? terms are not defined here) *)

  type t = {
    id: ID.t;
    kind: kind;
  }

  let ty t = match t.kind with
    | Const ty
    | Cstor (ty,_) -> ty

  (* TODO: also, pointer to the definition/declaration/datatype
     to get rid of environment *)

  let make id kind = {id; kind}
  let make_const id ty = make id (Const ty)
  let make_cstor id ty data = make id (Cstor (ty,data))

  let equal a b = ID.equal a.id b.id
  let compare a b = ID.compare a.id b.id
  let pp out a = ID.pp out a.id
end

(** {2 Typed De Bruijn indices} *)
module DB = struct
  type t = int * Ty.t
  let level = fst
  let ty = snd
  let succ (i,ty) = i+1,ty
  let hash (i,ty) = Hash.combine Ty.hash i ty
end

(** {2 Congruence Closure} *)

module Make(Dummy : sig end) = struct
  type if_pos =
    | If_test
    | If_then
    | If_else

  type term = {
    mutable term_id: int; (* unique ID *)
    term_ty: Ty.t;
    term_cell: term_cell;
    mutable term_root: term; (* representative *)
    mutable term_next: term; (* list of representatives *)
    mutable term_equiv_class: equiv_class; (* data for the whole EC *)
  }
  and term_cell =
    | True
    | False
    | DB of DB.t (* de bruijn indice *)
    | Const of TypedConst.t
    | App of term * term list
    | Fun of Ty.t * term
    | If of term * term * term
    | Match of term * (Ty.t list * term) ID.Map.t

  and equiv_class = {
    mutable ec_watched: occur_list; (* terms in which this occurs *)
    mutable ec_distinct: equiv_class list; (* incompatible classes *)
  }

  and occur_list = occurrence list
  and occurrence =
    | O_app_fun of term (* term is the function of an app *)
    | O_app_arg of term * int (* term is an app argument *)
    | O_fun
    | O_if of term * if_pos
    | O_match_head of term
    | O_match_cstor of term * ID.t

  module Equiv_class = struct
    type t = equiv_class

    let of_term t = t.term_equiv_class

    let true_ = {
      ec_watched=[];
      ec_distinct=[];
    }
    let false_ = {
      ec_watched=[];
      ec_distinct=[];
    }

    (* true and false: incompatible *)
    let () =
      true_.ec_distinct <- [false_];
      false_.ec_distinct <- [true_];
      ()

  end

  module Term = struct
    type t = term

    let term_hash_ (t:term) : int = match t.term_cell with
      | True -> 1
      | False -> 2
      | DB d -> Hash.combine DB.hash 3 d
      | _ -> assert false (* TODO*)

    (* equality that relies on physical equality of subterms *)
    let term_eq_ t1 t2 : bool =
      assert false (* TODO *)

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
        term_root=t;
        term_next=t;
        term_equiv_class =
          if b then Equiv_class.true_ else Equiv_class.false_;
      } in
      hashcons_ t

    let true_ = mk_bool_ true
    let false_ = mk_bool_ false

    (* true and false: incompatible *)
    let () =
      true_.term_equiv_class.ec_distinct <- [false_.term_equiv_class];
      false_.term_equiv_class.ec_distinct <- [true_.term_equiv_class];
      ()

    let mk_term_ cell ty : term =
      let rec t = {
        term_id= -1;
        term_ty=ty;
        term_cell=cell;
        term_root=t;
        term_next=t;
        term_equiv_class = {
          ec_watched=[];
          ec_distinct=[];
        };
      } in
      hashcons_ t

    let db d = mk_term_ (DB d) (DB.ty d)

    let const c = mk_term_ (Const c) (TypedConst.ty c)

    let app f l = match l with
      | [] -> f
      | _ ->
        (* TODO: compute ty *)
        let ty = assert false in
        mk_term_ (App (f,l)) ty

    let fun_ ty t =
      let ty' = Ty.arrow ty t.term_ty in
      mk_term_ (Fun (ty, t)) ty'

    let match_ t m = assert false (* TODO *)

    let if_ a b c =
      (* TODO: check types *)
      mk_term_ (If (a,b,c)) b.term_ty

    let not_ = assert false (* TODO *)

    (* TODO: meta-variables? *)

    let ty t = t.term_ty

    let equal a b = a==b

    let compare a b = CCOrd.int_ a.term_id b.term_id

    let print _ _ = assert false (* TODO *)

    (* TODO: most of the interface, interning, etc.
       be careful to exploit DAG structure as much as possible *)
  end

  exception Inconsistent of term * term * term * term

  (* TODO CUT HERE TODO *)

  let is_const t = match t.CT.shape with
    | CT.Const _ -> true
    | CT.Apply _ -> false

  (** Merge equations in the congruence closure structure. [q] is a list
      of [eqn], processed in FIFO order. May raise Inconsistent. *)
  let rec merge cc eqn = match eqn with
    | EqnSimple (a, b) ->
      (* a=b, just propagate *)
      propagate cc [PendingSimple eqn]
    | EqnApply (a1, a2, a) ->
      (* (a1 @ a2) = a *)
      let a1' = Puf.find cc.uf a1 in
      let a2' = Puf.find cc.uf a2 in
      begin try
        (* eqn' is (b1 @ b2) = b for some b1=a1', b2=a2' *)
        let eqn' = T2Hashtbl.find cc.lookup (a1', a2') in
        (* merge a and b because of eqn and eqn' *)
        propagate cc [PendingDouble (eqn, eqn')]
      with Not_found ->
        (* remember that a1' @ a2' = a *)
        let lookup = T2Hashtbl.replace cc.lookup (a1', a2') eqn in
        let use_a1' = try THashtbl.find cc.use a1' with Not_found -> [] in
        let use_a2' = try THashtbl.find cc.use a2' with Not_found -> [] in
        let use = THashtbl.replace cc.use a1' (eqn::use_a1') in
        let use = THashtbl.replace use a2' (eqn::use_a2') in
        { cc with use; lookup; }
      end
  (* propagate: merge pending equations *)
  and propagate cc eqns =
    let pending = ref eqns in
    let uf = ref cc.uf in
    let use = ref cc.use in
    let lookup = ref cc.lookup in
    (* process each pending equation *)
    while !pending <> [] do
      let eqn = List.hd !pending in
      pending := List.tl !pending;
      (* extract the two merged terms *)
      let a, b = match eqn with
        | PendingSimple (EqnSimple (a, b)) -> a, b
        | PendingDouble (EqnApply (a1,a2,a), EqnApply (b1,b2,b)) -> a, b
        | _ -> assert false
      in
      let a' = Puf.find !uf a in
      let b' = Puf.find !uf b in
      if not (CT.eq a' b') then begin
        let use_a' = try THashtbl.find !use a' with Not_found -> [] in
        let use_b' = try THashtbl.find !use b' with Not_found -> [] in
        (* merge a and b's equivalence classes *)
        (* Format.printf "merge %d %d@." a.CT.tag b.CT.tag; *)
        uf := Puf.union !uf a b eqn;
        (* check which of [a'] and [b'] is the new representative. [repr] is
            the new representative, and [other] is the former representative *)
        let repr = Puf.find !uf a' in
        let use_repr = ref (if CT.eq repr a' then use_a' else use_b') in
        let use_other  = if CT.eq repr a' then use_b' else use_a' in
        (* consider all c1@c2=c in use(a') *)
        List.iter
          (fun eqn -> match eqn with
          | EqnSimple _ -> ()
          | EqnApply (c1, c2, c) ->
            let c1' = Puf.find !uf c1 in
            let c2' = Puf.find !uf c2 in
            begin try
              let eqn' = T2Hashtbl.find !lookup (c1', c2') in
              (* merge eqn with eqn', by congruence *)
              pending := (PendingDouble (eqn,eqn')) :: !pending
            with Not_found ->
              lookup := T2Hashtbl.replace !lookup (c1', c2') eqn;
              use_repr := eqn :: !use_repr;
            end)
          use_other;
        (* update use list of [repr] *)
        use := THashtbl.replace !use repr !use_repr;
        (* check for inconsistencies *)
        match Puf.inconsistent !uf with
        | None -> ()  (* consistent *)
        | Some (t1, t2, t1', t2') ->
          (* inconsistent *)
          let cc = { cc with use= !use; lookup= !lookup; uf= !uf; } in
          raise (Inconsistent (cc, t1, t2, t1', t2'))
    end
  done;
  let cc = { cc with use= !use; lookup= !lookup; uf= !uf; } in
  cc

  (** Add the given term to the CC *)
  let rec add cc t =
    match t.CT.shape with
    | CT.Const _ ->
      cc   (* always trivially defined *)
    | CT.Apply (t1, t2) ->
      if BV.get cc.defined t.CT.tag
      then cc  (* already defined *)
      else begin
        (* note that [t] is defined, add it to the UF to avoid GC *)
        let defined = BV.set_true cc.defined t.CT.tag in
        let cc = {cc with defined; } in
        (* recursive add. invariant: if a term is added, then its subterms
           also are (hence the base case of constants or already added terms). *)
        let cc = add cc t1 in
        let cc = add cc t2 in
        let cc = merge cc (EqnApply (t1, t2, t)) in
        cc
      end

  (** Check whether the two terms are equal *)
  let eq cc t1 t2 =
    let cc = add (add cc t1) t2 in
    let t1' = Puf.find cc.uf t1 in
    let t2' = Puf.find cc.uf t2 in
    CT.eq t1' t2'

  (** Assert that the two terms are equal (may raise Inconsistent) *)
  let merge cc t1 t2 =
    let cc = add (add cc t1) t2 in
    merge cc (EqnSimple (t1, t2))

  (** Assert that the two given terms are distinct (may raise Inconsistent) *)
  let distinct cc t1 t2 =
    let cc = add (add cc t1) t2 in
    let t1' = Puf.find cc.uf t1 in
    let t2' = Puf.find cc.uf t2 in
    if CT.eq t1' t2'
      then raise (Inconsistent (cc, t1', t2', t1, t2)) (* they are equal, fail *)
      else
        (* remember that they should not become equal *)
        let uf = Puf.distinct cc.uf t1 t2 in
        { cc with uf; }

  type action =
    | Merge of CT.t * CT.t
    | Distinct of CT.t * CT.t
    (** Action that can be performed on the CC *)

  let do_action cc action = match action with
    | Merge (t1, t2) -> merge cc t1 t2
    | Distinct (t1, t2) -> distinct cc t1 t2

  (** Check whether the two terms can be equal *)
  let can_eq cc t1 t2 =
    let cc = add (add cc t1) t2 in
    not (Puf.must_be_distinct cc.uf t1 t2)

  (** Iterate on terms that are congruent to the given term *)
  let iter_equiv_class cc t f =
    Puf.iter_equiv_class cc.uf t f

  (** {3 Auxilliary Union-find for explanations} *)

  module SparseUF = struct
    module H = Hashtbl.Make(HashedCT)

    type t = uf_ref H.t
    and uf_ref = {
      term : CT.t;
      mutable parent : CT.t;
      mutable highest_node : CT.t;
    }  (** Union-find reference *)

    let create size = H.create size

    let get_ref uf t =
      try H.find uf t
      with Not_found ->
        let r_t = { term=t; parent=t; highest_node=t; } in
        H.add uf t r_t;
        r_t

    let rec find_ref uf r_t =
      if CT.eq r_t.parent r_t.term
        then r_t  (* fixpoint *)
        else
          let r_t' = get_ref uf r_t.parent in
          find_ref uf r_t'  (* recurse (no path compression) *)

    let find uf t =
      try
        let r_t = H.find uf t in
        (find_ref uf r_t).term
      with Not_found ->
        t

    let eq uf t1 t2 =
      CT.eq (find uf t1) (find uf t2)

    let highest_node uf t =
      try
        let r_t = H.find uf t in
        (find_ref uf r_t).highest_node
      with Not_found ->
        t

    (* oriented union (t1 -> t2), assuming t2 is "higher" than t1 *)
    let union uf t1 t2 =
      let r_t1' = find_ref uf (get_ref uf t1) in
      let r_t2' = find_ref uf (get_ref uf t2) in
      r_t1'.parent <- r_t2'.term
  end

  (** {3 Producing explanations} *)

  type explanation =
    | ByCongruence of CT.t * CT.t  (* direct congruence of terms *)
    | ByMerge of CT.t * CT.t       (* user merge of terms *)

  (** Explain why those two terms are equal (they must be) *)
  let explain cc t1 t2 =
    assert (eq cc t1 t2);
    (* keeps track of which equalities are already explained *)
    let explained = SparseUF.create 5 in
    let explanations = ref [] in
    (* equations waiting to be explained *)
    let pending = Queue.create () in
    Queue.push (t1,t2) pending;
    (* explain why a=c, where c is the root of the proof forest a belongs to *)
    let rec explain_along a c =
      let a' = SparseUF.highest_node explained a in
      if CT.eq a' c then ()
      else match Puf.explain_step cc.uf a' with
      | None -> assert (CT.eq a' c)
      | Some (b, e) ->
        (* a->b on the path from a to c *)
        begin match e with
        | PendingSimple (EqnSimple (a',b')) ->
          explanations := ByMerge (a', b') :: !explanations
        | PendingDouble (EqnApply (a1, a2, a'), EqnApply (b1, b2, b')) ->
          explanations := ByCongruence (a', b') :: !explanations;
          Queue.push (a1, b1) pending;
          Queue.push (a2, b2) pending;
        | _ -> assert false
        end;
        (* now a' = b is justified *)
        SparseUF.union explained a' b;
        (* recurse *)
        let new_a = SparseUF.highest_node explained b in
        explain_along new_a c
    in
    (* process pending equations *)
    while not (Queue.is_empty pending) do
      let a, b = Queue.pop pending in
      if SparseUF.eq explained a b
        then ()
        else begin
          let c = Puf.common_ancestor cc.uf a b in
          explain_along a c;
          explain_along b c;
        end
    done;
    !explanations
end

(** {2 Curryfied terms} *)

module Curryfy(X : Hashtbl.HashedType) = struct
  type symbol = X.t
  type t = {
    shape : shape;      (** Which kind of term is it? *)
    tag : int;          (** Unique ID *)
  }
  and shape =
    | Const of symbol   (** Constant *)
    | Apply of t * t    (** Curryfied application *)

  type term = t

  module WE = Weak.Make(struct
    type t = term
    let equal a b = match a.shape, b.shape with
      | Const ia, Const ib -> X.equal ia ib
      | Apply (a1,a2), Apply (b1,b2) -> a1 == b1 && a2 == b2
      | _ -> false
    let hash a = match a.shape with
      | Const i -> X.hash i
      | Apply (a, b) -> a.tag * 65599 + b.tag
  end)

  let __table = WE.create 10001
  let count = ref 0

  let hashcons t =
    let t' = WE.merge __table t in
    (if t == t' then incr count);
    t'

  let mk_const i =
    let t = {shape=Const i; tag= !count; } in
    hashcons t

  let mk_app a b =
    let t = {shape=Apply (a, b); tag= !count; } in
    hashcons t

  let get_id t = t.tag

  let eq t1 t2 = t1 == t2

  let rec pp_skel oc t = match t.shape with
    | Const _ -> Printf.fprintf oc "%d" t.tag
    | Apply (t1, t2) ->
      Printf.fprintf oc "(%a %a):%d" pp_skel t1 pp_skel t2 t.tag
end
