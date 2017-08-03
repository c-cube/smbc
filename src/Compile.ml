
(* This file is free software. See file "license" for more details. *)

(** {1 Compilation to Rewriting} *)

module Fmt = CCFormat

module A = Ast
module RA = Rw_ast

module M = Model
module RM = Rw_model

type var = Ty.t Var.t

type state = {
  st_cst_tbl: RA.cst ID.Tbl.t; (* defined constants *)
  st_unknown_tbl: var ID.Tbl.t; (* unknown -> variable *)
  mutable st_unknowns: ID.t list; (* unknowns to appear in model *)
  mutable st_new_stmt_l : RA.statement CCVector.vector; (* new statements *)
}

let create() = {
  st_cst_tbl=ID.Tbl.create 64;
  st_unknown_tbl=ID.Tbl.create 32;
  st_unknowns=[];
  st_new_stmt_l=CCVector.create();
}

let error msg = failwith ("in compile: "^ msg)
let errorf msg = Fmt.ksprintf ~f:error msg

let find_cst ~st (c:ID.t) : RA.cst =
  try ID.Tbl.find st.st_cst_tbl c
  with Not_found ->
    errorf "undefined constant `%a`" ID.pp c

(* create new unknown with given type *)
let mk_unknown ~st name ty : A.term =
  let c_id = ID.makef "?%s" name in
  let c = A.unknown c_id ty in
  st.st_unknowns <- c_id :: st.st_unknowns;
  c

(* TODO: should take 1/ set of RA.term rules  2/ A.term def *)
(* define a new function with a set of rewrite rules *)
let define_fun ~st:_ (_name:string) (_rules:RA.rule list) (_def:A.term) : RA.cst =
  assert false (* TODO *)

(* simple prefix skolemization: if [t = exists x1...xn. u],
   declare [x1...xn] as new unknowns (not to be in the final model)
   and return [u] instead, as well as an stironment
   that maps [x_i] to their corresponding new unknowns *)
let skolemize ~st (t:A.term) : A.term =
  let rec aux subst t = match A.term_view t with
    | A.Bind (A.Exists, v, u) ->
      let c = mk_unknown ~st (Var.id v |> ID.to_string) (Var.ty v) in
      aux (A.Subst.add subst v c) u
    | _ -> A.Subst.eval subst t
  in
  aux A.Subst.empty t

(* [t=u], but one of them is a lambda/function type. Add/create new variables
     [vars] and turn this into [t vars = u vars], modulo beta.
     @return [vars, t vars, u vars] *)
let complete_eq t u =
  let ty_args, ty_ret = Ty.unfold (A.ty t) in
  assert (Ty.equal Ty.prop ty_ret);
  assert (List.length ty_args > 0);
  (* unfold t and u *)
  let vars_t, t = A.unfold_fun t in
  let vars_u, u = A.unfold_fun u in
  (* variable names, for re-use *)
  let names =
    if List.length vars_t > List.length vars_u
    then List.map Var.name vars_t
    else List.map Var.name vars_u
  in
  (* make variables for full application *)
  let vars =
    List.mapi
      (fun i ty ->
         let name = try List.nth names i with _ -> Printf.sprintf "x_%d" i in
         Var.of_string name ty)
      ty_args
  in
  let mk_args_subst vars' =
    let n = List.length vars' in
    List.map A.var (CCList.drop n vars),
    A.Subst.of_list
      (List.combine vars' (CCList.take n vars |> List.map A.var))
  in
  let args_t, subst_t = mk_args_subst vars_t in
  let args_u, subst_u = mk_args_subst vars_u in
  let t = A.app (A.Subst.eval subst_t t) args_t in
  let u = A.app (A.Subst.eval subst_u u) args_u in
  vars, t, u

(* turn [f = g] into [∀x. f x=g x] *)
let remove_ext ~st:_ (t:A.term) : A.term =
  let rec aux t = match A.term_view t with
    | A.Binop (A.Eq,a,b) when Ty.is_arrow (A.ty a) ->
      let vars_forall, a, b = complete_eq a b in
      let t' = A.forall_l vars_forall (A.eq a b) in
      Log.debugf 5
        (fun k->k "(@[<2>rewrite-eq@ `%a`@ :into `%a`@])" A.pp_term t A.pp_term t');
      assert (vars_forall<>[]);
      aux t'
    | _ ->
      A.map ~bind:(fun () v -> (), v) ~f:(fun () -> aux) () t
  in
  aux t

(* eliminate selectors by defining custom symbols for them *)
let remove_select ~st:_ (_t:A.term) : A.term =
  assert false
  (* TODO:
     - use A.map to traverse term
     - for [select_c_i u] obtain the list of cstors of the type
     - get-or-create symbol with rules
       [select-c-i (c t1…tn) --> ti]
       [select-c-i (d t1…tm) --> undefined]
     - apply symbol to [u]
  *)

(** Flattening into lambda-free, match-free terms *)
module Flatten = struct
  type ra_subst = RA.term Var.Map.t

  type local_st = {
    s_a: A.Subst.t;
    s_ra: ra_subst;
  }

  let pp_ra_subst out (s:ra_subst) =
    let pp_b = Fmt.(pair Var.pp RA.T.pp) in
    Format.fprintf out "{@[%a@]}" (Utils.pp_list pp_b) (Var.Map.to_list s)

  type 'a t = local_st -> (local_st * 'a) Sequence.t

  let lst_empty : local_st = { s_a=A.Subst.empty; s_ra=Var.Map.empty }

  let empty : 'a t = fun _ -> Sequence.empty

  let return
    : type a. a -> a t
    = fun x lst -> Sequence.return (lst, x)

  let (>>=)
    : type a b. a t -> (a -> b t) -> b t
    = fun seq f lst yield ->
      seq lst (fun (lst,x) ->
        f x lst (fun (lst',y) ->
          let lst =
            { s_a=A.Subst.merge lst.s_a lst'.s_a;
              s_ra=Var.Map.merge_disj lst.s_ra lst'.s_ra; }
          in
          yield (lst,y)))

  let (>|=)
    : type a b. a t -> (a -> b) -> b t
    = fun seq f lst yield ->
      seq lst (fun (lst,x) ->
        yield (lst,f x))

  let (<*>)
    : ('a -> 'b) t -> 'a t -> 'b t
    = fun f x ->
      f >>= fun f ->
      x >|= fun x -> f x

  let (<$>) f x = x >|= f

  let add_subst
    : A.Subst.t -> unit t
    = fun sigma lst ->
      let lst = {
        lst with s_a = A.Subst.merge sigma lst.s_a
      } in
      Sequence.return (lst, ())

  let get_subst : A.Subst.t t
    = fun lst -> Sequence.return (lst, lst.s_a)

  let get_ra_subst : ra_subst t
    = fun lst -> Sequence.return (lst, lst.s_ra)

  let update_subst (f:A.Subst.t -> A.Subst.t) : unit t
    = fun lst ->
      let lst = {lst with s_a = f lst.s_a} in
      Sequence.return (lst, ())

  (* non deterministic choice *)
  let (<+>)
    : type a. a t -> a t -> a t
    = fun x y subst ->
      Sequence.append (x subst) (y subst)

  let rec map_m f l = match l with
    | [] -> return []
    | x :: tail ->
      f x >>= fun x ->
      map_m f tail >|= fun tail -> x::tail

  let rec fold_m f acc l = match l with
    | [] -> return acc
    | [x] -> f acc x
    | x :: tail ->
      f acc x >>= fun acc -> fold_m f acc tail

  let choice_l
    : 'a t list -> 'a t
    = fun l subst ->
      Sequence.flat_map (fun x -> x subst) (Sequence.of_list l)

  let of_list
    : 'a list -> 'a t
    = fun l subst ->
      Sequence.of_list l |> Sequence.map (fun x->subst,x)

  let to_list' : 'a t -> 'a list
    = fun seq -> seq lst_empty |> Sequence.map snd |> Sequence.to_rev_list

  let apply_subst_vars_ (subst:A.Subst.t) vars : A.term list =
    List.map
      (fun v -> A.Subst.find subst v |> CCOpt.get_or ~default:(A.var v))
      vars

  let apply_ra_subst_vars_ (subst:ra_subst) vars : RA.term list =
    List.map
      (fun v ->
         begin match Var.Map.get v subst with
           | Some t -> t
           | None ->
             errorf "could not find var `%a`@ in ra_subst `%a`" Var.pp v
               pp_ra_subst subst
         end)
      vars


  type position =
    | Pos_toplevel (* outside, as a formula *)
    | Pos_inner (* inside a term *)

  let pp_rules =
    Fmt.(Utils.pp_list Dump.(pair (list RA.T.pp |> hovbox) RA.T.pp) |> hovbox)

  (* conversion of terms can yield several possible terms, by
     eliminating if and match
     @param vars the variables that can be replaced in the context
     @param of_ the ID being defined, if any
  *)
  let flatten_rec ~st ?of_ (pos:position) (vars:var list) (t0:A.term): RA.term t =
    (* how to name intermediate subterms? *)
    let mk_pat what = match of_ with
      | None -> what ^  "_"
      | Some id -> Fmt.sprintf "%s_%s_" (ID.name id) what
    in
    let rec aux pos vars t : RA.term t = match A.term_view t with
      | A.Bool b -> return (RA.T.bool b)
      | A.Var v ->
        (* look [v] up in subst. If [v --> t'], then flatten [t']
           because it was not processed so far (bound in let) *)
        get_subst >>= fun subst ->
        begin match A.Subst.find subst v with
          | None -> errorf "in `%a`,@ variable `%a` occurs free" A.pp_term t0 Var.pp v
          | Some t' -> aux pos vars t'
        end
      | A.Const c ->
        begin match ID.Tbl.get st.st_cst_tbl c with
          | None -> errorf "in `%a`,@ constant `%a` not defined" A.pp_term t0 ID.pp c
          | Some cst -> return (RA.T.const cst)
        end
      | A.App (f,l) ->
        RA.T.app
        <$> aux Pos_inner vars f
        <*> map_m (aux Pos_inner vars) l
      | A.If (a,b,c) ->
        begin match A.term_view a with
          | A.Var x when List.exists (Var.equal x) vars ->
            (* substitute [x] with [true] and [false] in either branch *)
            begin
              (add_subst (A.Subst.singleton x A.true_) >>= fun () -> aux pos vars b)
              <+>
                (add_subst (A.Subst.singleton x A.false_) >>= fun () -> aux pos vars c)
            end
          | _ ->
            (* keep a "if", since it does not destruct an input var *)
            RA.T.if_
            <$> aux Pos_inner vars a
            <*> aux Pos_inner vars b
            <*> aux Pos_inner vars c
        end
      | A.Let (v,t,u) ->
        (* add let-bound terms to substitution without processing them.
           They will be processed differently at every place the
           variables are used *)
        update_subst (fun s -> A.Subst.add s v t) >>= fun () ->
        aux pos vars u
      | A.Match (u,m) ->
        begin match A.term_view u with
          | A.Var x when List.exists (Var.equal x) vars ->
            (* will replace [x] by each constructor *)
            of_list (ID.Map.to_list m) >>= fun (c,(c_vars,rhs)) ->
            (* the term [c c_vars] *)
            let case =
              let ty = Ty.arrow_l (List.map Var.ty c_vars) (A.ty rhs) in
              A.app
                (A.const c ty)
                (List.map A.var c_vars)
            in
            (* bind [x = c vars] *)
            let subst = A.Subst.add A.Subst.empty x case in
            add_subst subst >>= fun () ->
            (* directly replace by [rhs]. [c_vars] can be replaced themselves. *)
            aux pos (c_vars@vars) rhs
          | _ ->
            (* give a name to the match *)
            (* first, compute closure variables, i.e. variables that are free
               in the branches. *)
            let closure =
              ID.Map.values m
              |> Sequence.to_rev_list
              |> List.rev_map
                (fun (match_vars,rhs) ->
                   (* match variables are not free; just bind them temporarily *)
                   A.forall_l match_vars rhs)
              |> A.free_vars_l
              |> Var.Set.to_list
            in
            let cases =
              of_list (ID.Map.to_list m) >>= fun (cstor,(c_vars,rhs)) ->
              aux pos (c_vars@vars) rhs >>= fun rhs ->
              get_ra_subst >|= fun subst ->
              let case =
                let cst = find_cst ~st cstor in
                RA.T.app
                  (RA.T.const cst)
                  (apply_ra_subst_vars_ subst c_vars)
              in
              apply_ra_subst_vars_ subst closure @ [case], rhs
            in
            let rules = to_list' cases in
            (* term definition *)
            let def = A.fun_l closure t in
            Log.debugf 5
              (fun k->k "(@[define_match@ :term %a@ :rules %a@])" A.pp_term t pp_rules rules);
            let cst = define_fun ~st (mk_pat "match") rules def in
            (* now apply definition to [u] *)
            aux Pos_inner vars u >|= fun u ->
            RA.T.app
              (RA.T.const cst)
              (List.map RA.T.var closure @ [u])
        end
      | A.Binop (A.Eq,a,_) when Ty.is_arrow (A.ty a) ->
        (* should have been removed *)
        errorf "forbidden equation between functions:@ `%a`" A.pp_term t
      | A.Not t ->
        RA.T.unop RA.U_not <$> aux Pos_inner vars t
      | A.Binop (op,a,b) ->
        let op = match op with
          | A.Eq -> RA.B_eq
          | A.And -> RA.B_and
          | A.Imply -> RA.B_imply
          | A.Or -> RA.B_or
        in
        RA.T.binop op
        <$> aux Pos_toplevel vars a
        <*> aux Pos_toplevel vars b
      | A.Bind ((A.Forall | A.Exists),_,_) ->
        errorf "forbidden quantification:@ `%a`" A.pp_term t
      | A.Bind (A.Fun, _, _) ->
        (* lambda-lifting *)
        let fun_vars, body = A.unfold_fun t in
        assert (fun_vars <> []);
        (* flatten body into a set of rules, adding [fun_vars] to closure *)
        let closure = fun_vars @ vars in
        let rules =
          begin
            aux Pos_inner closure body >>= fun rhs ->
            get_ra_subst >|= fun subst ->
            apply_ra_subst_vars_ subst closure, rhs
          end
          |> to_list'
        in
        (* term definition *)
        let def = A.fun_l vars t in
        Log.debugf 5
          (fun k->k "(@[define_match@ :term %a@ :rules %a@])" A.pp_term t pp_rules rules);
        let cst = define_fun ~st (mk_pat "fun") rules def in
        RA.T.app
          (RA.T.const cst)
          (List.map RA.T.var closure)
        |> return
      | A.Bind (A.Mu,_,_) -> assert false (* TODO? *)
      | A.Undefined_value -> return (RA.T.undefined (A.ty t))
      | A.Unknown id ->
        let v = match ID.Tbl.get st.st_unknown_tbl id with
          | None ->
            let v = Var.make id (A.ty t) in
            ID.Tbl.add st.st_unknown_tbl id v;
            v
          | Some v -> v
        in
        return (RA.T.unknown v)
      | A.Select _ ->
        errorf "forbidden `select`@ in `%a`" A.pp_term t
      | A.Switch _ -> assert false
      | A.Asserting (t, g) ->
        (* [t asserting g] --> [if g then t else undefined] *)
        let ty = A.ty t in
        let mk_undef t g = RA.T.if_ g t (RA.T.undefined ty) in
        mk_undef <$> aux pos vars t <*> aux Pos_inner vars g
    in
    Log.debugf 5
      (fun k->k "(@[<2>flatten_rec@ `@[%a@]`@ vars: (@[%a@])@])"
          A.pp_term t0 (Utils.pp_list Var.pp) vars);
    aux pos vars t0

  let flatten_rec_l ~st ?of_ pos vars l =
    map_m (flatten_rec ~st ?of_ pos vars) l
end

let compile (st:state) (stmt:A.statement): RA.statement list =
  assert false (* TODO *)

let translate_model st (m:RM.t) : M.t =
  assert false (* TODO *)

(* TODO
val compile : state -> Ast.statement -> Rw_ast.statement list
(** [compile state st] compiles the statement's terms into rewrite-based
    terms, possibly modifying the state, and returns new statements. *)

val translate_model : state -> Rw_model.t -> Model.t
(** Translate a model back into normal AST *)

    let add_statement st =
      Log.debugf 2
        (fun k->k "(@[add_statement@ @[%a@]@])" A.pp_statement st);
      model_st_ := A.st_add_statement !model_st_ st;
      match st with
        | A.Assert t ->
          let st, t = skolemize t in
          let t = conv_term ~st t in
          Top_goals.push t;
          push_clause (Clause.make [Lit.atom t])
        | A.Goal (vars, t) ->
          (* skolemize *)
          let st, consts =
            CCList.fold_map
              (fun st v ->
                 let ty = Var.ty v |> conv_ty in
                 let c = Cst.make_undef ~depth:0 (Var.id v) ty in
                 add_let_bound st v (Term.const c), c)
              empty_st
              vars
          in
          (* model should contain values of [consts] *)
          List.iter add_cst_support_ consts;
          let t = conv_term_rec st t in
          Top_goals.push t;
          push_clause (Clause.make [Lit.atom t])
        | TyDecl id ->
          let rec ty = lazy (
            let ty0 = {
              uty_self=ty;
              uty_parent=None;
              uty_offset=0; (* root *)
              uty_pair=Lazy_none;
              uty_status=None;
            } in
            Ty_h.atomic id (Uninterpreted ty0)
          ) in
          (* model should contain domain of [ty] *)
          add_ty_support_ (Lazy.force ty);
          ID.Tbl.add ty_tbl_ id ty
        | A.Decl (id, ty) ->
          assert (not (ID.Tbl.mem decl_ty_ id));
          let ty = conv_ty ty in
          let cst = Cst.make_undef ~depth:0 id ty in
          add_cst_support_ cst; (* need it in model *)
          ID.Tbl.add decl_ty_ id (Lazy.from_val cst)
        | A.Data l ->
          (* declare the type, and all the constructors *)
          List.iter
            (fun {Ty.data_id; data_cstors} ->
               let ty = lazy (
                 let cstors =
                   ID.Map.to_seq data_cstors
                   |> Sequence.map
                     (fun (id_c, ty_c) ->
                        let c = lazy (
                          let ty_c = conv_ty ty_c in
                          Cst.make_cstor id_c ty_c
                        ) in
                        ID.Tbl.add decl_ty_ id_c c; (* declare *)
                        c)
                   |> Sequence.to_rev_list
                 in
                 Ty_h.atomic data_id (Data cstors)
               ) in
               ID.Tbl.add ty_tbl_ data_id ty;
            )
            l;
          (* force evaluation *)
          List.iter
            (fun {Ty.data_id; _} ->
               ID.Tbl.find ty_tbl_ data_id |> Lazy.force |> ignore)
            l
        | A.Define l ->
          (* declare the mutually recursive functions *)
          List.iter
            (fun (id,ty,rhs) ->
               let ty = conv_ty ty in
               let rhs = lazy (conv_term rhs) in
               let cst = lazy (
                 Cst.make_defined id ty rhs
               ) in
               ID.Tbl.add decl_ty_ id cst)
            l;
          (* force thunks *)
          List.iter
            (fun (id,_,_) ->
               let c = ID.Tbl.find decl_ty_ id |> Lazy.force in
               begin match c.cst_kind with
                 | Cst_defined (lazy _) -> () (* also force definition *)
                 | _ -> assert false
               end;
               (* also register the constant for expansion *)
               declare_defined_cst c
            )
            l

        | A.Fun (v,body) ->
          let st' = add_bound st v in
          let body = conv_term_rec st' body in
          let ty = Var.ty v |> conv_ty in
          Term.fun_ ty body
        | A.Select (sel, u) ->
          let u = conv_term_rec st u in
          let sel =
            let select_cstor = match ID.Tbl.get decl_ty_ sel.A.select_cstor with
              | Some (lazy c) ->
                assert (c.cst_kind = Cst_cstor);
                c
              | _ -> assert false
            in
            { select_name=Lazy.force sel.A.select_name;
              select_cstor; select_i=sel.A.select_i }
          in
          Term.select sel u
        | A.Forall (v,body) ->
          let st' = add_bound st v in
          let body = conv_term_rec st' body in
          let uty =
            let ty = Var.ty v |> conv_ty in
            match Ty_h.view ty with
              | Atomic (_, Uninterpreted uty) -> uty
              | _ -> errorf "forall: need to quantify on an uninterpreted type, not %a" Ty_h.pp ty
          in
          Term.forall uty body
        | A.Exists (v,body) ->
          let st' = add_bound st v in
          let body = conv_term_rec st' body in
          let uty =
            let ty = Var.ty v |> conv_ty in
            match Ty_h.view ty with
              | Atomic (_, Uninterpreted uty) -> uty
              | _ -> errorf "exists: need to quantify on an uninterpreted type, not %a" Ty_h.pp ty
          in
          Term.exists uty body
        | A.Mu (v,body) ->
          let st' = add_bound st v in
          let body = conv_term_rec st' body in
          Term.mu body
        | A.Match (u,m) ->
          let any_rhs_depends_vars = ref false in (* some RHS depends on matched arg? *)
          let m =
            ID.Map.map
              (fun (vars,rhs) ->
                 let n_vars = List.length vars in
                 let st', tys =
                   CCList.fold_map
                     (fun st v -> add_bound st v, Var.ty v |> conv_ty)
                     st vars
                 in
                 let rhs = conv_term_rec st' rhs in
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
              let u = conv_term_rec st u in
              Term.match_ u m
          end
        | A.Switch _ ->
          errorf "cannot convert switch %a" A.pp_term t
        | A.Let (v,t,u) ->
          (* substitute on the fly *)
          let t = conv_term_rec st t in
          let st' = add_let_bound st v t in
          conv_term_rec st' u
        | A.If (a,b,c) ->
          let b = conv_term_rec st b in
          let c = conv_term_rec st c in
          (* optim: [if _ b b --> b] *)
          if Term.equal b c
          then b
          else Term.if_ (conv_term_rec st a) b c
        | A.Not t -> Term.not_ (conv_term_rec st t)
        | A.Binop (op,a,b) ->
          let a = conv_term_rec st a in
          let b = conv_term_rec st b in
          begin match op with
            | A.And -> Term.and_ a b
            | A.Or -> Term.or_ a b
            | A.Imply -> Term.imply a b
            | A.Eqn -> Term.eq a b
          end
        | A.Undefined_value ->
          Term.undefined_value (conv_ty t.A.ty)
        | A.Asserting (t, g) ->
          (* [t asserting g] becomes  [if g t fail] *)
          let t = conv_term_rec st t in
          let g = conv_term_rec st g in
          Term.if_ g t (Term.undefined_value t.term_ty)

   *)
