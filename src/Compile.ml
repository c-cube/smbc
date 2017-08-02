
(* This file is free software. See file "license" for more details. *)

(** {1 Compilation to Rewriting} *)

module A = Ast
module RA = Rw_ast

type state = {
  st_foo: unit;
}

let create() = {
  st_foo=();
}

(* simple prefix skolemization: if [t = exists x1...xn. u],
   declare [x1...xn] as new unknowns (not to be in the final model)
   and return [u] instead, as well as an stironment
   that maps [x_i] to their corresponding new unknowns *)
let skolemize ~st (t:A.term) : A.term =
  let rec aux st t = match A.term_view t with
    | A.Exists (v, u) ->
      let ty = conv_ty (Var.ty v) in
      let c_id = ID.makef "?%s" (Var.id v |> ID.to_string) in
      let c = Cst.make_undef ~depth:0 c_id ty in
      let st = add_let_bound st v (Term.const c) in
      aux st u
    | _ -> st, t
  in
  aux empty_st t

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
