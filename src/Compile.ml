
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
  st_to_expand: A.term ID.Tbl.t; (* term -> its def *)
  mutable st_unknowns: var list; (* unknowns to appear in model *)
  mutable st_new_stmt_l : RA.statement CCVector.vector; (* new statements *)
}

let create() = {
  st_cst_tbl=ID.Tbl.create 64;
  st_unknowns=[];
  st_to_expand=ID.Tbl.create 32;
  st_new_stmt_l=CCVector.create();
}

exception Error of (Fmt.t -> unit)
let () = Printexc.register_printer
    (function
      | Error msg -> Fmt.sprintf "@[<2>in compile:@ %t@]" msg |> CCOpt.return
      | _ -> None)

let error (msg:string) = raise (Error (fun out -> Fmt.string out msg))
let errorf k = raise (Error
      (fun out -> k (fun fmt -> Format.fprintf out fmt)))

let find_cst ~st (c:ID.t) : RA.cst =
  try ID.Tbl.find st.st_cst_tbl c
  with Not_found ->
    errorf (fun k->k "undefined constant `%a`" ID.pp c)

let add_unknown ~st v =
  st.st_unknowns <- v :: st.st_unknowns;
  ()

(* TODO: should take 1/ set of RA.term rules  2/ A.term def *)
(* define a new function with a set of rewrite rules *)
let define_fun ~st (name:string) (ty:Ty.t) (rules:RA.rule list lazy_t) (def:A.term) : RA.cst =
  let id = ID.make name in
  let c = RA.Cst.mk_def id ty rules in
  Log.debugf 3
    (fun k->k "(@[define_fun %a@ :ty %a@ :rules %a@ :def-for %a@])"
        ID.pp id Ty.pp ty
        (Utils.pp_list RA.pp_rule) (Lazy.force rules)
        A.pp_term def);
  ID.Tbl.add st.st_cst_tbl id c;
  ID.Tbl.add st.st_to_expand id def;
  c

(* simple prefix skolemization: if [t = exists x1...xn. u],
   declare [x1...xn] as new unknowns (not to be in the final model)
   and return [u] instead, as well as an stironment
   that maps [x_i] to their corresponding new unknowns *)
let skolemize ~st (t:A.term) : A.term =
  let rec aux subst t = match A.term_view t with
    | A.Bind (A.Exists, v, u) ->
      let v' = Var.copy v in
      add_unknown ~st v';
      aux (A.Subst.add subst v (A.var v')) u
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
      seq lst (fun (lst,x) -> f x lst yield)

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

  let get_subst : A.Subst.t t
    = fun lst -> Sequence.return (lst, lst.s_a)

  let get_ra_subst : ra_subst t
    = fun lst -> Sequence.return (lst, lst.s_ra)

  let update_subst (f:A.Subst.t -> A.Subst.t) : unit t
    = fun lst ->
      let lst = {lst with s_a = f lst.s_a} in
      Sequence.return (lst, ())

  let update_ra_subst (f:ra_subst -> ra_subst) : unit t
    = fun lst ->
      let lst = {lst with s_ra = f lst.s_ra} in
      Sequence.return (lst, ())

  let add_ra_subst v t : unit t =
    update_ra_subst (Var.Map.add v t)

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
           | None -> RA.T.var v
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
          | None -> return (RA.T.var v)
          | Some t' -> aux pos vars t'
        end
      | A.Const c ->
        begin match ID.Tbl.get st.st_cst_tbl c with
          | None ->
            errorf
              (fun k->k "in `@[%a@]`,@ constant `%a` not defined%a"
                  A.pp_term t0 ID.pp c
                  (Fmt.some (Fmt.within " (in definition of " ")" ID.pp)) of_)
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
              (add_ra_subst x (RA.T.bool true) >>= fun () -> aux pos vars b)
              <+>
                (add_ra_subst x (RA.T.bool false) >>= fun () -> aux pos vars c)
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
              let c = find_cst ~st c in
              RA.T.app
                (RA.T.const c)
                (List.map RA.T.var c_vars)
            in
            (* bind [x = c vars] *)
            add_ra_subst x case >>= fun () ->
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
            let rules = lazy (
              begin
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
              end |> to_list'
            ) in
            (* term definition *)
            let def = A.fun_l closure t in
            let cst = define_fun ~st (mk_pat "match") (A.ty def) rules def in
            (* now apply definition to [u] *)
            aux Pos_inner vars u >|= fun u ->
            RA.T.app
              (RA.T.const cst)
              (List.map RA.T.var closure @ [u])
        end
      | A.Binop (A.Eq,a,_) when Ty.is_arrow (A.ty a) ->
        (* should have been removed *)
        errorf (fun k->k "forbidden equation between functions:@ `%a`" A.pp_term t)
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
        errorf (fun k->k "forbidden quantification:@ `%a`" A.pp_term t)
      | A.Bind (A.Fun, _, _) ->
        (* lambda-lifting *)
        let fun_vars, body = A.unfold_fun t in
        assert (fun_vars <> []);
        (* flatten body into a set of rules, adding [fun_vars] to closure *)
        let closure = fun_vars @ vars in
        let rules = lazy (
          begin
            aux Pos_inner closure body >>= fun rhs ->
            get_ra_subst >|= fun subst ->
            apply_ra_subst_vars_ subst closure, rhs
          end
          |> to_list'
        ) in
        (* term definition *)
        let def = A.fun_l vars t in
        let cst = define_fun ~st (mk_pat "fun") (A.ty def) rules def in
        RA.T.app
          (RA.T.const cst)
          (List.map RA.T.var closure)
        |> return
      | A.Bind (A.Mu,_,_) -> assert false (* TODO? *)
      | A.Undefined_value -> return (RA.T.undefined (A.ty t))
      | A.Unknown v -> return (RA.T.unknown v)
      | A.Select _ ->
        errorf (fun k->k "forbidden `select`@ in `%a`" A.pp_term t)
      | A.Switch _ -> assert false
      | A.Asserting (t, g) ->
        (* [t asserting g] --> [if g then t else undefined] *)
        let ty = A.ty t in
        let mk_undef t g = RA.T.if_ g t (RA.T.undefined ty) in
        mk_undef <$> aux pos vars t <*> aux Pos_inner vars g
    in
    Log.debugf 5
      (fun k->k "(@[<hv1>flatten_rec@ :term @[%a@]@ :vars (@[%a@])@ :of %a@])"
          A.pp_term t0 (Utils.pp_list Var.pp) vars
          Fmt.(some ID.pp) of_);
    aux pos vars t0

  let flatten_rec_l ~st ?of_ pos vars l =
    map_m (flatten_rec ~st ?of_ pos vars) l

  let flatten_def ~st ?of_ (vars:var list) (rhs:A.term): RA.rule list =
    begin
      flatten_rec ~st ?of_ Pos_toplevel vars rhs >>= fun rhs ->
      get_ra_subst >|= fun subst ->
      apply_ra_subst_vars_ subst vars, rhs
    end |> to_list'
end

let compile (st:state) (stmt:A.statement): RA.statement list =
  (* preprocessing to remove some constructs *)
  let preprocess (t:A.term): A.term = t in
  let preprocess_bool t : A.term =
    assert (Ty.is_prop (A.ty t));
    t
    |> skolemize ~st
    |> preprocess
  in
  (* how to flatten a toplevel proposition. Shoudl return only one term. *)
  let conv_prop t =
    let l =
      Flatten.flatten_rec ~st Flatten.Pos_toplevel [] t
      |> Flatten.to_list'
    in
    begin match l with
      | [f] -> f
      | _ ->
        errorf (fun k->k "flattening `%a`@ :expected one term@ :yields (@[%a@])"
          A.pp_term t (Utils.pp_list RA.T.pp) l)
    end
  in
  (* return statements, with fresh ones added *)
  let ret_l (l:RA.statement list) : RA.statement list =
    let prelude = CCVector.to_list st.st_new_stmt_l in
    CCVector.clear st.st_new_stmt_l;
    if l=[] then prelude else prelude @ l
  in
  let l = match stmt with
    | A.Data l ->
      (* declare constructors *)
      List.iter
        (fun d ->
           ID.Map.iter
             (fun c_id c_ty ->
                let c = RA.Cst.mk_cstor c_id c_ty in
                ID.Tbl.add st.st_cst_tbl c_id c)
             d.Ty.data_cstors)
        l;
      ret_l [ RA.Stmt.data l ]
    | A.TyDecl _ty_id ->
      assert false (* TODO: translate into datatype *)
    | A.Decl (_,_) ->
      assert false (* TODO: translate into datatype *)
    | A.Define l ->
      let l =
        List.map
          (fun (id,ty,def) ->
             let def = preprocess def in
             let vars, body = A.unfold_fun def in
             let rules = lazy (
               Flatten.flatten_def ~st ~of_:id vars body
             ) in
             let c = RA.Cst.mk_def id ty rules in
             ID.Tbl.add st.st_cst_tbl id c;
             c)
          l
      in
      (* force definitions *)
      List.iter
        (fun c -> match c.RA.cst_def with
           | RA.Cst_def (lazy _) -> () | _ -> assert false)
        l;
      (* return new defs *)
      ret_l [RA.Stmt.def l]
      | A.Assert t ->
        let t = t |> preprocess_bool |> conv_prop in
        ret_l [ RA.Stmt.goal t ]
      | A.Goal (unknowns,t) ->
        let t = t |> preprocess_bool |> conv_prop in
        ret_l [
          RA.Stmt.in_model unknowns;
          RA.Stmt.goal t;
        ]
  in
  Log.debugf 2
    (fun k->k "(@[<hv>compile@ :stmt %a@ :into (@[<hv>%a@])@])"
        A.pp_statement stmt
        (Utils.pp_list RA.Stmt.pp) l);
  l

let translate_model _st (_m:RM.t) : M.t =
  assert false (* TODO *)

