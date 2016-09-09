
(* This file is free software. See file "license" for more details. *)

(** {1 Model} *)

module A = Ast

type term = A.term
type ty = A.Ty.t
type domain = ID.t list

type t = {
  env: A.env;
  (* environment, defining symbols *)
  domains: domain A.Ty.Map.t;
  (* uninterpreted type -> its domain *)
  consts: term ID.Map.t;
  (* constant -> its value *)
}

let make ~env ~consts ~domains =
  {env; consts; domains}

type entry =
  | E_ty of ty * domain
  | E_const of ID.t * term

let pp out (m:t) =
  let pp_cst_name out c = ID.pp_name out c in
  let pp_entry out = function
    | E_ty (ty,l) ->
      Format.fprintf out "(@[<1>type@ %a@ (@[<hv>%a@])@])"
        A.Ty.pp ty (Utils.pp_list pp_cst_name) l
    | E_const (c,t) ->
      Format.fprintf out "(@[<1>val@ %a@ %a@])"
        ID.pp_name c A.pp_term t
  in
  let es =
    CCList.append
      (A.Ty.Map.to_list m.domains |> List.map (fun (ty,dom) -> E_ty (ty,dom)))
      (ID.Map.to_list m.consts |> List.map (fun (c,t) -> E_const (c,t)))
  in
  Format.fprintf out "(@[<v>%a@])" (Utils.pp_list pp_entry) es

exception Bad_model of t * term * term
exception Error of string

let () = Printexc.register_printer
    (function
      | Error msg -> Some ("internal error: " ^ msg)
      | Bad_model (m,t,t') ->
        let msg = CCFormat.sprintf
            "@[<hv2>Bad model:@ goal `@[%a@]`@ evaluates to `@[%a@]`,@ \
             not true,@ in model @[%a@]@."
            A.pp_term t A.pp_term t' pp m
        in
        Some msg
      | _ -> None)

let errorf msg = CCFormat.ksprintf msg ~f:(fun s -> raise (Error s))

module VarMap = CCMap.Make(struct
    type t = A.Ty.t A.Var.t
    let compare = A.Var.compare
  end)

let empty_subst = VarMap.empty

let rec as_cstor_app env t = match A.term_view t with
  | A.Const id ->
    begin match A.env_find_def env id with
      | Some (A.E_cstor ty) -> Some (id, ty, [])
      | _ -> None
    end
  | A.App (f, l) ->
    CCOpt.map (fun (id,ty,l') -> id,ty,l'@l) (as_cstor_app env f)
  | _ -> None

let as_domain_elt env t = match A.term_view t with
  | A.Const id ->
    begin match A.env_find_def env id with
      | Some A.E_uninterpreted_cst -> Some id
      | _ -> None
    end
  | _ -> None

let apply_subst subst t =
  let rec aux subst t = match A.term_view t with
    | A.Var v -> VarMap.get_or ~or_:t v subst
    | A.True
    | A.False
    | A.Const _ -> t
    | A.App (f,l) -> A.app (aux subst f) (List.map (aux subst) l)
    | A.If (a,b,c) -> A.if_ (aux subst a) (aux subst b) (aux subst c)
    | A.Match (u,m) ->
      (* TODO: rename *)
      A.match_ (aux subst u)
        (ID.Map.map (fun (vars,rhs) ->  vars, aux subst rhs) m)
    | A.Switch (u,m) ->
      A.switch (aux subst u) (ID.Map.map (aux subst) m)
    | A.Let (x,t,u) ->
      let x', subst' = rename_var x subst in
      A.let_ x' (aux subst t) (aux subst' u)
    | A.Fun (x,body) ->
      let x', subst' = rename_var x subst in
      A.fun_ x' (aux subst' body)
    | A.Forall (x,body) ->
      let x', subst' = rename_var x subst in
      A.forall x' (aux subst' body)
    | A.Exists (x,body) ->
      let x', subst' = rename_var x subst in
      A.exists x' (aux subst' body)
    | A.Mu (_,_) -> assert false
    | A.Not f -> A.not_ (aux subst f)
    | A.Binop (op,a,b) -> A.binop op (aux subst a)(aux subst b)
  and rename_var v subst =
    let v' = A.Var.copy v in
    let subst' = VarMap.add v (A.var v') subst in
    v', subst'
  in
  aux subst t

(* eval term [t] under model [m] *)
let eval (m:t) (t:term) =
  let rec aux (subst:term VarMap.t) (t:term) =
    match A.term_view t with
      | A.True
      | A.False -> t
      | A.Var v -> VarMap.get_or ~or_:t v subst
      | A.Const c ->
        begin match A.env_find_def m.env c with
          | Some (A.E_defined (_, t')) -> aux empty_subst t'
          | _ ->
            begin match ID.Map.get c m.consts with
              | None -> t
              | Some t' -> aux subst t'
            end
        end
      | A.App (f,l) ->
        (* here, call by value *)
        let f = aux subst f in
        let l = List.map (aux subst) l in
        aux_app subst f l
      | A.If (a,b,c) ->
        let a = aux subst a in
        begin match A.term_view a with
          | A.True -> aux subst b
          | A.False -> aux subst c
          | _ -> A.if_ a b c
        end
      | A.Mu _ -> assert false
      | A.Let (x,t,u) ->
        let t = aux subst t in
        let subst' = VarMap.add x t subst in
        aux subst' u
      | A.Fun _ -> t
      | A.Forall (v,body)
      | A.Exists (v,body) ->
        let ty = A.Var.ty v in
        let dom =
          try A.Ty.Map.find ty m.domains
          with Not_found -> errorf "could not find type %a in model" A.Ty.pp ty
        in
        (* expand into and/or over the domain *)
        let t' =
          let l =
            List.map
              (fun c_dom ->
                 let subst' = VarMap.add v (A.const c_dom ty) subst in
                 aux subst' body)
              dom
          in
          match A.term_view t with
            | A.Forall _ -> A.and_l l
            | A.Exists _ -> A.or_l l
            | _ -> assert false
        in
        aux subst t'
      | A.Match (u, branches) ->
        let u = aux subst u in
        begin match as_cstor_app m.env u with
          | None -> A.match_ u branches
          | Some (c, _, args) ->
            match ID.Map.get c branches with
              | None -> assert false
              | Some (vars, rhs) ->
                assert (List.length vars = List.length args);
                let subst' =
                  List.fold_left2
                    (fun s v t -> VarMap.add v t s)
                    subst vars args
                in
                aux subst' rhs
        end
      | A.Switch (u, map) ->
        let u = aux subst u in
        begin match as_domain_elt m.env u with
          | None -> A.switch u map
          | Some cst ->
            begin match ID.Map.get cst map with
              | Some rhs -> aux subst rhs
              | None -> A.switch u map
            end
        end
      | A.Not f ->
        let f = aux subst f in
        begin match A.term_view f with
          | A.True -> A.false_
          | A.False -> A.true_
          | _ -> A.not_ f
        end
      | A.Binop (op, a, b) ->
        let a = aux subst a in
        let b = aux subst b in
        begin match op with
          | A.And ->
            begin match A.term_view a, A.term_view b with
              | A.True, A.True -> A.true_
              | A.False, _
              | _, A.False -> A.false_
              | _ -> A.and_ a b
            end
          | A.Or ->
            begin match A.term_view a, A.term_view b with
              | A.True, _
              | _, A.True -> A.true_
              | A.False, A.False -> A.false_
              | _ -> A.or_ a b
            end
          | A.Imply ->
            begin match A.term_view a, A.term_view b with
              | _, A.True
              | A.False, _  -> A.true_
              | A.True, A.False -> A.false_
              | _ -> A.imply a b
            end
          | A.Eq ->
            begin match A.term_view a, A.term_view b with
              | A.True, A.True
              | A.False, A.False -> A.true_
              | A.True, A.False
              | A.False, A.True -> A.false_
              | _ ->
                begin match as_cstor_app m.env a, as_cstor_app m.env b with
                  | Some (c1,_,l1), Some (c2,_,l2) ->
                    if ID.equal c1 c2 then (
                      assert (List.length l1 = List.length l2);
                      aux subst (A.and_l (List.map2 A.eq l1 l2))
                    ) else A.false_
                  | _ ->
                    begin match as_domain_elt m.env a, as_domain_elt m.env b with
                      | Some c1, Some c2 ->
                        (* domain elements: they are all distinct *)
                        if ID.equal c1 c2
                        then A.true_
                        else A.false_
                      | _ ->
                        A.eq a b
                    end
                end
            end
        end
  and aux_app subst f l = match A.term_view f, l with
    | A.Const c, _ ->
      begin match A.env_find_def m.env c with
        | Some (A.E_defined (_, def_f)) ->
          aux_app subst def_f l
        | _ -> aux_app' subst f l
      end
    | A.Fun (v, body), arg :: tail ->
      let subst = VarMap.add v arg subst in
      aux_app subst body tail
    | A.Var v, _ ->
      begin match VarMap.get v subst with
        | Some f' -> aux_app subst f' l
        | None -> aux_app' subst f l
      end
    | _ -> aux_app' subst f l
  and aux_app' subst f l =
    let f' = aux subst f in (* now, evaluate body *)
    A.app f' l
  in
  aux empty_subst t

(* check model *)
let check (m:t) ~goals =
  let bad =
    goals
    |> CCList.find_map
      (fun t ->
         let t' = eval m t in
         match A.term_view t' with
           | A.True -> None
           | _ -> Some (t, t'))
  in
  match bad with
    | None -> ()
    | Some (t,t') -> raise (Bad_model (m, t, t'))
