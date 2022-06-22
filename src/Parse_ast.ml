(* This file is free software. See file "license" for more details. *)

(** {1 Trivial AST for parsing} *)

open Common_

module A = Smtlib_utils.V_2_6.Ast
module Loc = Smtlib_utils.V_2_6.Loc


type var = string

type ty =
  | Ty_bool
  | Ty_const of string
  | Ty_arrow of ty list * ty

type typed_var = var * ty

(** {2 AST: S-expressions with locations} *)
type term =
  | True
  | False
  | Const of string
  | App of term * term list
  | Match of term * match_branch list
  | Is_a of string * term
  | Let of var * term * term
  | If of term * term * term
  | Fun of typed_var * term
  | Mu of typed_var * term
  | Eq of term * term
  | Imply of term * term
  | And of term list
  | Or of term list
  | Not of term
  | Forall of typed_var * term
  | Exists of typed_var * term
  | Asserting of term * term (* [t asserting g] *)

and match_branch =
  | Match_case of string * var list * term
  | Match_default of term

type statement = {
  stmt: stmt;
  loc: Loc.t option;
}

and stmt =
  | Stmt_include of string
  | Stmt_ty_decl of string
  | Stmt_decl of string * ty
  | Stmt_def of (string * ty * term) list
  | Stmt_data of (string * (string * (string option * ty) list) list) list
  | Stmt_assert of term
  | Stmt_goal of {
      prove: bool;
      vars: typed_var list;
      body: term;
    } (* satisfy/prove this *)

let ty_prop = Ty_bool
let ty_const s = Ty_const s
let ty_arrow_l args ret = if args=[] then ret else Ty_arrow (args, ret)
let ty_arrow a b = ty_arrow_l [a] b

let true_ = True
let false_ = False
let const s = Const s
let app f l = match f, l with
  | _, [] -> f
  | App (f1, l1), _ -> App (f1, l1 @ l)
  | _ -> App (f, l)
let match_ u l = Match (u,l)
let is_a c t = Is_a(c,t)
let let_ v t u = Let (v,t,u)
let if_ a b c = If(a,b,c)
let fun_ v t = Fun (v,t)
let fun_l = List.fold_right fun_
let eq a b = Eq (a,b)
let imply a b = Imply(a,b)
let and_ l = And l
let or_ l = Or l
let not_ t = Not t
let forall x t = Forall (x,t)
let exists x t = Exists (x,t)
let forall_l = List.fold_right forall
let exists_l = List.fold_right exists
let asserting t g = Asserting(t,g)

let _mk ?loc stmt = { loc; stmt }

let include_ ?loc s = _mk ?loc (Stmt_include s)
let ty_decl ?loc s = _mk ?loc (Stmt_ty_decl s)
let decl ?loc f ty = _mk ?loc (Stmt_decl (f, ty))
let def ?loc l = _mk ?loc (Stmt_def l)
let data ?loc l = _mk ?loc (Stmt_data l)
let assert_ ?loc t = _mk ?loc (Stmt_assert t)
let goal ?loc ~prove vars t = _mk ?loc (Stmt_goal {prove;vars;body=t})

let loc t = t.loc
let view t = t.stmt

let fpf = Format.fprintf

let rec pp_ty out (ty:ty) = match ty with
  | Ty_bool -> CCFormat.string out "prop"
  | Ty_const s -> CCFormat.string out s
  | Ty_arrow (args,ret) ->
    fpf out "(@[=>@ %a@ %a@])" (Util.pp_list pp_ty) args pp_ty ret

let rec pp_term out (t:term) = match t with
  | True -> CCFormat.string out "true"
  | False -> CCFormat.string out "false"
  | Const s -> CCFormat.string out s
  | App (f,l) -> fpf out "(@[<1>%a@ %a@])" pp_term f (Util.pp_list pp_term) l
  | Match (lhs,cases) ->
    let pp_case out = function
      | Match_default rhs -> fpf out "(@[<2>case default@ %a@])" pp_term rhs
      | Match_case (c,[],rhs) ->
        fpf out "(@[<2>case %s@ %a@])" c pp_term rhs
      | Match_case (c,vars,rhs) ->
        fpf out "(@[<2>case@ (@[%s@ %a@])@ %a@])"
          c (Util.pp_list CCFormat.string) vars pp_term rhs
    in
    fpf out "(@[<1>match %a@ (@[<hv>%a@])@])" pp_term lhs
      (Util.pp_list pp_case) cases
  | Is_a(c,t) -> fpf out "(@[is-%s@ %a@])" c pp_term t
  | Let (v,t,u) -> fpf out "(@[<hv1>let %s@ %a@ %a@])" v pp_term t pp_term u
  | If (a,b,c) -> fpf out "(@[<hv1>ite %a@ %a@ %a@])" pp_term a pp_term b pp_term c
  | Fun (v,body) -> fpf out "(@[<1>lambda@ (%a)@ %a@])" pp_typed_var v pp_term body
  | Forall (v,body) -> fpf out "(@[<1>forall@ (%a)@ %a@])" pp_typed_var v pp_term body
  | Exists (v,body) -> fpf out "(@[<1>exists@ (%a)@ %a@])" pp_typed_var v pp_term body
  | Mu (v,body) -> fpf out "(@[<1>mu@ (%a)@ %a@])" pp_typed_var v pp_term body
  | Eq (a,b) -> fpf out "(@[=@ %a@ %a@])" pp_term a pp_term b
  | Imply (a,b) -> fpf out "(@[=>@ %a@ %a@])" pp_term a pp_term b
  | And l -> fpf out "(@[<hv>and@ %a@])" (Util.pp_list pp_term) l
  | Or l -> fpf out "(@[<hv>or@ %a@])" (Util.pp_list pp_term) l
  | Not t -> fpf out "(not %a)" pp_term t
  | Asserting (t,g) -> fpf out "(@[:asserting@ %a@ %a@])" pp_term t pp_term g
and pp_typed_var out (v,ty) =
  fpf out "(@[%s@ %a@])" v pp_ty ty

let pp_stmt out (st:statement) = match view st with
  | Stmt_include s -> fpf out "(include %S)" s
  | Stmt_assert t -> fpf out "(@[assert@ %a@])" pp_term t
  | Stmt_goal {prove;vars;body=t} ->
    fpf out "(@[goal@ :prove %B (@[%a@])@ %a@])"
      prove (Util.pp_list pp_typed_var) vars pp_term t
  | Stmt_ty_decl s ->
    fpf out "(@[declare-sort@ %s 0@])" s
  | Stmt_decl (s, ty) ->
    fpf out "(@[declare-const@ %s@ %a@])" s pp_ty ty
  | Stmt_def l ->
    let pp_def out (s,ty,rhs) =
      fpf out "(@[<1>%s@ %a@ %a@])" s pp_ty ty pp_term rhs
    in
    fpf out "(@[<hv1>define@ %a@])" (Util.pp_list pp_def) l
  | Stmt_data l ->
    let pp_arg out (name_opt,ty) = match name_opt with
      | None -> pp_ty out ty
      | Some n -> fpf out "(%s:%a)" n pp_ty ty
    in
    let pp_cstor out (s,ty_args) =
      if ty_args=[] then CCFormat.string out s
      else fpf out "(@[<1>%s@ %a@])" s (Util.pp_list pp_arg) ty_args
    in
    let pp_data out (s,cstors) =
      fpf out "(@[<hv1>%s@ (@[<v>%a@]@])" s (Util.pp_list pp_cstor) cstors
    in
    fpf out "(@[<hv>data@ @[<v>%a@]@])" (Util.pp_list pp_data) l

(** {2 Conversion from {!Tip_ast}} *)

exception Tip_error of Loc.t option * string

let tip_error ?loc msg = raise (Tip_error (loc, msg))
let tip_errorf ?loc msg = CCFormat.ksprintf msg ~f:(tip_error ?loc)

module Tip = struct

  let rec conv_ty (ty:A.ty): ty = match ty with
    | A.Ty_bool -> ty_prop
    | A.Ty_app (a, []) -> ty_const a
    | A.Ty_app (_, _::_) ->
      tip_errorf "cannot convert polymorphic type@ `@[%a@]`" A.pp_ty ty
    | A.Ty_arrow (args, ret) ->
      ty_arrow_l (List.map conv_ty args) (conv_ty ret)
    | A.Ty_real ->
      tip_errorf "cannot handle Real`"

  let conv_typed_var (v,ty) = v, conv_ty ty
  let conv_typed_vars = List.map conv_typed_var

  let conv_term (t:A.term): term =
    let rec aux t = match t with
      | A.True -> true_
      | A.False -> false_
      | A.Const s -> const s
      | A.App ((":asserting" | "asserting"), [t;g]) ->
        asserting (aux t) (aux g)
      | A.Arith _ ->
          tip_errorf "cannot handle arithmetic expression"
      | A.Attr (t, _) -> aux t
      | A.App (f, l) ->
        app (aux (A.Const f)) (List.map aux l)
      | A.HO_app (a,b) -> app (aux a) [aux b]
      | A.Cast (t, _) -> aux t
      | A.If (a,b,c) -> if_ (aux a) (aux b) (aux c)
      | A.Match (lhs,l) ->
        let l =
          List.map
            (function
              | A.Match_default rhs -> Match_default (aux rhs)
              | A.Match_case (c,vars,rhs) -> Match_case (c,vars,aux rhs))
            l
        in
        match_ (aux lhs) l
      | A.Is_a (c,t) ->
        let t = aux t in
        is_a c t
      | A.Fun (vars,body) -> fun_ (conv_typed_var vars) (aux body)
      | A.Or l -> or_ (List.map aux l)
      | A.And l -> and_ (List.map aux l)
      | A.Imply (a,b) -> imply (aux a) (aux b)
      | A.Eq (a,b) -> eq (aux a) (aux b)
      | A.Distinct ([] | [_]) ->
        tip_error "`distinct` should have at least 2 arguments"
      | A.Distinct l ->
        (* encode [distinct t1...tn] into [And_{i,j<i} ti!=tj] *)
        List.map aux l
        |> CCList.diagonal
        |> List.map (fun (a,b) -> not_ (eq a b))
        |> and_
      | A.Not a -> not_ (aux a)
      | A.Let (l, rhs) ->
        List.fold_right
          (fun (v,t) rhs -> let_ v (aux t) rhs)
          l (aux rhs)
      | A.Forall (vars,body) -> forall_l (conv_typed_vars vars) (aux body)
      | A.Exists (vars,body) -> exists_l (conv_typed_vars vars) (aux body)
    in
    aux t

  let conv_fun_decl ?loc f =
    if f.A.fun_ty_vars <> []
    then tip_errorf ?loc "cannot convert polymorphic function@ %a"
        (A.pp_fun_decl A.pp_ty) f;
    let args = List.map conv_ty f.A.fun_args in
    let ty = ty_arrow_l args (conv_ty f.A.fun_ret) in
    f.A.fun_name, ty

  let conv_fun_def ?loc f body =
    if f.A.fun_ty_vars <> []
    then tip_errorf ?loc "cannot convert polymorphic function@ %a"
        (A.pp_fun_decl A.pp_typed_var) f;
    let args = List.map conv_typed_var f.A.fun_args in
    let ty =
      ty_arrow_l
        (List.map snd args)
        (conv_ty f.A.fun_ret)
    in
    f.A.fun_name, ty, fun_l args (conv_term body)

  let rec open_forall (t:term): typed_var list * term = match t with
    | Forall (v, t') ->
      let vars, body = open_forall t' in
      v :: vars, body
    | _ -> [], t

  let conv_stmt (st:A.statement): statement option =
    let loc = A.loc st in
    match A.view st with
      | A.Stmt_decl_sort (s, 0) ->
        ty_decl ?loc s |> Option.return
      | A.Stmt_decl_sort (_, _) ->
        tip_errorf ?loc "cannot handle polymorphic type@ %a" A.pp_stmt st
      | A.Stmt_decl fr ->
        let f, ty = conv_fun_decl ?loc fr in
        decl ?loc f ty |> Option.return
      | A.Stmt_assert t ->
        assert_ ?loc (conv_term t) |> Option.return
      | A.Stmt_data l ->
        let conv_data ((s,n), cstors) =
          if n<>0 then
            tip_errorf ?loc "cannot convert polymorphic data@ `@[%a@]`" A.pp_stmt st;
          let cstors =
            List.map
              (fun c ->
                 c.A.cstor_name,
                 List.map
                   (fun (select,ty) -> Some select,conv_ty ty)
                   c.A.cstor_args)
              cstors
          in
          s, cstors
        in
        let l = List.map conv_data l in
        data ?loc l |> Option.return
      | A.Stmt_fun_def f
      | A.Stmt_fun_rec f ->
        let id, ty, t = conv_fun_def ?loc f.A.fr_decl f.A.fr_body in
        def ?loc [id, ty, t] |> Option.return
      | A.Stmt_funs_rec fsr ->
        let {A.fsr_decls=decls; fsr_bodies=bodies} = fsr in
        if List.length decls <> List.length bodies
        then tip_errorf ?loc "declarations and bodies should have same length";
        let l = List.map2 (conv_fun_def ?loc) decls bodies in
        def ?loc l |> Option.return
      | A.Stmt_set_info _ | A.Stmt_set_logic _ | A.Stmt_check_sat | A.Stmt_exit
      | A.Stmt_get_option _ | A.Stmt_get_info _| A.Stmt_get_value _|
      A.Stmt_check_sat_assuming _|A.Stmt_pop _| A.Stmt_push _ |
      A.Stmt_get_unsat_assumptions | A.Stmt_get_unsat_core | A.Stmt_reset |
      A.Stmt_set_option _ | A.Stmt_reset_assertions | A.Stmt_get_proof |
      A.Stmt_get_model |A.Stmt_get_assignment |A.Stmt_get_assertions
        -> None
end

(** {2 Errors} *)

exception Parse_error of Loc.t option * string

let parse_error ?loc msg = raise (Parse_error (loc, msg))
let parse_errorf ?loc msg = Format.ksprintf (parse_error ?loc) msg

(** printing exceptions *)

let () = Printexc.register_printer
    (function
      | Parse_error (loc, msg) ->
        Some (CCFormat.sprintf "parse error at %a:@ %s" Loc.pp_opt loc msg)
      | Tip_error (loc, msg) ->
        Some (CCFormat.sprintf "TIP conversion error at %a:@ %s" Loc.pp_opt loc msg)
      | _ -> None)
