
(* This file is free software. See file "license" for more details. *)

(** {1 Trivial AST for parsing} *)

module Loc = Tip_loc

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
  | Let of var * term * term
  | If of term * term * term
  | Fun of typed_var * term
  | Mu of typed_var * term
  | Eq of term * term
  | Imply of term * term
  | And of term list
  | Or of term list
  | Not of term

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
  | Stmt_data of (string * (string * ty list) list) list
  | Stmt_assert of term
  | Stmt_goal of typed_var list * term (* satisfy this *)

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
let let_ v t u = Let (v,t,u)
let if_ a b c = If(a,b,c)
let fun_ v t = Fun (v,t)
let fun_l = List.fold_right fun_
let eq a b = Eq (a,b)
let imply a b = Imply(a,b)
let and_ l = And l
let or_ l = Or l
let not_ t = Not t

let _mk ?loc stmt = { loc; stmt }

let include_ ?loc s = _mk ?loc (Stmt_include s)
let ty_decl ?loc s = _mk ?loc (Stmt_ty_decl s)
let decl ?loc f ty = _mk ?loc (Stmt_decl (f, ty))
let def ?loc l = _mk ?loc (Stmt_def l)
let data ?loc l = _mk ?loc (Stmt_data l)
let assert_ ?loc t = _mk ?loc (Stmt_assert t)
let goal ?loc vars t = _mk ?loc (Stmt_goal (vars, t))

let loc t = t.loc
let view t = t.stmt

let fpf = Format.fprintf

let rec pp_ty out (ty:ty) = match ty with
  | Ty_bool -> CCFormat.string out "prop"
  | Ty_const s -> CCFormat.string out s
  | Ty_arrow (args,ret) ->
    fpf out "(@[->@ %a@ %a@])" (Utils.pp_list pp_ty) args pp_ty ret

let rec pp_term out (t:term) = match t with
  | True -> CCFormat.string out "true"
  | False -> CCFormat.string out "false"
  | Const s -> CCFormat.string out s
  | App (f,l) -> fpf out "(@[<1>%a@ %a@])" pp_term f (Utils.pp_list pp_term) l
  | Match (lhs,cases) ->
    let pp_case out = function
      | Match_default rhs -> fpf out "(@[<2>case default@ %a@])" pp_term rhs
      | Match_case (c,[],rhs) ->
        fpf out "(@[<2>case %s@ %a@])" c pp_term rhs
      | Match_case (c,vars,rhs) ->
        fpf out "(@[<2>case@ (@[%s@ %a@])@ %a@])"
          c (Utils.pp_list CCFormat.string) vars pp_term rhs
    in
    fpf out "(@[<1>match %a@ (@[<hv>%a@])@])" pp_term lhs
      (Utils.pp_list pp_case) cases
  | Let (v,t,u) -> fpf out "(@[<hv1>let %s@ %a@ %a@])" v pp_term t pp_term u
  | If (a,b,c) -> fpf out "(@[<hv1>if %a@ %a@ %a@])" pp_term a pp_term b pp_term c
  | Fun (v,body) -> fpf out "(@[<1>fun@ (%a)@ %a@])" pp_typed_var v pp_term body
  | Mu (v,body) -> fpf out "(@[<1>fun@ (%a)@ %a@])" pp_typed_var v pp_term body
  | Eq (a,b) -> fpf out "(@[=@ %a@ %a@])" pp_term a pp_term b
  | Imply (a,b) -> fpf out "(@[=>@ %a@ %a@])" pp_term a pp_term b
  | And l -> fpf out "(@[<hv>and@ %a@])" (Utils.pp_list pp_term) l
  | Or l -> fpf out "(@[<hv>or@ %a@])" (Utils.pp_list pp_term) l
  | Not t -> fpf out "(not %a)" pp_term t
and pp_typed_var out (v,ty) =
  fpf out "(@[%s@ %a@])" v pp_ty ty

let pp_stmt out (st:statement) = match view st with
  | Stmt_include s -> fpf out "(include %S)" s
  | Stmt_assert t -> fpf out "(@[assert@ %a@])" pp_term t
  | Stmt_goal (vars,t) ->
    fpf out "(@[goal@ (@[%a@])@ %a@])" (Utils.pp_list pp_typed_var) vars pp_term t
  | Stmt_ty_decl s ->
    fpf out "(@[ty-decl@ %s@])" s
  | Stmt_decl (s, ty) ->
    fpf out "(@[decl@ %s@ %a@])" s pp_ty ty
  | Stmt_def l ->
    let pp_def out (s,ty,rhs) =
      fpf out "(@[<1>%s@ %a@ %a@])" s pp_ty ty pp_term rhs
    in
    fpf out "(@[<hv1>define@ %a@])" (Utils.pp_list pp_def) l
  | Stmt_data l ->
    let pp_cstor out (s,ty_args) =
      if ty_args=[] then CCFormat.string out s
      else fpf out "(@[<1>%s@ %a@])" s (Utils.pp_list pp_ty) ty_args
    in
    let pp_data out (s,cstors) =
      fpf out "(@[<hv1>%s@ (@[<v>%a@]@])" s (Utils.pp_list pp_cstor) cstors
    in
    fpf out "(@[<hv>data@ @[<v>%a@]@])" (Utils.pp_list pp_data) l

(** {2 Conversion from {!Tip_ast}} *)

exception Tip_error of Loc.t option * string

let tip_error ?loc msg = raise (Tip_error (loc, msg))
let tip_errorf ?loc msg = CCFormat.ksprintf msg ~f:(tip_error ?loc)

module Tip = struct
  module A = Tip_ast

  let rec conv_ty (ty:A.ty): ty = match ty with
    | A.Ty_bool -> ty_prop
    | A.Ty_app (a, []) -> ty_const a
    | A.Ty_app (_, _::_) ->
      tip_errorf "cannot convert polymorphic type@ `@[%@]`" A.pp_ty ty
    | A.Ty_arrow (args, ret) ->
      ty_arrow_l (List.map conv_ty args) (conv_ty ret)

  let conv_typed_var (v,ty) = v, conv_ty ty

  let conv_term (t:A.term): term =
    let rec aux t = match t with
      | A.True -> true_
      | A.False -> false_
      | A.Const s -> const s
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
      | A.Fun (vars,body) -> fun_ (conv_typed_var vars) (aux body)
      | A.Or l -> or_ (List.map aux l)
      | A.And l -> and_ (List.map aux l)
      | A.Imply (a,b) -> imply (aux a) (aux b)
      | A.Eq (a,b) -> eq (aux a) (aux b)
      | A.Not a -> not_ (aux a)
      | A.Let (l, rhs) ->
        List.fold_right
          (fun (v,t) rhs -> let_ v (aux t) rhs)
          l (aux rhs)
    in
    aux t

  (* convert this function *)
  let conv_fun ?loc f body =
    if f.A.fun_ty_vars <> []
    then tip_errorf ?loc "cannot convert polymorphic function@ %a" A.pp_fun_decl f;
    let args = List.map conv_typed_var f.A.fun_args in
    let ty =
      ty_arrow_l
        (List.map snd args)
        (conv_ty f.A.fun_ret)
    in
    f.A.fun_name, ty, fun_l args (conv_term body)

  let conv_stmt (st:A.statement): statement option =
    let loc = A.loc st in
    match A.view st with
      | A.Stmt_decl_sort (s, 0) ->
        ty_decl ?loc s |> CCOpt.return
      | A.Stmt_decl_sort (_, _) ->
        tip_errorf ?loc "cannot handle polymorphic type@ %a" A.pp_stmt st
      | A.Stmt_decl (s, ty) ->
        decl ?loc s (conv_ty ty) |> CCOpt.return
      | A.Stmt_assert t ->
        assert_ ?loc (conv_term t) |> CCOpt.return
      | A.Stmt_data ([], l) ->
        let conv_data (s, cstors) =
          let cstors =
            List.map
              (fun c ->
                 c.A.cstor_name, List.map (fun (_,ty) -> conv_ty ty) c.A.cstor_args)
              cstors
          in
          s, cstors
        in
        let l = List.map conv_data l in
        data ?loc l |> CCOpt.return
      | A.Stmt_data (_::_, _) ->
        tip_errorf ?loc "cannot convert polymorphic data@ `@[%a@]`" A.pp_stmt st
      | A.Stmt_fun_rec f ->
        let id, ty, t = conv_fun ?loc f.A.fr_decl f.A.fr_body in
        def ?loc [id, ty, t] |> CCOpt.return
      | A.Stmt_funs_rec fsr ->
        let {A.fsr_decls=decls; fsr_bodies=bodies} = fsr in
        if List.length decls <> List.length bodies
        then tip_errorf ?loc "declarations and bodies should have same length";
        let l = List.map2 (conv_fun ?loc) decls bodies in
        def ?loc l |> CCOpt.return
      | A.Stmt_assert_not ([], vars, t) ->
        let vars = List.map conv_typed_var vars in
        let g = not_ (conv_term t) in (* negate *)
        goal ?loc vars g |> CCOpt.return
      | A.Stmt_assert_not (_::_, _, _) ->
        tip_errorf ?loc "cannot convert polymorphic goal@ `@[%a@]`"
          A.pp_stmt st
      | A.Stmt_check_sat -> None

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
