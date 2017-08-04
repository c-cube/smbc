
(* This file is free software. See file "license" for more details. *)

(** {1 Basic AST for rewriting} *)

module Fmt = CCFormat

type var = Ty.t Var.t

type unop = U_not
type binop = B_eq | B_leq | B_lt | B_and | B_or | B_imply

type term = {
  view: term_view;
  ty: Ty.t;
}
and term_view =
  | Var of var (* bound var, for rules *)
  | Const of cst
  | Unknown of var (* meta-variable *)
  | App of term * term list
  | Bool of bool
  | If of term * term * term
  | Unop of unop * term
  | Binop of binop * term * term
  | Undefined of Ty.t

and cst = {
  cst_id : ID.t;
  cst_ty : Ty.t;
  cst_def : cst_def;
}

and cst_def =
  | Cst_def of rule list lazy_t
  | Cst_cstor of ID.t (* datatype *)

(* [cst args --> rhs] *)
and rule = term list * term

type statement =
  | St_data of Ty.data list (* declare mutual datatypes *)
  | St_def of cst list (* define constants *)
  | St_goal of term (* boolean term *)
  | St_in_model of var list (* unknowns that must be in model *)

module Cst = struct
  type t = cst
  let ty c = c.cst_ty
  let mk_ id ty d : t = {cst_id=id; cst_ty=ty; cst_def=d}
  let mk_def id ty rules : t = mk_ id ty (Cst_def rules)
  let mk_cstor id ty =
    let _, ret = Ty.unfold ty in
    let ty_id = match ret with Ty.Const id -> id | _ -> assert false in
    mk_ id ty (Cst_cstor ty_id)
  let pp out (c:t) = ID.pp out c.cst_id
end

let pp_binop out = function
  | B_eq -> Fmt.string out "="
  | B_leq -> Fmt.string out "<="
  | B_lt -> Fmt.string out "<"
  | B_and -> Fmt.string out "and"
  | B_or -> Fmt.string out "or"
  | B_imply -> Fmt.string out "=>"

module T = struct
  type t = term

  let view t = t.view
  let ty t = t.ty

  let mk_ view ty : t = { view; ty; }

  let rec pp out (t:t): unit = match view t with
    | Var v -> Var.pp out v
    | Const c -> Cst.pp out c
    | App (f, l) ->
      Format.fprintf out "(@[%a@ %a@])" pp f (Utils.pp_list pp) l
    | Unknown v -> Format.fprintf out "?%a" Var.pp v
    | Bool b -> Fmt.bool out b
    | Unop (U_not,t) -> Fmt.fprintf out "(@[<1>not@ %a@])" pp t
    | Binop (op,t,u) ->
      Fmt.fprintf out "(@[<hv1>%a@ %a@ %a@])" pp_binop op pp t pp u
    | If (a,b,c) ->
      Fmt.fprintf out "(@[<hv1>if@ %a@ %a@ %a@])" pp a pp b pp c
    | Undefined _ -> Fmt.string out "?__"

  let var v = mk_ (Var v) (Var.ty v)
  let const c = mk_ (Const c) (Cst.ty c)
  let unknown v = mk_ (Unknown v) (Var.ty v)

  let app f l =
    if l=[] then f else (
      (* compute ty *)
      let rec aux_ty ty_f l = match ty_f, l with
        | _, [] -> ty_f
        | Ty.Arrow (a, ty_f'), arg :: tail ->
          if Ty.equal a (ty arg) then aux_ty ty_f' tail
          else
            Ty.ill_typed
              "in `(@[%a@ %a@])`,@ expected `%a`,@ got `%a:%a`"
              pp f (Utils.pp_list pp) l Ty.pp a pp arg Ty.pp (ty arg)
        | _, arg :: _ ->
          Ty.ill_typed
            "in `(@[%a@ %a@])`,@ cannot apply term of type `%a`,@ to `%a:%a`"
              pp f (Utils.pp_list pp) l Ty.pp ty_f pp arg Ty.pp (ty arg)
      in
      let ty = aux_ty (ty f) l in
      mk_ (App (f,l)) ty
    )

  let app_cst c l = app (const c) l

  let bool b = mk_ (Bool b) Ty.prop
  let if_ a b c = mk_ (If (a,b,c)) (ty b)
  let unop o t = mk_ (Unop (o,t)) Ty.prop
  let binop o t u = mk_ (Binop (o,t,u)) Ty.prop
  let undefined ty = mk_ (Undefined ty) ty
end

let pp_rule out (r:rule) =
  let args, rhs = r in
  Fmt.fprintf out "(@[%a@ --> %a@])" (Utils.pp_list T.pp) args T.pp rhs

module Stmt = struct
  type t = statement

  let goal t : t = St_goal t

  let data l : t =
    assert (l<>[]);
    St_data l

  let def l : t =
    assert (l<>[]);
    St_def l

  let in_model l : t =
    assert (l<>[]);
    St_in_model l

  let pp out = function
    | St_data l ->
      let pp_data out (d:Ty.data) =
        Fmt.fprintf out "(@[<hv1>%a@ %a@])"
          ID.pp d.Ty.data_id
          (Utils.pp_list Fmt.(within "(" ")" @@ pair ~sep:(return "->@ ") ID.pp Ty.pp))
          (ID.Map.to_list d.Ty.data_cstors)
      in
      Fmt.fprintf out "(@[<hv1>data@ %a@])" (Utils.pp_list pp_data) l
    | St_def l ->
      let pp_c_full out c =
        let rules = match c.cst_def with
          | Cst_def (lazy l) -> l | Cst_cstor _ -> assert false
        in
        Fmt.fprintf out "(@[<1>%a : %a@ := (@[%a@])@])"
          Cst.pp c Ty.pp (Cst.ty c) (Utils.pp_list pp_rule) rules
      in
      Fmt.fprintf out "(@[<hv1>def@ %a@])" (Utils.pp_list pp_c_full) l
    | St_goal g -> Fmt.fprintf out "(@[<1>goal %a@])" T.pp g
    | St_in_model l -> Fmt.fprintf out "(@[<1>in_model@ %a@])" (Utils.pp_list Var.pp) l
end

module As_key = struct
  type t = var
  let compare = Var.compare
  let equal = Var.equal
  let hash = Var.hash
end

