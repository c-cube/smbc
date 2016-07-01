
(* This file is free software. See file "license" for more details. *)

(** {1 Preprocessing AST} *)

type 'a or_error = ('a, string) CCResult.t
type sexp = CCSexp.t
type 'a to_sexp = 'a -> sexp

module S = CCSexp

let (<?>) = CCOrd.(<?>)

(** {2 Types} *)

module Var = struct
  type 'ty t = {
    id: ID.t;
    ty: 'ty;
  }

  let make id ty = {id;ty}
  let copy {id;ty} = {ty; id=ID.copy id}
  let ty v = v.ty

  let equal a b = ID.equal a.id b.id
  let pp out v = ID.pp out v.id
  let to_sexp f v = S.of_list [ID.to_sexp v.id; f v.ty]
end

module Ty = struct
  type t =
    | Prop
    | Const of ID.t
    | Arrow of t * t

  let prop = Prop
  let const id = Const id
  let arrow a b = Arrow (a,b)
  let arrow_l = List.fold_right arrow

  let rec to_sexp = function
    | Prop -> S.atom "prop"
    | Const id -> S.atom (ID.to_string id)
    | Arrow (a,b) -> S.of_list [S.atom "->"; to_sexp a; to_sexp b]

  let pp out t = CCSexpM.print out (to_sexp t)

  let to_int_ = function
    | Prop -> 0
    | Const _ -> 1
    | Arrow _ -> 2

  let rec compare a b = match a, b with
    | Prop, Prop -> 0
    | Const a, Const b -> ID.compare a b
    | Arrow (a1,a2), Arrow (b1,b2) ->
      compare a1 b1 <?> (compare, a2,b2)
    | Prop, _
    | Const _, _
    | Arrow _, _ -> CCOrd.int_ (to_int_ a) (to_int_ b)

  let equal a b = compare a b = 0
end

type var = Ty.t Var.t

type binop =
  | And
  | Or
  | Imply

type term = {
  term: term_cell;
  ty: Ty.t;
}
and term_cell =
  | Var of var
  | Const of ID.t
  | App of term * term list
  | If of term * term * term
  | Match of term * (var list * term) ID.Map.t
  | Fun of var * term
  | Eq of term * term
  | Not of term
  | Binop of binop * term * term
  | True
  | False

type data = {
  data_id: ID.t;
  data_cstors: Ty.t ID.Map.t;
}

type statement =
  | Data of data list
  | TyDecl of ID.t (* new atomic cstor *)
  | Decl of ID.t * Ty.t
  | Define of ID.t * term
  | Assert of term
  | Goal of var list * term

exception Ill_typed of string

let ill_typed fmt =
  CCFormat.ksprintf
    ~f:(fun s -> raise (Ill_typed s))
    fmt

let mk_ term ty = {term;ty}
let var v = mk_ (Var v) (Var.ty v)
let const id ty = mk_ (Const id) ty
let true_ = mk_ True Ty.prop
let false_ = mk_ False Ty.prop

(** {2 Printing} *)

let var_sexp_ v = ID.to_sexp v.Var.id
let typed_var_to_sexp = Var.to_sexp Ty.to_sexp

let rec term_to_sexp t = match t.term with
  | Var v -> var_sexp_ v
  | Const id -> ID.to_sexp id
  | App (f,l) -> S.of_list (term_to_sexp f :: List.map term_to_sexp l)
  | If (a,b,c) ->
    S.of_list [S.atom "if"; term_to_sexp a; term_to_sexp b; term_to_sexp c]
  | Match (t, m) ->
    (S.atom "match" :: term_to_sexp t ::
      (ID.Map.to_list m
       |> List.map
         (fun (c,(vars, rhs)) ->
            S.of_list
              [ S.of_list (ID.to_sexp c :: List.map var_sexp_ vars);
                term_to_sexp rhs])))
    |> S.of_list
  | Fun (v,t) -> S.of_list [S.atom "fun"; var_sexp_ v; term_to_sexp t]
  | Eq (a,b) -> S.of_list [S.atom "="; term_to_sexp a; term_to_sexp b]
  | Not t -> S.of_list [S.atom "not"; term_to_sexp t]
  | Binop (And, a, b) ->
    S.of_list [S.atom "and"; term_to_sexp a; term_to_sexp b]
  | Binop (Or, a, b) ->
    S.of_list [S.atom "or"; term_to_sexp a; term_to_sexp b]
  | Binop (Imply, a, b) ->
    S.of_list [S.atom "=>"; term_to_sexp a; term_to_sexp b]
  | True -> S.atom "true"
  | False -> S.atom "false"

let data_to_sexp d =
  let cstors =
    ID.Map.fold
      (fun c ty acc -> S.of_list [ID.to_sexp c; Ty.to_sexp ty] :: acc)
      d.data_cstors []
  in
  S.of_list (ID.to_sexp d.data_id :: cstors)

let statement_to_sexp st = match st with
  | Data l ->
    S.of_list
      [ S.atom "data";
        S.of_list (List.map data_to_sexp l)]
  | TyDecl id ->
    S.of_list [S.atom "type"; ID.to_sexp id]
  | Decl (id,ty) ->
    S.of_list [S.atom "decl"; ID.to_sexp id; Ty.to_sexp ty]
  | Define (id,t) ->
    S.of_list [S.atom "define"; ID.to_sexp id; term_to_sexp t]
  | Assert t ->
    S.of_list [S.atom "assert"; term_to_sexp t]
  | Goal (vars,t) ->
    S.of_list
      [S.atom "goal";
       S.of_list (List.map typed_var_to_sexp vars);
       term_to_sexp t]

let pp_term out t = CCSexpM.print out (term_to_sexp t)
let pp_statement out t = CCSexpM.print out (statement_to_sexp t)

(** {2 Constructors} *)

let rec app_ty_ ty l : Ty.t = match ty, l with
  | _, [] -> ty
  | Ty.Arrow (ty_a,ty_rest), a::tail ->
    if Ty.equal ty_a a.ty
    then app_ty_ ty_rest tail
    else ill_typed "expected `@[%a@]`,@ got `@[%a : %a@]`"
        Ty.pp ty_a pp_term a Ty.pp a.ty
  | (Ty.Prop | Ty.Const _), a::_ ->
    ill_typed "cannot apply ty `@[%a@]`@ to `@[%a@]`" Ty.pp ty pp_term a

let mk_ term ty = {term; ty}

let var v = mk_ (Var v) (Var.ty v)

let const id ty = mk_ (Const id) ty

let app f l = match f.term, l with
  | _, [] -> f
  | App (f1, l1), _ ->
    let ty = app_ty_ f.ty l in
    mk_ (App (f1, l1 @ l)) ty
  | _ ->
    let ty = app_ty_ f.ty l in
    mk_ (App (f, l)) ty

let if_ a b c =
  if a.ty <> Ty.Prop
  then ill_typed "if: test  must have type prop, not `@[%a@]`" Ty.pp a.ty;
  if not (Ty.equal b.ty c.ty)
  then ill_typed
      "if: both branches must have same type,@ not `@[%a@]` and `@[%a@]`"
      Ty.pp b.ty Ty.pp c.ty;
  mk_ (If (a,b,c)) b.ty

(* TODO: check types *)
let match_ t m =
  let _, (_, rhs) = ID.Map.choose m in
  mk_ (Match (t,m)) rhs.ty

let fun_ v t =
  let ty = Ty.arrow (Var.ty v) t.ty in
  mk_ (Fun (v,t)) ty

let fun_l = List.fold_right fun_

let eq a b =
  if not (Ty.equal a.ty b.ty)
  then ill_typed "eq: `@[%a@]` and `@[%a@]` do not have the same type"
      pp_term a pp_term b;
  mk_ (Eq (a,b)) Ty.prop

let check_prop_ t =
  if not (Ty.equal t.ty Ty.prop)
  then ill_typed "expected prop, got `@[%a : %a@]`" pp_term t Ty.pp t.ty

let binop op a b =
  check_prop_ a; check_prop_ b;
  mk_ (Binop (op, a, b))

let and_ = binop And
let or_ = binop Or
let imply = binop Imply

(** {2 Parsing} *)

module StrMap = CCMap.Make(String)

exception Error of string

let errorf msg = CCFormat.ksprintf ~f:(fun e -> raise (Error e)) msg

module Ctx = struct
  type kind =
    | Ty
    | Data of data
    | Fun of Ty.t
    | Cstor of Ty.t * data

  type t = {
    names: ID.t StrMap.t;
    kinds: kind ID.Map.t;
  }

  let empty : t = {
    names=StrMap.empty;
    kinds=ID.Map.empty;
  }

  let add_kind t (id:ID.t) (k:kind) : t =
    if ID.Map.mem id t.kinds
    then errorf "ID `%a` already declared" ID.pp id;
    { t with kinds=ID.Map.add id k t.kinds }

  let add_id t (s:string): t * ID.t =
    let id = ID.make s in
    {t with names=StrMap.add s id t.names}, id

  let find_kind t (id:ID.t) : kind =
    try ID.Map.find id t.kinds
    with Not_found -> errorf "did not find kind of ID `%a`" ID.pp id

  let pp_kind out = function
    | Ty -> Format.fprintf out "type"
    | Cstor d ->
      Format.fprintf out "(@[cstor %a@])" CCSexpM.print (data_to_sexp d)
    | Data d ->
      Format.fprintf out "(@[data %a@])" CCSexpM.print (data_to_sexp d)
    | Fun ty ->
      Format.fprintf out "(@[fun %a@])" Ty.pp ty
end

let find_id_ ctx (s:string): ID.t =
  try StrMap.find s ctx.Ctx.names
  with Not_found -> errorf "name `%s` not in scope" s

let rec conv_ty ctx s = match s with
  | `Atom "prop" -> Ty.prop
  | `Atom s -> let id = find_id_ ctx s in Ty.const id
  | `List [`Atom "->"; a; b] ->
    let a = conv_ty ctx a in
    let b = conv_ty ctx b in
    Ty.arrow a b
  | _ -> errorf "expected type, got `@[%a@]`" CCSexpM.print s

let rec conv_term ctx s = match s with
  | `Atom "true" -> true_
  | `Atom "false" -> false_
  | `Atom s ->
    let id = find_id_ ctx s in
    let ty = match Ctx.find_kind ctx id with
      | Ctx.Fun ty
      | Ctx.Cstor (ty,_) -> ty
      | Ctx.Ty
      | Ctx.Data _ -> errorf "expected term, not type; got `%a`" ID.pp id
    in
    const id ty
  | `List [`Atom "if"; a; b; c] ->
    let a = conv_term ctx a in
    let b = conv_term ctx b in
    let c = conv_term ctx c in
    if_ a b c
  (* TODO: other cases, including match *)
  | _ -> errorf "expected term, got `@[%a@]`" CCSexpM.print s

let conv_statement ctx s = match s with
  | `List [`Atom "decl"; `Atom s; ty] ->
    let ty = conv_ty ctx ty in
    let ctx, id = Ctx.add_id ctx s in
    let ctx = Ctx.add_kind ctx id (Ctx.Fun ty) in
    ctx, Decl (id,ty)
  | _ -> errorf "expected statement,@ got `@[%a@]`" CCSexpM.print s

let term_of_sexp ctx s =
  try conv_term ctx s |> CCResult.return
  with e -> CCResult.of_exn_trace e

let statement_of_sexp ctx s =
  try conv_statement ctx s |> CCResult.return
  with e -> CCResult.of_exn_trace e


let statements_of_sexps ?(init=Ctx.empty) l =
  try
    CCList.fold_map conv_statement init l
    |> CCResult.return
  with e ->
    CCResult.of_exn_trace e

