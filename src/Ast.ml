
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
  let print out v = ID.print out v.id
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

  let print out t = CCSexpM.print out (to_sexp t)

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

type data = {
  data_id: ID.t;
  data_cstors: Ty.t ID.Map.t;
}

type statement =
  | Data of data list
  | Define of ID.t * term
  | Assert of term
  | Goal of var list * term

exception Ill_typed of string

let ill_typed fmt =
  CCFormat.ksprintf
    ~f:(fun s -> raise (Ill_typed s))
    fmt


(** {2 Printing} *)

let var_sexp_ v = ID.to_sexp v.Var.id

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

let statement_to_sexp = assert false

let print_term out t = CCSexpM.print out (term_to_sexp t)
let print_statement out t = CCSexpM.print out (statement_to_sexp t)

(** {2 Constructors} *)

let rec app_ty_ ty l : Ty.t = match ty, l with
  | _, [] -> ty
  | Ty.Arrow (ty_a,ty_rest), a::tail ->
    if Ty.equal ty_a a.ty
    then app_ty_ ty_rest tail
    else ill_typed "expected `@[%a@]`,@ got `@[%a : %a@]`"
        Ty.print ty_a print_term a Ty.print a.ty
  | (Ty.Prop | Ty.Const _), a::_ ->
    ill_typed "cannot apply ty `@[%a@]`@ to `@[%a@]`" Ty.print ty print_term a

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
  then ill_typed "if: test  must have type prop, not `@[%a@]`" Ty.print a.ty;
  if not (Ty.equal b.ty c.ty)
  then ill_typed "if: both branches must have same type,@ not `@[%a@]` and `@[%a@]`"
      Ty.print b.ty Ty.print c.ty;
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
      print_term a print_term b;
  mk_ (Eq (a,b)) Ty.prop

let check_prop_ t =
  if not (Ty.equal t.ty Ty.prop)
  then ill_typed "expected prop, got `@[%a : %a@]`" print_term t Ty.print t.ty

let binop op a b =
  check_prop_ a; check_prop_ b;
  mk_ (Binop (op, a, b))

let and_ = binop And
let or_ = binop Or
let imply = binop Imply

(** {2 Parsing} *)

val term_of_sexp : sexp -> term or_error
val statement_of_sexp : sexp -> statement or_error
