
(* This file is free software. See file "license" for more details. *)

(** {1 Preprocessing AST} *)

type 'a or_error = ('a, string) CCResult.t
type sexp = CCSexp.t
type 'a to_sexp = 'a -> sexp

(** {2 Types} *)

module Var : sig
  type 'ty t = private {
    id: ID.t;
    ty: 'ty;
  }

  val make : ID.t -> 'ty -> 'ty t
  val copy : 'a t -> 'a t
  val ty : 'a t -> 'a

  val equal : 'a t -> 'a t -> bool
  val pp : _ t CCFormat.printer
  val to_sexp : 'ty to_sexp -> 'ty t to_sexp
end

type var = Ty.t Var.t

type binop =
  | And
  | Or
  | Imply

type term = private {
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

(* TODO: records? *)

type statement =
  | Data of Ty.data list
  | TyDecl of ID.t (* new atomic cstor *)
  | Decl of ID.t * Ty.t
  | Define of ID.t * term
  | Assert of term
  | Goal of var list * term

(** {2 Constructors} *)

val var : var -> term
val const : ID.t -> Ty.t -> term
val app : term -> term list -> term
val if_ : term -> term -> term -> term
val match_ : term -> (var list * term) ID.Map.t -> term
val fun_ : var -> term -> term
val fun_l : var list -> term -> term
val eq : term -> term -> term
val not_ : term -> term
val binop : binop -> term -> term -> term
val and_ : term -> term -> term
val or_ : term -> term -> term
val imply : term -> term -> term
val true_ : term
val false_ : term

(** {2 Printing} *)

val term_to_sexp : term to_sexp
val statement_to_sexp : statement to_sexp

val pp_term : term CCFormat.printer
val pp_statement : statement CCFormat.printer

(** {2 Parsing and Typing} *)

module Ctx : sig
  type t
  val empty : t
  include Intf.PRINT with type t := t
end

val term_of_sexp : Ctx.t -> sexp -> term or_error

val statement_of_sexp : Ctx.t -> sexp -> (Ctx.t * statement) or_error

val statements_of_sexps :
  ?init:Ctx.t -> sexp list -> (Ctx.t * statement list) or_error

