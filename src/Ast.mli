
(* This file is free software. See file "license" for more details. *)

(** {1 Preprocessing AST} *)

type 'a or_error = ('a, string) CCResult.t
type sexp = CCSexp.t
type 'a to_sexp = 'a -> sexp

(** {2 Types} *)

exception Error of string
exception Ill_typed of string

module Var : sig
  type 'ty t = private {
    id: ID.t;
    ty: 'ty;
  }

  val make : ID.t -> 'ty -> 'ty t
  val copy : 'a t -> 'a t
  val id : _ t -> ID.t
  val ty : 'a t -> 'a

  val equal : 'a t -> 'a t -> bool
  val compare : 'a t -> 'a t -> int
  val pp : _ t CCFormat.printer
  val to_sexp : _ t to_sexp
  val to_sexp_typed : 'ty to_sexp -> 'ty t to_sexp
end

module Ty : sig
  type t =
    | Prop
    | Const of ID.t
    | Arrow of t * t

  val prop : t
  val const : ID.t -> t
  val arrow : t -> t -> t
  val arrow_l : t list -> t -> t

  include Intf.EQ with type t := t
  include Intf.ORD with type t := t
  include Intf.HASH with type t := t
  include Intf.PRINT with type t := t

  val unfold : t -> t list * t
  (** [unfold ty] will get the list of arguments, and the return type
      of any function. An atomic type is just a function with no arguments *)

  val to_sexp : t to_sexp

  (** {2 Datatypes} *)

  (** Mutually recursive datatypes *)
  type data = {
    data_id: ID.t;
    data_cstors: t ID.Map.t;
  }

  val data_to_sexp : data -> sexp

  module Map : CCMap.S with type key = t

  (** {2 Error Handling} *)

  val ill_typed : ('a, Format.formatter, unit, 'b) format4 -> 'a
end

type var = Ty.t Var.t

type binop =
  | And
  | Or
  | Imply
  | Eq

type term = private {
  term: term_cell;
  ty: Ty.t;
}
and term_cell =
  | Var of var
  | Const of ID.t
  | App of term * term list
  | If of term * term * term
  | Select of select * term
  | Match of term * (var list * term) ID.Map.t
  | Switch of term * term ID.Map.t (* switch on constants *)
  | Let of var * term * term
  | Fun of var * term
  | Forall of var * term
  | Exists of var * term
  | Mu of var * term
  | Not of term
  | Binop of binop * term * term
  | Asserting of term * term
  | True
  | False

and select = {
  select_name: ID.t lazy_t;
  select_cstor: ID.t;
  select_i: int;
}

(* TODO: records? *)

type definition = ID.t * Ty.t * term

type statement =
  | Data of Ty.data list
  | TyDecl of ID.t (* new atomic cstor *)
  | Decl of ID.t * Ty.t
  | Define of definition list
  | Assert of term
  | Goal of var list * term

(** {2 Constructors} *)

val term_view : term -> term_cell

val var : var -> term
val const : ID.t -> Ty.t -> term
val app : term -> term list -> term
val app_a : term -> term array -> term
val select : select -> term -> Ty.t -> term
val if_ : term -> term -> term -> term
val match_ : term -> (var list * term) ID.Map.t -> term
val switch : term -> term ID.Map.t -> term
val let_ : var -> term -> term -> term
val fun_ : var -> term -> term
val fun_l : var list -> term -> term
val fun_a : var array -> term -> term
val forall : var -> term -> term
val forall_l : var list -> term -> term
val exists : var -> term -> term
val exists_l : var list -> term -> term
val mu : var -> term -> term
val eq : term -> term -> term
val not_ : term -> term
val binop : binop -> term -> term -> term
val and_ : term -> term -> term
val and_l : term list -> term
val or_ : term -> term -> term
val or_l : term list -> term
val imply : term -> term -> term
val true_ : term
val false_ : term
val asserting : term -> term -> term

val unfold_fun : term -> var list * term

(** {2 Printing} *)

val term_to_sexp : term to_sexp
val statement_to_sexp : statement to_sexp

val pp_term : term CCFormat.printer
val pp_statement : statement CCFormat.printer

val pp_term_tip : term CCFormat.printer
val pp_ty_tip : Ty.t CCFormat.printer
val pp_statement_tip : statement CCFormat.printer

(** {2 Parsing and Typing} *)

module Ctx : sig
  type t
  val create: include_dir:string -> unit -> t
  include Intf.PRINT with type t := t
end

type syntax =
  | Auto
  (** Guess based on file extension *)
  | Smbc
  (** Native syntax *)
  | Tip
  (** Syntax for Tip (https://github.com/tip-org/)

      This is a small subset of Smtlib2, so we can reuse the same S-expr
      parser as {!Smbc} *)

val string_of_syntax : syntax -> string

val parse : include_dir:string -> file:string -> syntax -> statement list or_error
(** Parse the given file, type-check, etc.
    @raise Error in case the input is ill formed
    @raise Ill_typed if the input is ill typed *)

val parse_stdin : syntax -> statement list or_error
(** Parse stdin, type-check, etc.
    @raise Error in case the input is ill formed
    @raise Ill_typed if the input is ill typed *)

(** {2 Environment} *)

type env_entry =
  | E_uninterpreted_ty
  | E_uninterpreted_cst (* domain element *)
  | E_const of Ty.t
  | E_data of Ty.t ID.Map.t (* list of cstors *)
  | E_cstor of Ty.t
  | E_defined of Ty.t * term (* if defined *)

type env = {
  defs: env_entry ID.Map.t;
}
(** Environment with definitions and goals *)

val env_empty : env

val env_add_statement : env -> statement -> env

val env_of_statements: statement Sequence.t -> env

val env_find_def : env -> ID.t -> env_entry option

val env_add_def : env -> ID.t -> env_entry -> env

