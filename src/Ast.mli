
(* This file is free software. See file "license" for more details. *)

(** {1 Preprocessing AST} *)

type 'a or_error = ('a, string) CCResult.t
type sexp = CCSexp.t
type 'a to_sexp = 'a -> sexp

(** {2 Types} *)

exception Error of string

type var = Ty.t Var.t

type binop =
  | And
  | Or
  | Imply
  | Eq

type binder =
  | Fun
  | Forall
  | Exists
  | Mu

type term = private {
  term: term_cell;
  ty: Ty.t;
}
and term_cell =
  | Var of var
  | Const of ID.t
  | Unknown of ID.t
  | App of term * term list
  | If of term * term * term
  | Select of select * term
  | Match of term * (var list * term) ID.Map.t
  | Switch of term * term ID.Map.t (* switch on constants *)
  | Bind of binder * var * term
  | Let of var * term * term
  | Not of term
  | Binop of binop * term * term
  | Asserting of term * term
  | Undefined_value
  | Bool of bool

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
val ty : term -> Ty.t

val var : var -> term
val const : ID.t -> Ty.t -> term
val unknown : ID.t -> Ty.t -> term
val app : term -> term list -> term
val app_a : term -> term array -> term
val select : select -> term -> Ty.t -> term
val if_ : term -> term -> term -> term
val match_ : term -> (var list * term) ID.Map.t -> term
val switch : term -> term ID.Map.t -> term
val let_ : var -> term -> term -> term
val bind : ty:Ty.t -> binder -> var -> term -> term
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
val undefined_value : Ty.t -> term
val asserting : term -> term -> term

val unfold_fun : term -> var list * term

val map :
  bind:('b_acc -> var -> 'b_acc * var) ->
  f:('b_acc -> term -> term) ->
  'b_acc ->
  term ->
  term

val fold :
  bind:('b_acc -> var -> 'b_acc) ->
  f:('b_acc -> 'acc -> term -> 'acc) ->
  'b_acc ->
  'acc ->
  term ->
  'acc

val free_vars : ?bound:Var.Set.t -> term -> Var.Set.t

val free_vars_l : ?bound:Var.Set.t -> term list -> Var.Set.t

(** {2 Substitutions} *)

module Subst : sig
  type t = term Var.Map.t

  val empty : t
  val is_empty : t -> bool
  val add : t -> var -> term -> t
  val mem : t -> var -> bool
  val find : t -> var -> term option
  val of_list : (var * term) list -> t
  val singleton : var -> term -> t

  val merge : t -> t -> t

  val rename : t -> var -> t * var

  val eval : t -> term -> term

  val pp : t CCFormat.printer
end

(** {2 Printing} *)

val pp_term : term CCFormat.printer
val pp_statement : statement CCFormat.printer

val pp_term_tip : term CCFormat.printer
val pp_ty_tip : Ty.t CCFormat.printer
val pp_statement_tip : statement CCFormat.printer

(** {2 Parsing and Typing} *)

type syntax =
  | Auto
  (** Guess based on file extension *)
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

