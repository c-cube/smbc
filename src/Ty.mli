
(* This file is free software. See file "license" for more details. *)

(** {1 Simple Types} *)

type sexp = CCSexp.t
type 'a to_sexp = 'a -> sexp

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

val is_prop : t -> bool
val is_const : t -> bool
val is_arrow : t -> bool

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

exception Ill_typed of string

val ill_typed : ('a, Format.formatter, unit, 'b) format4 -> 'a
