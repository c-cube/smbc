
(* This file is free software. See file "license" for more details. *)

(** {1 Named Variables} *)

type sexp = CCSexp.t
type 'a to_sexp = 'a -> sexp

type 'ty t = private {
  id: ID.t;
  ty: 'ty;
}

val make : ID.t -> 'ty -> 'ty t
val makef : ty:'a -> ('b, Format.formatter, unit, 'a t) format4 -> 'b
val of_string : string -> 'ty -> 'ty t

val copy : 'a t -> 'a t
val id : _ t -> ID.t
val name : _ t -> string
val ty : 'a t -> 'a

val equal : 'a t -> 'a t -> bool
val compare : 'a t -> 'a t -> int
val hash : 'a t -> int
val pp : _ t CCFormat.printer
val to_sexp : _ t to_sexp
val to_sexp_typed : 'ty to_sexp -> 'ty t to_sexp

type ty_t = Ty.t t

module Set : CCSet.S with type elt = ty_t
module Tbl : CCHashtbl.S with type key = ty_t
module Map : sig
  include CCMap.S with type key = ty_t
  val merge_disj : 'a t -> 'a t -> 'a t
end
