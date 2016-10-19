
(* This file is free software. See file "license" for more details. *)

(** {1 Model} *)

module A = Ast

type term = A.term
type ty = A.Ty.t
type domain = ID.t list

type t = private {
  env: A.env;
  (* environment, defining symbols *)
  domains: domain A.Ty.Map.t;
  (* uninterpreted type -> its domain *)
  consts: term ID.Map.t;
  (* constant -> its value *)
}

val make :
  env:A.env ->
  consts:term ID.Map.t ->
  domains:domain A.Ty.Map.t ->
  t

val pp : t CCFormat.printer
val pp_tip : t CCFormat.printer
val pp_syn : A.syntax -> t CCFormat.printer

val eval : t -> term -> term

exception Bad_model of t * term * term

val check : t -> goals:term list -> unit
(** @raise Bad_model if some goal is not satisfied *)
