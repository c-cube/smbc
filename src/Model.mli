
(* This file is free software. See file "license" for more details. *)

(** {1 Model} *)

type term = Ast.term
type ty = Ast.Ty.t
type domain = ID.t list

type fuel

type t = private {
  env: Ast.env;
  (* environment, defining symbols *)
  domains: domain Ast.Ty.Map.t;
  (* uninterpreted type -> its domain *)
  consts: term ID.Map.t;
  (* constant -> its value *)
  mutable local_fuel: fuel;
  (* used for computations. only use if you know what you are doing *)
}

val make :
  env:Ast.env ->
  consts:term ID.Map.t ->
  domains:domain Ast.Ty.Map.t ->
  t

val pp : t CCFormat.printer
val pp_tip : t CCFormat.printer
val pp_syn : Ast.syntax -> t CCFormat.printer

val eval : ?computation_limit:int -> t -> term -> term

exception Bad_model of t * term * term

val check : ?computation_limit:int -> t -> goals:term list -> unit
(** @raise Bad_model if some goal is not satisfied *)
