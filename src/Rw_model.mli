
(* This file is free software. See file "license" for more details. *)

(** {1 Model with Rw_ast} *)

type term = Rw_ast.term

type t = private {
  consts: term ID.Map.t;
  (* constant -> its value *)
}

val consts : t -> term ID.Map.t

val make :
  consts:term ID.Map.t ->
  unit ->
  t

val pp : t CCFormat.printer

(* TODO: checking? *)
