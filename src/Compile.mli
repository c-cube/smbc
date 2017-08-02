
(* This file is free software. See file "license" for more details. *)

(** {1 Compilation to Rewriting} *)

type state

val create : unit -> state

val compile : state -> Ast.statement -> Rw_ast.statement list
(** [compile state st] compiles the statement's terms into rewrite-based
    terms, possibly modifying the state, and returns new statements. *)

val translate_model : state -> Rw_model.t -> Model.t
(** Translate a model back into normal AST *)

