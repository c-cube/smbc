
(* This file is free software. See file "license" for more details. *)

(** {1 Solver}

    The solving algorithm, based on MCSat *)

module type CONFIG = sig
  val max_depth: int

  val deepening_step : int option
  (** Increment between two successive max depths in iterative deepening *)

  val progress: bool
  (** progress display progress bar *)

  val pp_hashcons: bool

  val dimacs_file : string option
  (** File for dumping the SAT problem *)
end

module Make(C:CONFIG)(Dummy : sig end) : sig
  type model = Model.t

  type unknown =
    | U_timeout
    | U_max_depth
    | U_incomplete

  type res =
    | Sat of Model.t
    | Unsat (* TODO: proof *)
    | Unknown of unknown

  val pp_stats : unit CCFormat.printer

  val add_statement_l : Ast.statement list -> unit

  val solve :
    ?on_exit:(unit -> unit) list ->
    ?check:bool ->
    unit ->
    res
  (** [solve ()] checks the satisfiability of the statement added so far
      @param check if true, the model is checked before returning
      @param on_exit functions to be run before this returns *)
end
