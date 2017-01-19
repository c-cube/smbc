
(* This file is free software. See file "license" for more details. *)

(** {1 Solver}

    The solving algorithm, based on MCSat *)

module type CONFIG = sig
  val max_depth: int

  val deepening_step : int option
  (** Increment between two successive max depths in iterative deepening *)

  val uniform_depth : bool
  (** Depth increases uniformly *)

  val progress: bool
  (** progress display progress bar *)

  val pp_hashcons: bool

  val dimacs_file : string option
  (** File for dumping the SAT problem *)
end

module Make(C:CONFIG)(Dummy : sig end) : sig
  type term
  type cst
  type ty_h (** types *)

  type cst_info

  type ty_def

  type ty_cell =
    | Prop
    | Atomic of ID.t * ty_def
    | Arrow of ty_h * ty_h

  type 'a db_env

  (** {2 Main} *)

  type model = Model.t

  type unknown =
    | U_timeout
    | U_max_depth
    | U_incomplete
    | U_undefined_values (* non-terminating functions, ill-applied selector, etc. *)

  val pp_unknown : unknown CCFormat.printer

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
