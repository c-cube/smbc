
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
end

module Make(C:CONFIG)(Dummy : sig end) : sig
  type term
  type cst
  type ty_h (** types *)

  type cst_info

  (** The various kinds of constants *)
  type cst_kind =
    | Cst_bool
    | Cst_undef of ty_h * cst_info
    | Cst_cstor of ty_h
    | Cst_defined of ty_h * term lazy_t

  (** Definition of an atomic type *)
  type ty_def =
    | Uninterpreted (* uninterpreted type TODO: cardinal, \And, \Or *)
    | Data of cst lazy_t list (* set of constructors *)

  type ty_cell =
    | Prop
    | Atomic of ID.t * ty_def
    | Arrow of ty_h * ty_h

  type 'a db_env

  (** {2 Hashconsed Types} *)
  module Ty : sig
    type t = ty_h

    val view : t -> ty_cell

    val prop : t
    val atomic : ID.t -> ty_def -> t
    val arrow : t -> t -> t
    val arrow_l : t list -> t -> t

    val is_prop : t -> bool
    val is_data : t -> bool
    val unfold : t -> t list * t

    include Intf.EQ with type t := t
    include Intf.ORD with type t := t
    include Intf.HASH with type t := t
    include Intf.PRINT with type t := t
  end

  (** {2 Typed De Bruijn indices} *)
  module DB : sig
    type t
    val make : int -> Ty.t -> t
    val level : t -> int
    val ty : t -> Ty.t
    val succ : t -> t
  end

  (** {2 Typed Constant} *)
  module Typed_cst : sig
    type t = cst

    val id : t -> ID.t
    val kind : t -> cst_kind
    val ty : t -> Ty.t

    val ty_of_kind : cst_kind -> Ty.t

    include Intf.EQ with type t := t
    include Intf.ORD with type t := t
    include Intf.HASH with type t := t
    include Intf.PRINT with type t := t

    module Map : CCMap.S with type key = t
  end

  (** {2 Terms} *)

  module Term : sig
    type t = term

    val db : DB.t -> t
    val const : cst -> t
    val const_with_env : term db_env -> cst -> t
    val app : t -> t list -> t
    val fun_ : Ty.t -> t -> t
    val mu : t -> t
    val match_ : t -> (Ty.t list * t) ID.Map.t -> t
    val if_ : t -> t -> t -> t
    val true_ : t
    val false_ : t
    val not_ : t -> t
    val and_ : t -> t -> t
    val or_ : t -> t -> t
    val imply : t -> t -> t
    val eq : t -> t -> t

    val ty : t -> Ty.t

    include Intf.EQ with type t := t
    include Intf.ORD with type t := t
    include Intf.HASH with type t := t
    include Intf.PRINT with type t := t

    val pp_dot : t Sequence.t CCFormat.printer
  end

  (** {2 Literals} *)
  module Lit : sig
    type t

    val neg : t -> t
    val eq : term -> term -> t
    val neq : term -> term -> t
    val atom : ?sign:bool -> term -> t

    include Intf.EQ with type t := t
    include Intf.ORD with type t := t
    include Intf.HASH with type t := t
    include Intf.PRINT with type t := t
  end

  (** {2 Main} *)

  type model = term Typed_cst.Map.t
  (** Map from constants to their value *)

  val pp_model : model CCFormat.printer

  type unknown =
    | U_timeout
    | U_max_depth
    | U_incomplete

  type res =
    | Sat of model
    | Unsat (* TODO: proof *)
    | Unknown of unknown

  val pp_term_graph: unit CCFormat.printer
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
