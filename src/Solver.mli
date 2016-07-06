
(* This file is free software. See file "license" for more details. *)

(** {1 Solver}

    The solving algorithm, based on MCSat *)

module Make(Dummy : sig end) : sig
  type term
  type cst
  type ty_h (** types *)

  type cst_info = {
    cst_depth: int lazy_t;
    (* refinement depth, used for iterative deepening *)
    cst_parent: (cst * term) lazy_t option;
    (* if const was created as argument of another const in
       a given case *)
    mutable cst_cases : term list option;
    (* cover set (lazily evaluated) *)
    mutable cst_cases_blocked: term list;
    (* parts of cover set forbidden in current branch *)
  }

  (** The various kinds of constants *)
  type cst_kind =
    | Cst_bool
    | Cst_undef of ty_h * cst_info
    | Cst_cstor of ty_h
    | Cst_defined of ty_h * term

  (** Definition of an atomic type *)
  type ty_def =
    | Uninterpreted (* uninterpreted type TODO: cardinal, \And, \Or *)
    | Data of cst list (* set of constructors *)

  type ty_cell =
    | Prop
    | Atomic of ID.t * ty_def
    | Arrow of ty_h * ty_h

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

    val make : ID.t -> cst_kind -> t
    val make_bool : ID.t -> t
    val make_undef : ?parent:(t * term) lazy_t -> ID.t -> Ty.t -> t
    val make_cstor : ID.t -> Ty.t -> t
    val make_defined: ID.t -> Ty.t -> term -> t

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
    val app : t -> t list -> t
    val fun_ : Ty.t -> t -> t
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
  end

  (** {2 Literals} *)
  module Lit : sig
    type t

    val not_ : t -> t
    val eq : term -> term -> t
    val neq : term -> term -> t
    val atom : ?sign:bool -> term -> t

    include Intf.EQ with type t := t
    include Intf.ORD with type t := t
    include Intf.HASH with type t := t
    include Intf.PRINT with type t := t
  end

  (** {2 Main} *)

  val add_statement : Ast.statement -> unit

  val add_statement_l : Ast.statement list -> unit

  type model = term Typed_cst.Map.t
  (** Map from constants to their value *)

  type unknown =
    | U_timeout
    | U_max_depth

  type res =
    | Sat of model
    | Unsat (* TODO: proof *)
    | Unknown of unknown

  val check : unit -> res
  (** [check ()] checks the satisfiability of the
      current set of statements *)
end
