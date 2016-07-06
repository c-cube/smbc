
(* This file is free software. See file "license" for more details. *)

(** {1 Solver}

    The solving algorithm, based on MCSat *)

(** {2 Typed De Bruijn indices} *)
module DB : sig
  type t
  val make : int -> Ty.t -> t
  val level : t -> int
  val ty : t -> Ty.t
  val succ : t -> t
end

(** {2 The Main Solver} *)

module Make(Dummy : sig end) : sig
  type term
  type cst = term Typed_cst.t

  (** {2 Typed Constant} *)
  module Typed_cst : sig
    type t

    (** The various kinds of constants *)
    and cst_kind =
      | Cst_undef of Ty.t * cst_info
      | Cst_cstor of Ty.t * Ty.data
      | Cst_defined of Ty.t * term

    and cst_info = {
      cst_depth: int;
      (* refinement depth, used for iterative deepening *)
      cst_parent: t option;
      (* if const was created as argument of another const *)
      mutable cst_cases : term list option;
      (* cover set (lazily evaluated) *)
    }

    (* TODO: replace Ty.data with something using Typed_cst so that
       there is no global environment *)

    val make : ID.t -> cst_kind -> t
    val make_undef : ?parent:t -> ID.t -> Ty.t -> t
    val make_cstor : ID.t -> Ty.t -> Ty.data -> t
    val make_defined: ID.t -> Ty.t -> term -> t

    val id : t -> ID.t
    val kind : t -> cst_kind
    val ty : t -> Ty.t

    val ty_of_kind : cst_kind -> Ty.t

    val equal : t -> t -> bool
    val compare : t -> t -> int
    val hash : t -> int
    val pp : t CCFormat.printer

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

    (* TODO: meta-variables? *)

    val ty : t -> Ty.t

    include Intf.EQ with type t := t
    include Intf.ORD with type t := t
    include Intf.HASH with type t := t
    include Intf.PRINT with type t := t

    (* TODO: most of the interface, interning, etc.
       be careful to exploit DAG structure as much as possible *)
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

  val check : ?max_depth:int -> unit -> res
  (** [check ()] checks the satisfiability of the current set of statements *)
end
