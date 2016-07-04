
(* This file is free software. See file "license" for more details. *)

(** {1 Functional Congruence Closure} *)

(** {2 Typed De Bruijn indices} *)
module DB : sig
  type t
  val make : int -> Ty.t -> t
  val level : t -> int
  val ty : t -> Ty.t
  val succ : t -> t
end

(** {2 Congruence Closure} *)

module Make(Dummy : sig end) : sig

  (** {2 Terms} *)

  module Term : sig
    type t

    val db : DB.t -> t
    val const : Typed_cst.t -> t
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
    include Intf.PRINT with type t := t

    (* TODO: most of the interface, interning, etc.
       be careful to exploit DAG structure as much as possible *)
  end

  type term = Term.t

  exception Inconsistent of term * term * term * term
  (** Exception raised when equality and inequality constraints are
      inconsistent. [Inconsistent (a, b, a', b')] means
      that [a=b, a=a', b=b'] in
      the congruence closure, but [a' != b'] was asserted before. *)

  type level
  (** Level for backtracking *)

  val cur_level : unit -> level
  (** Current level *)

  val push_level : unit -> level
  (** Push a new level and return the old one *)

  val backtrack : level -> unit
  (** Return to given level *)

  val normal_form : term -> term
  (** Current normal form of a term *)

  val check_eq : term -> term -> bool
  (** Check whether the two terms are equal *)

  val assert_choice : Typed_cst.t -> term -> unit
  (** [assert_choice c t] makes [c = t] valid in the current normalisation state,
      propagating equalities and reducing some terms along the way
      @raise Invalid_argument if the constant is already set
      @raise Inconsistent if this makes the state inconsistent because two
        terms have become equal, that should not *)

  val assert_neq : term -> term -> unit
  (** Assert that the two given terms are distinct
      @raise Inconsistent if this makes the state inconsistent *)

  (* explain why the normal form in terms of choices *)
  type explanation =
    | By_choice of Typed_cst.t * term (* assertion [c --> t] *)

  val pp_explanation : explanation CCFormat.printer

  val explain : term -> term -> explanation list
  (** Explain why those two terms are equal (assuming they are),
      by returning a list of atomic operations.
      @raise Invalid_argument if the terms are not equal modulo reduction *)
end
