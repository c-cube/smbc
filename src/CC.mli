
(* This file is free software. See file "license" for more details. *)

(** {1 Functional Congruence Closure} *)

(** {2 Typed Constant} *)

module TypedConst : sig
  type kind =
    | Const of Ty.t
    | Cstor of Ty.t * Ty.data
    (* TODO: defined function (how? terms are not defined here) *)

  type t = private {
    id: ID.t;
    kind: kind;
  }

  (* TODO: also, pointer to the definition/declaration/datatype
     to get rid of environment *)

  val make : ID.t -> kind -> t
  val make_const : ID.t -> Ty.t -> t
  val make_cstor : ID.t -> Ty.t -> Ty.data -> t

  val ty : t -> Ty.t

  include Intf.EQ with type t := t
  include Intf.ORD with type t := t
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

(** {2 Congruence Closure} *)

module Make(Dummy : sig end) : sig

  (** {2 Terms} *)

  module Term : sig
    type t

    val db : DB.t -> t
    val const : TypedConst.t -> t
    val app : t -> t list -> t
    val fun_ : Ty.t -> t -> t
    val match_ : t -> (Ty.t list * t) ID.Map.t -> t
    val if_ : t -> t -> t -> t
    val true_ : t
    val false_ : t
    val not_ : t -> t

    (* TODO: meta-variables? *)

    val ty : t -> Ty.t

    include Intf.EQ with type t := t
    include Intf.ORD with type t := t
    include Intf.PRINT with type t := t

    (* TODO: most of the interface, interning, etc.
       be careful to exploit DAG structure as much as possible *)
  end

  type term = Term.t

  (** {2 Equivalence Classes} *)

  module Equiv_class : sig
    type t
    (** An equivalence class *)

    val of_term : term -> t
    (** Intern the term in the congruence closure structure, obtaining its
        equivalence class *)

    val representative : t -> term
    (** Current representative of the class *)

    val true_ : t
    val false_ : t

    val to_seq : t -> term Sequence.t
    (** [equiv_class_seq ec] iterates on all terms in this equivalence
        class *)
  end

  exception Inconsistent of term * term * term * term
  (** Exception raised when equality and inequality constraints are
      inconsistent. [Inconsistent (a, b, a', b')] means
      that [a=b, a=a', b=b'] in
      the congruence closure, but [a' != b'] was asserted before. *)

  type level
  (** Level for backtracking *)

  val cur_level : unit -> level
  (** Current level *)

  val backtrack : level -> unit
  (** Return to given level *)

  val check_eq : term -> term -> bool
  (** Check whether the two terms are equal *)

  val assert_eq : term -> term -> level
  (** Assert that the two terms are equal
      @return the new level
      @raise Inconsistent if it makes the state inconsistent *)

  val assert_neq : term -> term -> level
  (** Assert that the two given terms are distinct
      @return the new level
      @raise Inconsistent if this makes the state inconsistent *)

  type explanation =
    | Exp_congruence of term * term (* direct congruence of terms *)
    | Exp_merge of term * term (* user merge of terms *)
  (* TODO: rules on beta-reduction, datatypes, ite, match... *)

  val explain : term -> term -> explanation list
  (** Explain why those two terms are equal (assuming they are),
      by returning a list of atomic operations.
      @raise Invalid_argument if the terms are not equal modulo CC *)
end
