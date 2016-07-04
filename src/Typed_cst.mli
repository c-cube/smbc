
(* This file is free software. See file "license" for more details. *)

(** {1 Typed Constant} *)

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

val id : t -> ID.t
val kind : t -> kind
val ty : t -> Ty.t

include Intf.EQ with type t := t
include Intf.ORD with type t := t
include Intf.HASH with type t := t
include Intf.PRINT with type t := t
