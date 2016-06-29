
(* This file is free software. See file "license" for more details. *)

(** {1 Unique Identifiers} *)

type t

val make : string -> t
val copy : t -> t

val to_string : t -> string
val to_sexp : t -> CCSexp.t

include Intf.EQ with type t := t
include Intf.ORD with type t := t
include Intf.PRINT with type t := t

val print_name : t CCFormat.printer

module Map : CCMap.S with type key = t
module Set : CCSet.S with type elt = t
