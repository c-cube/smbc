
(* This file is free software. See file "license" for more details. *)

(** {1 Utils} *)

type 'a printer = 'a CCFormat.printer

val pp_list : ?sep:unit printer -> 'a printer -> 'a list printer
val pp_seq : ?sep:unit printer -> 'a printer -> 'a Iter.t printer
val pp_array : ?sep:unit printer -> 'a printer -> 'a array printer
