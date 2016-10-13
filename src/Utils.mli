
(* This file is free software. See file "license" for more details. *)

(** {1 Utils} *)

val pp_list : ?sep:string -> 'a CCFormat.printer -> 'a list CCFormat.printer

val pp_iarray : ?sep:string -> 'a CCFormat.printer -> 'a IArray.t CCFormat.printer
