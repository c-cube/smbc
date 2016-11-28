
(* This file is free software. See file "license" for more details. *)

(** {1 Utils} *)

val pp_list : ?sep:string -> 'a CCFormat.printer -> 'a list CCFormat.printer

val compose_n : int -> ('a -> 'a) -> 'a -> 'a
(** [compose_n n f x] is [f^n x] *)
