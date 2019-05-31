
(* This file is free software. See file "license" for more details. *)

(** {1 Imperative Set} *)

type 'a t

val create :
  eq:('a -> 'a -> bool) ->
  int ->
  'a t
(** [create ~eq ~hash size] makes a new set of initial size [size] *)

val mem : 'a t -> 'a -> bool
(** Check if an element is within *)

val add : 'a t -> 'a -> unit
(** Add an element *)

val to_seq : 'a t -> 'a Iter.t
(** Iterate on elements that are alive *)

val iter : ('a -> unit) -> 'a t -> unit
