
(* This file is free software. See file "license" for more details. *)

type 'a t = 'a -> int

val int : int t
val string : string t
val combine_int : int -> int -> int
val combine : 'a t -> int -> 'a -> int
val list : 'a t -> 'a list t
