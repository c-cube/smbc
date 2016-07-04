
(* This file is free software. See file "license" for more details. *)

type 'a t = 'a -> int

val int : int t
val string : string t
val combine : 'a t -> int -> 'a -> int

val pair : 'a t -> 'b t -> ('a * 'b) t

val list : 'a t -> 'a list t
val seq : 'a t -> 'a Sequence.t t

val combine2 : int -> int -> int
val combine3 : int -> int -> int -> int
val combine4 : int -> int -> int -> int -> int
