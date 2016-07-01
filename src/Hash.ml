
(* This file is free software. See file "license" for more details. *)

type 'a t = 'a -> int

let int i = i land max_int

let string (s:string) = Hashtbl.hash s

let combine_int a b = Hashtbl.seeded_hash a b
let combine f a b = Hashtbl.seeded_hash a (f b)

let list f l = List.fold_left (combine f) 0x42 l
