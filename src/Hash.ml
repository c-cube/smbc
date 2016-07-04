
(* This file is free software. See file "license" for more details. *)

type 'a t = 'a -> int

let int i = i land max_int

let string (s:string) = Hashtbl.hash s

let combine f a b = Hashtbl.seeded_hash a (f b)

let combine2 a b = Hashtbl.seeded_hash a b

let combine3 a b c =
  combine2 a b
  |> combine2 c

let combine4 a b c d =
  combine2 a b
  |> combine2 c
  |> combine2 d

let pair f g (x,y) = combine2 (f x) (g y)

let list f l = List.fold_left (combine f) 0x42 l
let seq f seq =
  let h = ref 0x43 in
  seq (fun x -> h := combine f !h x);
  !h
