
(* This file is free software. See file "license" for more details. *)

(** {1 Imperative Set} *)

type 'a t = {
  eq: 'a -> 'a -> bool;
  vec: 'a CCVector.vector
}

let create (type a) ~eq _size : a t =
  {vec= CCVector.create (); eq; }

let mem (type a) (set:a t) x =
  try
    (* search from the most recent elements, so that if we add
       the same element several times it gets faster *)
    let a = CCVector.unsafe_get_array set.vec in
    let n = CCVector.size set.vec in
    for i = n-1 downto 0 do
      if set.eq x (Array.unsafe_get a i) then raise Exit
    done;
    false
  with Exit -> true

let add (type a) (set:a t) x =
  if not (mem set x) then CCVector.push set.vec x

let to_seq (type a) (set:a t) =
  CCVector.to_seq set.vec

let iter f s = to_seq s f
