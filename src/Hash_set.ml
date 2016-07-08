
(* This file is free software. See file "license" for more details. *)

(** {1 Weak set} *)

module type ELT = sig
  type t
  val equal : t -> t -> bool
  val hash : t -> int
  val size : int (* initial size of table *)
end

module type S = sig
  type elt

  val mem : elt -> bool
  val add : elt -> unit
  val to_seq : elt Sequence.t
end

module Mk(E : ELT)
  : S with type elt = E.t
= struct
  type elt = E.t

  module H = Hashtbl.Make(E)

  let tbl_ = H.create E.size

  let mem x = H.mem tbl_ x
  let add x = H.add tbl_ x ()
  let to_seq yield = H.iter (fun k () -> yield k) tbl_
end

type 'a t = (module S with type elt = 'a)

let create (type a) ~eq ~hash size : a t =
  let size = max size 8 in
  let module S = Mk(struct
      type t = a
      let size = size
      let equal = eq
      let hash = hash
    end) in
  (module S)

let mem (type a) (set:a t) x =
  let (module S) = set in
  S.mem x

let add (type a) (set:a t) x =
  let (module S) = set in
  S.add x

let to_seq (type a) (set:a t) =
  let (module S) = set in
  S.to_seq

let iter f s = to_seq s f
