(*
MSAT is free software, using the Apache license, see file LICENSE
Copyright 2014 Guillaume Bury
Copyright 2014 Simon Cruanes
*)

(** {1 Logging functions} *)

let debug_level_ = ref 0
let set_debug l = debug_level_ := l
let get_debug () = !debug_level_

let debug_fmt_ = ref Format.std_formatter

let set_debug_out f = debug_fmt_ := f

let debug_real_ l k =
  CCFormat.fprintf !debug_fmt_ "@[<2>@{<Blue>[debug %d]@}@ " l;
  k (Format.kfprintf
      (fun fmt -> Format.fprintf fmt "@]@.")
      !debug_fmt_)

let debugf l k =
  if l <= !debug_level_
  then debug_real_ l k

let debug l msg = debugf l (fun k->k "%s" msg)
