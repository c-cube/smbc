
(* This file is free software. See file "license" for more details. *)

(** {1 Utils} *)

let pp_list ?(sep=" ") pp out l =
  CCFormat.list ~start:"" ~stop:"" ~sep pp out l
