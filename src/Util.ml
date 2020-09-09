
(* This file is free software. See file "license" for more details. *)

(** {1 Util} *)

module Fmt = CCFormat

type 'a printer = 'a CCFormat.printer

let pp_list ?(sep=Fmt.return "@ ") pp out l =
  Fmt.list ~sep pp out l

let pp_iter ?(sep=Fmt.return "@ ") pp out l =
  Fmt.iter ~sep pp out l

let pp_array ?(sep=Fmt.return "@ ") pp out l =
  Fmt.array ~sep pp out l
