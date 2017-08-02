
(* This file is free software. See file "license" for more details. *)

(** {1 Model with Rw_term} *)

module A = Rw_ast

type term = Rw_ast.term

type t = {
  consts: term ID.Map.t;
  (* constant -> its value *)
}

let make ~consts () = {consts}

let pp out (m:t) =
  let pp_term = A.T.pp in
  let pp_entry out (c,t) =
    Format.fprintf out "(@[<1>val@ %a@ %a@])"
      ID.pp_name c pp_term t
  in
  let es = ID.Map.to_list m.consts in
  Format.fprintf out "(@[<v>%a@])" (Utils.pp_list pp_entry) es
