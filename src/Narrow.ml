
(* This file is free software. See file "license" for more details. *)

let run file =
  let res = CCSexpM.parse_file_list file in
  match res with
    | `Error msg -> print_endline msg; exit 1
    | `Ok l ->
      match Ast.statements_of_sexps l with
        | Result.Error msg -> print_endline msg; exit 1
        | Result.Ok ast ->
          Format.printf "@[parsed:@ @[<v>%a@]@]@."
            (CCFormat.list ~start:"" ~stop:"" ~sep:"" Ast.pp_statement) ast;
          failwith "todo"

(** {2 Main} *)

let file = ref ""
let set_file s =
  if !file = "" then file := s
  else failwith "provide at most one file"

let options =
  [
  ] |> Arg.align

let () =
  Arg.parse options set_file "experimental SMT solver";
  if !file = "" then failwith "provide one file";
  run !file
