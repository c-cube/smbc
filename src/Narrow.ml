
(* This file is free software. See file "license" for more details. *)

let parse_file file =
  let res = CCSexpM.parse_file_list file in
  match res with
    | `Error msg -> print_endline msg; exit 1
    | `Ok l ->
      match Ast.statements_of_sexps l with
        | Result.Error msg -> print_endline msg; exit 1
        | Result.Ok ast -> ast

(** {2 Main} *)

let print_input_ = ref false
let file = ref ""
let set_file s =
  if !file = "" then file := s
  else failwith "provide at most one file"

let options =
  Arg.align [
    "--print-input", Arg.Set print_input_, " print input"
  ]

let () =
  Arg.parse options set_file "experimental SMT solver";
  if !file = "" then failwith "provide one file";
  let ast = parse_file !file in
  if !print_input_
  then 
    Format.printf "@[parsed:@ @[<v>%a@]@]@."
      (CCFormat.list ~start:"" ~stop:"" ~sep:"" Ast.pp_statement) ast;
  failwith "todo"
