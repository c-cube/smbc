
(* This file is free software. See file "license" for more details. *)

let parse_file file =
  let res = CCSexpM.parse_file_list file in
  match res with
    | `Error msg -> print_endline msg; exit 1
    | `Ok l ->
      match Ast.statements_of_sexps l with
        | Result.Error msg -> print_endline msg; exit 1
        | Result.Ok ast -> ast

let solve (ast:Ast.statement list) : unit =
  let module S = Solver.Make(struct end) in
  (* add statements *)
  S.add_statement_l ast;
  (* solve *)
  match S.check () with
    | S.Sat m ->
      Format.printf "result: @{<Green>SAT@}@, model @[%a@]@." S.pp_model m
    | S.Unsat ->
      Format.printf "result: @{<Yellow>UNSAT@}@."
    | S.Unknown _ ->
      Format.printf "result: @{<blue>UNKNOWN@}@."

(** {2 Main} *)

let print_input_ = ref false
let color_ = ref true
let file = ref ""
let set_file s =
  if !file = "" then file := s
  else failwith "provide at most one file"

let options =
  Arg.align [
    "--print-input", Arg.Set print_input_, " print input";
    "-nc", Arg.Clear color_, " do not use colors";
    "--debug", Arg.Int Log.set_debug, " set debug level";
    "--backtrace", Arg.Unit (fun () -> Printexc.record_backtrace true), " enable backtrace";
  ]

let () =
  Arg.parse options set_file "experimental SMT solver";
  if !file = "" then failwith "provide one file";
  CCFormat.set_color_default !color_;
  (* parse *)
  let ast = parse_file !file in
  if !print_input_
  then 
    Format.printf "@[parsed:@ @[<v>%a@]@]@."
      (CCFormat.list ~start:"" ~stop:"" ~sep:"" Ast.pp_statement) ast;
  (* solve *)
  solve ast
