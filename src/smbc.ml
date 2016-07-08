
(* This file is free software. See file "license" for more details. *)

type config = {
  max_depth: int;
  dot_term_graph: string option;
}

let parse_file file =
  let res = CCSexpM.parse_file_list file in
  match res with
    | `Error msg -> print_endline msg; exit 1
    | `Ok l ->
      let dir = Filename.dirname file in
      let ctx = Ast.Ctx.create ~include_dir:dir () in
      match Ast.statements_of_sexps ctx l with
        | Result.Error msg -> print_endline msg; exit 1
        | Result.Ok ast -> ast

let solve ~config (ast:Ast.statement list) : unit =
  let module Conf = struct
    let max_depth = config.max_depth
  end in
  let module S = Solver.Make(Conf)(struct end) in
  let print_term_graph = match config.dot_term_graph with
    | None -> []
    | Some file ->
      let doit() =
        Log.debugf 1 (fun k->k "print term graph in `%s`" file);
        CCIO.with_out file
          (fun oc ->
             let fmt = Format.formatter_of_out_channel oc in
             S.pp_term_graph fmt ())
      in
      [doit]
  in
  let on_exit =
    print_term_graph
    @ []
  in
  (* solve *)
  S.add_statement_l ast;
  match S.check ~on_exit () with
    | S.Sat m ->
      Format.printf "result: @{<Green>SAT@},@ (@[<1>model@ @[%a@]@])@." S.pp_model m
    | S.Unsat ->
      Format.printf "result: @{<Yellow>UNSAT@}@."
    | S.Unknown _ ->
      Format.printf "result: @{<blue>UNKNOWN@}@."

(** {2 Main} *)

let print_input_ = ref false
let color_ = ref true
let dot_term_graph_ = ref ""
let max_depth_ = ref 60

let file = ref ""
let set_file s =
  if !file = "" then file := s
  else failwith "provide at most one file"

let options =
  Arg.align [
    "--print-input", Arg.Set print_input_, " print input";
    "--max-depth", Arg.Set_int max_depth_, " set max depth";
    "--dot-term-graph", Arg.Set_string dot_term_graph_, " print term graph in file";
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
  let config = {
    max_depth = !max_depth_;
    dot_term_graph =
      (if !dot_term_graph_ = "" then None else Some !dot_term_graph_);
  } in
  solve ~config ast
