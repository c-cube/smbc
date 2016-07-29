
(* This file is free software. See file "license" for more details. *)

type config = {
  max_depth: int;
  print_stat: bool;
  dot_term_graph: string option;
  pp_hashcons: bool;
  progress : bool;
  deepening_step: int option;
  check: bool;
}

let parse_file file : Ast.statement list =
  Log.debugf 2 (fun k->k "(@[parse_file@ %S@])" file);
  let dir = Filename.dirname file in
  let res = Ast.parse ~include_dir:dir ~file in
  match res with
    | Result.Error msg -> print_endline msg; exit 1
    | Result.Ok l -> l

let solve ~config (ast:Ast.statement list) : unit =
  let module Conf = struct
    let max_depth = config.max_depth
    let pp_hashcons = config.pp_hashcons
    let progress = config.progress
    let deepening_step = config.deepening_step
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
  let res = S.solve ~on_exit ~check:config.check () in
  if config.print_stat then Format.printf "%a@." S.pp_stats ();
  match res with
    | S.Sat m ->
      Format.printf "(@[<1>result @{<Green>SAT@}@ :model @[%a@]@])@." S.pp_model m;
    | S.Unsat ->
      Format.printf "(result @{<Yellow>UNSAT@})@."
    | S.Unknown _ ->
      Format.printf "(result @{<blue>UNKNOWN@})@."

(** {2 Main} *)

let print_input_ = ref false
let color_ = ref true
let dot_term_graph_ = ref ""
let stats_ = ref false
let progress_  = ref false
let pp_hashcons_ = ref false
let max_depth_ = ref 60
let depth_step_ = ref 0
let check_ = ref false
let timeout_ = ref ~-1

let file = ref ""
let set_file s =
  if !file = "" then file := s
  else failwith "provide at most one file"

let set_debug_ d =
  Log.set_debug d;
  Msat.Log.set_debug d;
  ()

let options =
  Arg.align [
    "--print-input", Arg.Set print_input_, " print input";
    "--max-depth", Arg.Set_int max_depth_, " set max depth";
    "--dot-term-graph", Arg.Set_string dot_term_graph_, " print term graph in file";
    "--check", Arg.Set check_, " check model";
    "--no-check", Arg.Clear check_, " do not check model";
    "-nc", Arg.Clear color_, " do not use colors";
    "-p", Arg.Set progress_, " progress bar";
    "--pp-hashcons", Arg.Set pp_hashcons_, " print hashconsing IDs";
    "--debug", Arg.Int set_debug_, " set debug level";
    "--stats", Arg.Set stats_, " print stats";
    "--backtrace", Arg.Unit (fun () -> Printexc.record_backtrace true), " enable backtrace";
    "--depth-step", Arg.Set_int depth_step_, " increment for iterative deepening";
    "--timeout", Arg.Set_int timeout_, " timeout (in s)";
    "-t", Arg.Set_int timeout_, " alias to --timeout";
  ]

let setup_timeout_ t =
  assert (t >= 1);
  Sys.set_signal Sys.sigalrm
    (Sys.Signal_handle (fun _ -> print_endline "(TIMEOUT)"; exit 0));
  ignore (Unix.alarm !timeout_);
  ()

let setup_gc () =
  let g = Gc.get () in
  g.Gc.space_overhead <- 300;
  g.Gc.max_overhead <- 1000000; (* disable compaction *)
  g.Gc.minor_heap_size <- 500_000; (* ×8 to obtain bytes on 64 bits -->  *)
  Gc.set g

let () =
  Arg.parse options set_file "experimental SMT solver";
  if !file = "" then failwith "provide one file";
  CCFormat.set_color_default !color_;
  if !timeout_ >= 1 then setup_timeout_ !timeout_;
  setup_gc ();
  (* parse *)
  let ast = parse_file !file in
  if !print_input_
  then
    Format.printf "@[parsed:@ @[<v>%a@]@]@."
      (CCFormat.list ~start:"" ~stop:"" ~sep:"" Ast.pp_statement) ast;
  (* solve *)
  let config = {
    max_depth = !max_depth_;
    print_stat = !stats_;
    progress = !progress_;
    pp_hashcons = !pp_hashcons_;
    deepening_step =
      (if !depth_step_ = 0 then None else Some !depth_step_);
    dot_term_graph =
      (if !dot_term_graph_ = "" then None else Some !dot_term_graph_);
    check= !check_;
  } in
  solve ~config ast
