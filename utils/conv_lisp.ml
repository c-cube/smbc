#!/usr/bin/env ocaml

#use "topfind";;
#directory "_build/src/";;
#require "containers";;
#require "containers.sexp";;
#require "sequence";;
#require "result";;
#require "tip_parser";;
#load "Hash.cmo";;
#load "Utils.cmo";;
#load "ID.cmo";;
#load "Log.cmo";;
#load "Parse_ast.cmo";;
#load "Parser_smbc.cmo";;
#load "Lexer_smbc.cmo";;
#load "Ast.cmo";;

let process file =
  Format.printf "processing `%s`@." file;
  let stmts = Ast.parse ~include_dir:(Filename.dirname file) ~file Ast.Smbc in
  begin match stmts with
    | Result.Ok l ->
      (* Format.printf "@[<2>parsed@ %a@]@." (CCFormat.list Ast.pp_statement) l; *)
      let out_file = Filename.chop_suffix file ".lisp" ^ ".smt2" in
      CCIO.with_out out_file
        (fun oc ->
           let out = Format.formatter_of_out_channel oc in
           Format.fprintf out "@[<v>%a@]@."
             (CCFormat.list ~start:"" ~stop:"" ~sep:"" Ast.pp_statement_tip) l)
    | Result.Error e ->
      print_endline e;
      exit 1
  end

let () =
  for i=1 to Array.length Sys.argv-1 do
    process Sys.argv.(i)
  done
