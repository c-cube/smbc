
(* This file is free software. See file "license" for more details. *)

(** {1 Lexer for SMBC} *)

{
  module A = Parse_ast
  module Loc = A.Loc
  open Parser (* for tokens *)

}

let printable_char = [^ '\n']
let comment_line = ';' printable_char*

let sym = [^ '"' '(' ')' '\\' ' ' '\t' '\r' '\n']

let ident = sym+

let quoted = '"' ([^ '"'] | '\\' '"')* '"'

rule token = parse
  | eof { EOI }
  | '\n' { Lexing.new_line lexbuf; token lexbuf }
  | [' ' '\t' '\r'] { token lexbuf }
  | comment_line { token lexbuf }
  | '(' { LEFT_PAREN }
  | ')' { RIGHT_PAREN }
  | ident { IDENT(Lexing.lexeme lexbuf) }
  | quoted {
      (* TODO: unescape *)
      let s = Lexing.lexeme lexbuf in
      let s = String.sub s 1 (String.length s -2) in (* remove " " *)
      QUOTED s }
  | _ as c
    {
      let loc = Loc.of_lexbuf lexbuf in
      A.parse_errorf ~loc "unexpected char '%c'" c
    }

{

}
