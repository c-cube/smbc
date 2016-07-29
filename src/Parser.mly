

(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Parser for Nunchaku} *)

%{
  module A = Parse_ast
  module Loc = A.Loc

%}

%token EOI

%token LEFT_PAREN
%token RIGHT_PAREN
%token <string>IDENT
%token <string>QUOTED

%start <Parse_ast.t> parse
%start <Parse_ast.t list> parse_list

%%

parse_list: l=expr* EOI {l}

parse: t=expr EOI { t }

expr:
  | s=QUOTED
    {
      let loc = Loc.mk_pos $startpos $endpos in
      A.atom ~loc s
    }
  | s=IDENT
    {
      let loc = Loc.mk_pos $startpos $endpos in
      A.atom ~loc s
    }
  | LEFT_PAREN l=expr* RIGHT_PAREN
    {
      let loc = Loc.mk_pos $startpos $endpos in
      A.list ~loc l
    }



%%
