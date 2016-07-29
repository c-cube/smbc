

(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Parser for Nunchaku} *)

%{
  module A = Parse_ast
  module Loc = A.Loc

%}

%token EOI

%token LEFT_PAREN
%token RIGHT_PAREN

%token BOOL
%token ARROW

%token TRUE
%token FALSE
%token IF
%token MATCH
%token CASE
%token FUN
%token MU

%token DATA
%token ASSERT
%token ASSERT_NOT
%token FORALL
%token DECL
%token DEFINE

%token <string>IDENT
%token <string>QUOTED

%start <Parse_ast.statement> parse
%start <Parse_ast.statement list> parse_list

%%

parse_list: l=stmt* EOI {l}

parse: t=stmt EOI { t }

%inline llist(X):
  | LEFT_PAREN l=X* RIGHT_PAREN { l }

cstor:
  | c=IDENT { c, [] }
  | LEFT_PAREN c=IDENT l=ty+ RIGHT_PAREN { c, l }

data:
  | LEFT_PAREN s=IDENT l=llist(cstor) RIGHT_PAREN { s,l }

stmt:
  | LEFT_PAREN ASSERT t=term RIGHT_PAREN
    {
      let loc = Loc.mk_pos $startpos $endpos in
      A.assert_ ~loc t
    }
  | LEFT_PAREN DECL s=IDENT ty=ty RIGHT_PAREN
    {
      let loc = Loc.mk_pos $startpos $endpos in
      A.decl ~loc s ty
    }
  | LEFT_PAREN DATA l=llist(data) RIGHT_PAREN
    {
      let loc = Loc.mk_pos $startpos $endpos in
      A.data ~loc l
    }

ty:
  | PROP { A.ty_prop }
  | s=IDENT { A.ty_const s }
  | LEFT_PAREN ARROW args=ty+ ret=ty RIGHT_PAREN
    { A.ty_arrow_l args ret }

term:
  | TRUE { A.true_ }
  | FALSE { A.false_ }
  | s=QUOTED { A.const s }
  | s=IDENT { A.const s }
  | LEFT_PAREN f=term args=term+ RIGHT_PAREN { A.app f args }



%%
