

(* This file is free software, part of nunchaku. See file "license" for more details. *)

(** {1 Parser for Nunchaku} *)

%{
  module A = Parse_ast
  module Loc = A.Loc

%}

%token EOI

%token LEFT_PAREN
%token RIGHT_PAREN

%token PROP
%token ARROW

%token TRUE
%token FALSE
%token IF
%token MATCH
%token FUN
%token MU
%token AND
%token OR
%token NOT
%token IMPLY
%token EQ
%token FORALL
%token EXISTS

%token DATA
%token ASSERT
%token GOAL
%token DECL
%token DECL_TY
%token DEFINE
%token INCLUDE

%token <string>IDENT
%token <string>QUOTED

%start <Parse_ast.statement> parse
%start <Parse_ast.statement list> parse_list

%%

parse_list: l=stmt* EOI {l}

parse: t=stmt EOI { t }

cstor:
  | c=IDENT { {cstor_name=c; cstor_args=[]} }
  | LEFT_PAREN c=IDENT l=ty+ RIGHT_PAREN
    { {cstor_name=c;
       cstor_args=List.map (fun ty->None,ty) l;}
    }

data:
  | LEFT_PAREN
      s=IDENT l=cstor+
    RIGHT_PAREN { s,l }

def:
  | LEFT_PAREN f=IDENT ty=ty t=term RIGHT_PAREN
    { f, ty, t }

stmt:
  | LEFT_PAREN INCLUDE s=QUOTED RIGHT_PAREN
    {
      let loc = Loc.mk_pos $startpos $endpos in
      A.include_ ~loc s
    }
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
  | LEFT_PAREN DECL_TY s=IDENT RIGHT_PAREN
    {
      let loc = Loc.mk_pos $startpos $endpos in
      A.ty_decl ~loc s
    }
  | LEFT_PAREN
      GOAL
      LEFT_PAREN l=typed_var* RIGHT_PAREN
      t=term
    RIGHT_PAREN
    {
      let loc = Loc.mk_pos $startpos $endpos in
      A.goal ~loc l t
    }
  | LEFT_PAREN
      DATA
      l=data+
    RIGHT_PAREN
    {
      let loc = Loc.mk_pos $startpos $endpos in
      A.data ~loc l
    }
  | LEFT_PAREN
      DEFINE
      l=def+
    RIGHT_PAREN
    {
      let loc = Loc.mk_pos $startpos $endpos in
      A.def ~loc ~rec_:true l
    }
  | error
    {
      let loc = Loc.mk_pos $startpos $endpos in
      A.parse_error ~loc "expected statement"
    }

ty:
  | PROP { A.ty_prop }
  | s=IDENT { A.ty_const s }
  | LEFT_PAREN ARROW ty1=ty ty2=ty+ RIGHT_PAREN
    {
      (* extract last ty *)
      let args, ret = match List.rev ty2 with
        | [] -> assert false
        | ret :: ty2' -> ty1 :: List.rev ty2', ret
      in
      A.ty_arrow_l args ret
    }
  | error
    {
      let loc = Loc.mk_pos $startpos $endpos in
      A.parse_error ~loc "expected type"
    }

typed_var:
  | LEFT_PAREN v=IDENT ty=ty RIGHT_PAREN { v, ty }

branch:
  | LEFT_PAREN s=IDENT rhs=term RIGHT_PAREN { A.Match_case (s, [], rhs) }
  | LEFT_PAREN
      LEFT_PAREN s=IDENT vars=IDENT+ RIGHT_PAREN
      rhs=term
    RIGHT_PAREN  { A.Match_case (s, vars, rhs) }

term:
  | TRUE { A.true_ }
  | FALSE { A.false_ }
  | s=QUOTED { A.const s }
  | s=IDENT { A.const s }
  | LEFT_PAREN f=term args=term+ RIGHT_PAREN { A.app f args }
  | LEFT_PAREN IF a=term b=term c=term RIGHT_PAREN { A.if_ a b c }
  | LEFT_PAREN FUN v=typed_var body=term RIGHT_PAREN { A.fun_ v body }
  | LEFT_PAREN FORALL v=typed_var body=term RIGHT_PAREN { A.forall v body }
  | LEFT_PAREN EXISTS v=typed_var body=term RIGHT_PAREN { A.exists v body }
  | LEFT_PAREN MATCH lhs=term l=branch+ RIGHT_PAREN { A.match_ lhs l }
  | LEFT_PAREN AND l=term+ RIGHT_PAREN { A.and_ l }
  | LEFT_PAREN OR l=term+ RIGHT_PAREN { A.or_ l }
  | LEFT_PAREN NOT t=term RIGHT_PAREN { A.not_ t }
  | LEFT_PAREN EQ a=term b=term RIGHT_PAREN { A.eq a b }
  | LEFT_PAREN IMPLY a=term b=term RIGHT_PAREN { A.imply a b }
  | error
    {
      let loc = Loc.mk_pos $startpos $endpos in
      A.parse_error ~loc "expected term"
    }



%%
