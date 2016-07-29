
(* This file is free software. See file "license" for more details. *)

(** {1 Trivial AST for parsing} *)

module Loc = struct
  type t = {
    file : string;
    start_line : int;
    start_column : int;
    stop_line : int;
    stop_column : int;
  }

  let mk file start_line start_column stop_line stop_column =
    { file; start_line; start_column; stop_line; stop_column; }

  let mk_pair file (a,b)(c,d) = mk file a b c d

  let mk_pos start stop =
    let open Lexing in
    mk
      start.pos_fname
      start.pos_lnum (start.pos_cnum - start.pos_bol)
      stop.pos_lnum (stop.pos_cnum - stop.pos_bol)

  let equal = (=)

  let pp out pos =
    if pos.start_line = pos.stop_line
    then
      Format.fprintf out "file '%s': line %d, col %d to %d"
        pos.file pos.start_line pos.start_column pos.stop_column
    else
      Format.fprintf out "file '%s': line %d, col %d to line %d, col %d"
        pos.file
        pos.start_line pos.start_column
        pos.stop_line pos.stop_column

  let to_string = CCFormat.to_string pp

  let pp_opt out = function
    | None -> Format.fprintf out "<no location>"
    | Some pos -> pp out pos

  let to_string_opt = CCFormat.to_string pp_opt

  (** {2 Lexbuf} *)

  let set_file buf filename =
    let open Lexing in
    buf.lex_curr_p <- {buf.lex_curr_p with pos_fname=filename;};
    ()

  let get_file buf =
    let open Lexing in
    buf.lex_curr_p.pos_fname

  let of_lexbuf lexbuf =
    let start = Lexing.lexeme_start_p lexbuf in
    let end_ = Lexing.lexeme_end_p lexbuf in
    let s_l = start.Lexing.pos_lnum in
    let s_c = start.Lexing.pos_cnum - start.Lexing.pos_bol in
    let e_l = end_.Lexing.pos_lnum in
    let e_c = end_.Lexing.pos_cnum - end_.Lexing.pos_bol in
    let file = get_file lexbuf in
    mk file s_l s_c e_l e_c
end

(** {2 AST: S-expressions with locations} *)
type t = {
  cell: cell;
  loc: Loc.t option;
}

and cell =
  | List of t list
  | Atom of string

let _mk ?loc cell = { loc; cell }

let atom ?loc s : t = _mk ?loc (Atom s)
let list ?loc l : t = _mk ?loc (List l)
let int ?loc i : t = atom ?loc (string_of_int i)

let loc t = t.loc
let view t = t.cell

let rec pp out t = match t.cell with
  | Atom s ->
    if String.contains s ' ' || String.contains s '\\'
    then Format.fprintf out "\"%s\"" s
    else CCFormat.string out s
  | List l ->
    Format.fprintf out "(@[<hv1>%a@])" (Utils.pp_list ~sep:" " pp) l

(** {2 Errors} *)

exception Parse_error of Loc.t option * string

let () = Printexc.register_printer
    (function
      | Parse_error (loc, msg) ->
        Some (CCFormat.sprintf "parse error at %a:@ %s" Loc.pp_opt loc msg)
      | _ -> None)

let parse_error ?loc msg = raise (Parse_error (loc, msg))
let parse_errorf ?loc msg = Format.ksprintf (parse_error ?loc) msg
