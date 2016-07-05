
(* This file is free software. See file "license" for more details. *)

(** {1 Preprocessing AST} *)

type 'a or_error = ('a, string) CCResult.t
type sexp = CCSexp.t
type 'a to_sexp = 'a -> sexp

module S = CCSexp

let (<?>) = CCOrd.(<?>)

(** {2 Types} *)

module Var = struct
  type 'ty t = {
    id: ID.t;
    ty: 'ty;
  }

  let make id ty = {id;ty}
  let copy {id;ty} = {ty; id=ID.copy id}
  let ty v = v.ty

  let equal a b = ID.equal a.id b.id
  let pp out v = ID.pp out v.id
  let to_sexp f v = S.of_list [ID.to_sexp v.id; f v.ty]
end

type var = Ty.t Var.t

type binop =
  | And
  | Or
  | Imply

type term = {
  term: term_cell;
  ty: Ty.t;
}
and term_cell =
  | Var of var
  | Const of ID.t
  | App of term * term list
  | If of term * term * term
  | Match of term * (var list * term) ID.Map.t
  | Fun of var * term
  | Eq of term * term
  | Not of term
  | Binop of binop * term * term
  | True
  | False

type statement =
  | Data of Ty.data list
  | TyDecl of ID.t (* new atomic cstor *)
  | Decl of ID.t * Ty.t
  | Define of ID.t * Ty.t * term
  | Assert of term
  | Goal of var list * term

(** {2 Printing} *)

let var_sexp_ v = ID.to_sexp v.Var.id
let typed_var_to_sexp = Var.to_sexp Ty.to_sexp

let rec term_to_sexp t = match t.term with
  | Var v -> var_sexp_ v
  | Const id -> ID.to_sexp id
  | App (f,l) -> S.of_list (term_to_sexp f :: List.map term_to_sexp l)
  | If (a,b,c) ->
    S.of_list [S.atom "if"; term_to_sexp a; term_to_sexp b; term_to_sexp c]
  | Match (t, m) ->
    (S.atom "match" :: term_to_sexp t ::
      (ID.Map.to_list m
       |> List.map
         (fun (c,(vars, rhs)) -> match vars with
            | [] -> S.of_list [ID.to_sexp c; term_to_sexp rhs]
            | _::_ ->
              S.of_list
                [ S.of_list (ID.to_sexp c :: List.map var_sexp_ vars);
                  term_to_sexp rhs]
         )))
    |> S.of_list
  | Fun (v,t) -> S.of_list [S.atom "fun"; typed_var_to_sexp v; term_to_sexp t]
  | Eq (a,b) -> S.of_list [S.atom "="; term_to_sexp a; term_to_sexp b]
  | Not t -> S.of_list [S.atom "not"; term_to_sexp t]
  | Binop (And, a, b) ->
    S.of_list [S.atom "and"; term_to_sexp a; term_to_sexp b]
  | Binop (Or, a, b) ->
    S.of_list [S.atom "or"; term_to_sexp a; term_to_sexp b]
  | Binop (Imply, a, b) ->
    S.of_list [S.atom "=>"; term_to_sexp a; term_to_sexp b]
  | True -> S.atom "true"
  | False -> S.atom "false"

let statement_to_sexp st = match st with
  | Data l ->
    S.of_list
      (S.atom "data" :: List.map Ty.data_to_sexp l)
  | TyDecl id ->
    S.of_list [S.atom "type"; ID.to_sexp id]
  | Decl (id,ty) ->
    S.of_list [S.atom "decl"; ID.to_sexp id; Ty.to_sexp ty]
  | Define (id,ty,t) ->
    S.of_list
      [S.atom "define"; S.of_list [ID.to_sexp id; Ty.to_sexp ty]; term_to_sexp t]
  | Assert t ->
    S.of_list [S.atom "assert"; term_to_sexp t]
  | Goal (vars,t) ->
    S.of_list
      [S.atom "goal";
       S.of_list (List.map typed_var_to_sexp vars);
       term_to_sexp t]

let pp_term out t = CCSexpM.print out (term_to_sexp t)
let pp_statement out t = CCSexpM.print out (statement_to_sexp t)

(** {2 Constructors} *)

let rec app_ty_ ty l : Ty.t = match ty, l with
  | _, [] -> ty
  | Ty.Arrow (ty_a,ty_rest), a::tail ->
    if Ty.equal ty_a a.ty
    then app_ty_ ty_rest tail
    else Ty.ill_typed "expected `@[%a@]`,@ got `@[%a : %a@]`"
        Ty.pp ty_a pp_term a Ty.pp a.ty
  | (Ty.Prop | Ty.Const _), a::_ ->
    Ty.ill_typed "cannot apply ty `@[%a@]`@ to `@[%a@]`" Ty.pp ty pp_term a

let mk_ term ty = {term; ty}

let true_ = mk_ True Ty.prop
let false_ = mk_ False Ty.prop

let var v = mk_ (Var v) (Var.ty v)

let const id ty = mk_ (Const id) ty

let app f l = match f.term, l with
  | _, [] -> f
  | App (f1, l1), _ ->
    let ty = app_ty_ f.ty l in
    mk_ (App (f1, l1 @ l)) ty
  | _ ->
    let ty = app_ty_ f.ty l in
    mk_ (App (f, l)) ty

let if_ a b c =
  if a.ty <> Ty.Prop
  then Ty.ill_typed "if: test  must have type prop, not `@[%a@]`" Ty.pp a.ty;
  if not (Ty.equal b.ty c.ty)
  then Ty.ill_typed
      "if: both branches must have same type,@ not `@[%a@]` and `@[%a@]`"
      Ty.pp b.ty Ty.pp c.ty;
  mk_ (If (a,b,c)) b.ty

(* TODO: check types *)
let match_ t m =
  let _, (_, rhs) = ID.Map.choose m in
  mk_ (Match (t,m)) rhs.ty

let fun_ v t =
  let ty = Ty.arrow (Var.ty v) t.ty in
  mk_ (Fun (v,t)) ty

let fun_l = List.fold_right fun_

let eq a b =
  if not (Ty.equal a.ty b.ty)
  then Ty.ill_typed "eq: `@[%a@]` and `@[%a@]` do not have the same type"
      pp_term a pp_term b;
  mk_ (Eq (a,b)) Ty.prop

let check_prop_ t =
  if not (Ty.equal t.ty Ty.prop)
  then Ty.ill_typed "expected prop, got `@[%a : %a@]`" pp_term t Ty.pp t.ty

let binop op a b =
  check_prop_ a; check_prop_ b;
  mk_ (Binop (op, a, b)) Ty.prop

let and_ = binop And
let or_ = binop Or
let imply = binop Imply

let and_l = function
  | [] -> true_
  | [f] -> f
  | a :: l -> List.fold_left and_ a l

let or_l = function
  | [] -> false_
  | [f] -> f
  | a :: l -> List.fold_left or_ a l

let not_ t =
  check_prop_ t;
  mk_ (Not t) Ty.prop

(** {2 Parsing} *)

module StrTbl = CCHashtbl.Make(struct
    type t = string
    let equal = CCString.equal
    let hash = CCString.hash
  end)

exception Error of string

let () = Printexc.register_printer
    (function
      | Error msg -> Some ("ast error: " ^ msg)
      | _ -> None)

let errorf msg = CCFormat.ksprintf ~f:(fun e -> raise (Error e)) msg

module Ctx = struct
  type kind =
    | K_ty
    | K_fun of Ty.t
    | K_cstor of Ty.t
    | K_var of Ty.t (* local *)

  type t = {
    names: ID.t StrTbl.t;
    kinds: kind ID.Tbl.t;
  }

  let create() : t = {
    names=StrTbl.create 64;
    kinds=ID.Tbl.create 64;
  }

  let add_id t (s:string) (k:kind): ID.t =
    let id = ID.make s in
    StrTbl.add t.names s id;
    ID.Tbl.add t.kinds id k;
    id

  let with_var t (s:string) (ty:Ty.t) (f:Ty.t Var.t -> 'a): 'a =
    let id = ID.make s in
    StrTbl.add t.names s id;
    ID.Tbl.add t.kinds id (K_var ty);
    let v = Var.make id ty in
    CCFun.finally1 f v
      ~h:(fun () -> StrTbl.remove t.names s)

  let with_vars t (l:(string*Ty.t) list) (f:Ty.t Var.t list -> 'a): 'a =
    let rec aux ids l f = match l with
      | [] -> f (List.rev ids)
      | (s,ty) :: l' -> with_var t s ty (fun id -> aux (id::ids) l' f)
    in
    aux [] l f

  let find_kind t (id:ID.t) : kind =
    try ID.Tbl.find t.kinds id
    with Not_found -> errorf "did not find kind of ID `%a`" ID.pp id

  let pp_kind out = function
    | K_ty -> Format.fprintf out "type"
    | K_cstor ty ->
      Format.fprintf out "(@[cstor : %a@])" Ty.pp ty
    | K_fun ty ->
      Format.fprintf out "(@[fun : %a@])" Ty.pp ty
    | K_var ty ->
      Format.fprintf out "(@[var : %a@])" Ty.pp ty

  let pp out t =
    Format.fprintf out "ctx {@[%a@]}"
      (ID.Tbl.print ID.pp pp_kind) t.kinds
end

let find_id_ ctx (s:string): ID.t =
  try StrTbl.find ctx.Ctx.names s
  with Not_found -> errorf "name `%s` not in scope" s

let rec conv_ty ctx s = match s with
  | `Atom "prop" -> Ty.prop
  | `Atom s -> let id = find_id_ ctx s in Ty.const id
  | `List (`Atom "->" :: a :: ((_::_) as rest)) ->
    let rec aux_arr a rest = match rest with
      | [] -> a
      | b :: rest' ->
        let b = conv_ty ctx b in
        Ty.arrow a (aux_arr b rest')
    in
    let a = conv_ty ctx a in
    aux_arr a rest
  | _ -> errorf "expected type, got `@[%a@]`" CCSexpM.print s

let rec conv_term ctx s = match s with
  | `Atom "true" -> true_
  | `Atom "false" -> false_
  | `Atom s ->
    let id = find_id_ ctx s in
    let ty = match Ctx.find_kind ctx id with
      | Ctx.K_var ty
      | Ctx.K_fun ty
      | Ctx.K_cstor ty -> ty
      | Ctx.K_ty -> errorf "expected term, not type; got `%a`" ID.pp id
    in
    const id ty
  | `List [`Atom "if"; a; b; c] ->
    let a = conv_term ctx a in
    let b = conv_term ctx b in
    let c = conv_term ctx c in
    if_ a b c
  | `List [`Atom "fun"; `List [`Atom x; ty]; body] ->
    let ty = conv_ty ctx ty in
    Ctx.with_var ctx x ty
      (fun var ->
         let body = conv_term ctx body in
         fun_ var body)
  | `List (`Atom "and" :: l) ->
    let l = List.map (conv_term ctx) l in
    and_l l
  | `List (`Atom "or" :: l) ->
    let l = List.map (conv_term ctx) l in
    or_l l
  | `List [`Atom "not"; a] ->
    let a = conv_term ctx a in
    not_ a
  | `List [`Atom "="; a; b] ->
    let a = conv_term ctx a in
    let b = conv_term ctx b in
    eq a b
  | `List [`Atom "imply"; a; b] ->
    let a = conv_term ctx a in
    let b = conv_term ctx b in
    imply a b
  | `List (`Atom "match" :: lhs :: cases) ->
    let parse_case = function
      | `List [`Atom c; rhs] ->
        let c_id = find_id_ ctx c in
        let rhs = conv_term ctx rhs in
        c_id, ([], rhs)
      | `List [`List (`Atom c :: vars); rhs] ->
        let c_id = find_id_ ctx c in
        (* obtain the type *)
        let ty_args, _ty_ret = match Ctx.find_kind ctx c_id with
          | Ctx.K_cstor ty -> Ty.unfold ty
          | _ -> errorf "expected `%a` to be a constructor" ID.pp c_id
        in
        (* pair variables with their type *)
        if List.length vars <> List.length ty_args
        then
          errorf
            "in `@[%a@]` for case %a,@ wrong number of arguments (expected %d)"
            CCSexpM.print s ID.pp c_id (List.length ty_args);
        let vars =
          List.map2
            (fun s ty -> match s with
              | `Atom name -> name, ty
              | _ ->
                errorf "expected variable in case `%a`,@ got `@[%a@]`"
                  ID.pp c_id CCSexpM.print s)
            vars ty_args
        in
        Ctx.with_vars ctx vars
          (fun vars ->
             let rhs = conv_term ctx rhs in
             c_id, (vars, rhs))
      | s -> errorf "expected match-branch,@ got `@[%a@]`" CCSexpM.print s
    in
    let lhs = conv_term ctx lhs in
    let cases = List.map parse_case cases |> ID.Map.of_list in
    match_ lhs cases
  | `List (f :: ((_::_) as args)) ->
    let f = conv_term ctx f in
    let args = List.map (conv_term ctx) args in
    app f args
  | _ -> errorf "expected term,@ got `@[%a@]`" CCSexpM.print s

let conv_statement ctx s : statement = match s with
  | `List [`Atom "decl"; `Atom s; ty] ->
    let ty = conv_ty ctx ty in
    let id = Ctx.add_id ctx s (Ctx.K_fun ty) in
    Decl (id,ty)
  | `List (`Atom "data" :: l) ->
    (* first, read and declare each datatype (it can occur in the other
       datatypes' construtors) *)
    let pre_parse = function
      | `List (`Atom data_name :: cases) ->
        let data_id = Ctx.add_id ctx data_name Ctx.K_ty in
        data_id, cases
      | s -> errorf "expected data decl,@ got `@[%a@]`" CCSexpM.print s
    in
    let l = List.map pre_parse l in
    (* now parse constructors *)
    let l =
      List.map
        (fun (data_id, cstors) ->
           let data_ty = Ty.const data_id in
           let parse_case = function
             | `Atom c ->
               let id = Ctx.add_id ctx c (Ctx.K_cstor data_ty) in
               id, data_ty
             | `List (`Atom c :: args) ->
               let ty_args = List.map (conv_ty ctx) args in
               let ty_c = Ty.arrow_l ty_args data_ty in
               let id = Ctx.add_id ctx c (Ctx.K_cstor ty_c) in
               id, ty_c
             | s -> errorf "expected data decl,@ got `@[%a@]`" CCSexpM.print s
           in
           let data_cstors =
             List.map parse_case cstors
             |> ID.Map.of_list
           in
           {Ty.data_id; data_cstors})
        l
    in
    Data l
  | `List [`Atom "define"; `List [`Atom name; ty]; rhs] ->
    let ty = conv_ty ctx ty in
    let id = Ctx.add_id ctx name (Ctx.K_fun ty) in
    let rhs = conv_term ctx rhs in
    Define (id, ty, rhs)
  | `List [`Atom "goal"; `List vars; rhs] ->
    let vars =
      List.map
        (function
          | `List [`Atom s; ty] ->
            let ty = conv_ty ctx ty in s, ty
          | s -> errorf "expected typed var,@ got `@[%a@]`" CCSexpM.print s)
        vars
    in
    Ctx.with_vars ctx vars
      (fun vars ->
         let rhs = conv_term ctx rhs in
         Goal (vars, rhs))
  | _ -> errorf "expected statement,@ got `@[%a@]`" CCSexpM.print s

let term_of_sexp ctx s =
  try conv_term ctx s |> CCResult.return
  with e -> CCResult.of_exn_trace e

let statement_of_sexp ctx s =
  try conv_statement ctx s |> CCResult.return
  with e -> CCResult.of_exn_trace e

let statements_of_sexps ?(init=Ctx.create()) l =
  try
    CCList.map (conv_statement init) l
    |> CCResult.return
  with e ->
    CCResult.of_exn_trace e

