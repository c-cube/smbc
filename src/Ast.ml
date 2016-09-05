
(* This file is free software. See file "license" for more details. *)

(** {1 Preprocessing AST} *)

type 'a or_error = ('a, string) CCResult.t
type sexp = CCSexp.t
type 'a to_sexp = 'a -> sexp

module S = CCSexp

exception Error of string

exception Ill_typed of string

let () = Printexc.register_printer
    (function
      | Error msg -> Some ("ast error: " ^ msg)
      | Ill_typed msg -> Some ("ill-typed: " ^ msg)
      | _ -> None)

let errorf msg =
  CCFormat.ksprintf ~f:(fun e -> raise (Error e)) msg

(** {2 Types} *)

module Var = struct
  type 'ty t = {
    id: ID.t;
    ty: 'ty;
  }

  let make id ty = {id;ty}
  let makef ~ty fmt =
    CCFormat.ksprintf fmt ~f:(fun s -> make (ID.make s) ty)
  let copy {id;ty} = {ty; id=ID.copy id}
  let id v = v.id
  let ty v = v.ty

  let equal a b = ID.equal a.id b.id
  let pp out v = ID.pp out v.id
  let to_sexp f v = S.of_list [ID.to_sexp v.id; f v.ty]
end

module Ty = struct
  type t =
    | Prop
    | Const of ID.t
    | Arrow of t * t

  let prop = Prop
  let const id = Const id
  let arrow a b = Arrow (a,b)
  let arrow_l = List.fold_right arrow

  let to_int_ = function
    | Prop -> 0
    | Const _ -> 1
    | Arrow _ -> 2

  let (<?>) = CCOrd.(<?>)

  let rec compare a b = match a, b with
    | Prop, Prop -> 0
    | Const a, Const b -> ID.compare a b
    | Arrow (a1,a2), Arrow (b1,b2) ->
      compare a1 b1 <?> (compare, a2,b2)
    | Prop, _
    | Const _, _
    | Arrow _, _ -> CCOrd.int_ (to_int_ a) (to_int_ b)

  let equal a b = compare a b = 0

  let hash _ = 0 (* TODO *)

  let unfold ty =
    let rec aux acc ty = match ty with
      | Arrow (a,b) -> aux (a::acc) b
      | _ -> List.rev acc, ty
    in
    aux [] ty

  let rec to_sexp = function
    | Prop -> S.atom "prop"
    | Const id -> S.atom (ID.to_string id)
    | Arrow _ as ty ->
      let args, ret = unfold ty in
      S.of_list (S.atom "->":: List.map to_sexp args @ [to_sexp ret])

  let pp out t = CCSexpM.print out (to_sexp t)

  (** {2 Datatypes} *)

  type data = {
    data_id: ID.t;
    data_cstors: t ID.Map.t;
  }

  let data_to_sexp d =
    let cstors =
      ID.Map.fold
        (fun c ty acc ->
           let ty_args, _ = unfold ty in
           let c_sexp = match ty_args with
             | [] -> ID.to_sexp c
             | _::_ -> S.of_list (ID.to_sexp c :: List.map to_sexp ty_args)
           in
           c_sexp :: acc)
        d.data_cstors []
    in
    S.of_list (ID.to_sexp d.data_id :: cstors)

  let ill_typed fmt =
    CCFormat.ksprintf
      ~f:(fun s -> raise (Ill_typed s))
      fmt
end

type var = Ty.t Var.t

type binop =
  | And
  | Or
  | Imply
  | Eq

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
  | Let of var * term * term
  | Fun of var * term
  | Forall of var * term
  | Exists of var * term
  | Mu of var * term
  | Not of term
  | Binop of binop * term * term
  | True
  | False

type definition = ID.t * Ty.t * term

type statement =
  | Data of Ty.data list
  | TyDecl of ID.t (* new atomic cstor *)
  | Decl of ID.t * Ty.t
  | Define of definition list
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
  | Let (v,t,u) ->
    S.of_list [S.atom "let"; var_sexp_ v; term_to_sexp t; term_to_sexp u]
  | Fun (v,t) ->
    S.of_list [S.atom "fun"; typed_var_to_sexp v; term_to_sexp t]
  | Forall (v,t) ->
    S.of_list [S.atom "forall"; typed_var_to_sexp v; term_to_sexp t]
  | Exists (v,t) ->
    S.of_list [S.atom "exists"; typed_var_to_sexp v; term_to_sexp t]
  | Mu (v,t) ->
    S.of_list [S.atom "mu"; typed_var_to_sexp v; term_to_sexp t]
  | Not t -> S.of_list [S.atom "not"; term_to_sexp t]
  | Binop (Eq, a, b) ->
    S.of_list [S.atom "="; term_to_sexp a; term_to_sexp b]
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
  | Define defs ->
    let def_to_sexp (id,ty,t) =
      S.of_list [ID.to_sexp id; Ty.to_sexp ty; term_to_sexp t]
    in
    S.of_list (S.atom "define" :: List.map def_to_sexp defs)
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

let term_view t = t.term

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

let match_ t m =
  let c1, (_, rhs1) = ID.Map.choose m in
  ID.Map.iter
    (fun c (_, rhs) ->
       if not (Ty.equal rhs1.ty rhs.ty)
       then Ty.ill_typed
           "match: cases %a and %a disagree on return type,@ \
           between %a and %a"
           ID.pp c1 ID.pp c Ty.pp rhs1.ty Ty.pp rhs.ty)
    m;
  mk_ (Match (t,m)) rhs1.ty

let let_ v t u =
  if not (Ty.equal (Var.ty v) t.ty)
  then Ty.ill_typed
      "let: variable %a : @[%a@]@ and bounded term : %a@ should have same type"
      Var.pp v Ty.pp (Var.ty v) Ty.pp t.ty;
  mk_ (Let (v,t,u)) u.ty

let fun_ v t =
  let ty = Ty.arrow (Var.ty v) t.ty in
  mk_ (Fun (v,t)) ty

let quant_ q v t =
  if not (Ty.equal t.ty Ty.prop)
  then Ty.ill_typed
      "quantifier: bounded term : %a@ should have type prop"
      Ty.pp t.ty;
  let ty = Ty.prop in
  mk_ (q v t) ty

let forall = quant_ (fun v t -> Forall (v,t))
let exists = quant_ (fun v t -> Exists (v,t))

let mu v t =
  if not (Ty.equal (Var.ty v) t.ty)
  then Ty.ill_typed "mu-term: var has type %a,@ body %a"
      Ty.pp (Var.ty v) Ty.pp t.ty;
  let ty = Ty.arrow (Var.ty v) t.ty in
  mk_ (Fun (v,t)) ty

let fun_l = List.fold_right fun_
let forall_l = List.fold_right forall
let exists_l = List.fold_right exists

let eq a b =
  if not (Ty.equal a.ty b.ty)
  then Ty.ill_typed "eq: `@[%a@]` and `@[%a@]` do not have the same type"
      pp_term a pp_term b;
  mk_ (Binop (Eq,a,b)) Ty.prop

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

module A = Parse_ast

type syntax =
  | Auto
  | Smbc
  | Tip

let string_of_syntax = function
  | Auto -> "auto"
  | Smbc -> "smbc"
  | Tip -> "tip"

module StrTbl = CCHashtbl.Make(struct
    type t = string
    let equal = CCString.equal
    let hash = CCString.hash
  end)

module Ctx = struct
  type kind =
    | K_ty of ty_kind
    | K_fun of Ty.t
    | K_cstor of Ty.t
    | K_var of var (* local *)

  and ty_kind =
    | K_data (* data type *)
    | K_uninterpreted (* uninterpreted type *)
    | K_other

  type t = {
    names: ID.t StrTbl.t;
    kinds: kind ID.Tbl.t;
    data: (ID.t * Ty.t) list ID.Tbl.t; (* data -> cstors *)
    included: unit StrTbl.t; (* included paths *)
    include_dir: string; (* where to look for includes *)
    mutable loc: A.Loc.t option; (* current loc *)
  }

  let create ~include_dir () : t = {
    names=StrTbl.create 64;
    kinds=ID.Tbl.create 64;
    data=ID.Tbl.create 64;
    included=StrTbl.create 8;
    include_dir;
    loc=None;
  }

  let loc t = t.loc
  let set_loc ?loc t = t.loc <- loc

  let add_id t (s:string) (k:kind): ID.t =
    let id = ID.make s in
    StrTbl.add t.names s id;
    ID.Tbl.add t.kinds id k;
    id

  let add_data t (id:ID.t) cstors: unit =
    ID.Tbl.add t.data id cstors

  let with_var t (s:string) (ty:Ty.t) (f:Ty.t Var.t -> 'a): 'a =
    let id = ID.make s in
    StrTbl.add t.names s id;
    let v = Var.make id ty in
    ID.Tbl.add t.kinds id (K_var v);
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

  let as_data t (ty:Ty.t) : (ID.t * Ty.t) list = match ty with
    | Ty.Const id ->
      begin match ID.Tbl.get t.data id with
        | Some l -> l
        | None -> errorf "expected %a to be a datatype" Ty.pp ty
      end
    | _ -> errorf "expected %a to be a constant type" Ty.pp ty

  let pp_kind out = function
    | K_ty _ -> Format.fprintf out "type"
    | K_cstor ty ->
      Format.fprintf out "(@[cstor : %a@])" Ty.pp ty
    | K_fun ty ->
      Format.fprintf out "(@[fun : %a@])" Ty.pp ty
    | K_var v ->
      Format.fprintf out "(@[var : %a@])" Ty.pp (Var.ty v)

  let pp out t =
    Format.fprintf out "ctx {@[%a@]}"
      (ID.Tbl.print ID.pp pp_kind) t.kinds
end

let errorf_ctx ctx msg =
  errorf ("at %a:@ " ^^ msg) Parse_ast.Loc.pp_opt (Ctx.loc ctx)

let find_id_ ctx (s:string): ID.t =
  try StrTbl.find ctx.Ctx.names s
  with Not_found -> errorf_ctx ctx "name `%s` not in scope" s

let rec conv_ty ctx (t:A.ty) =
  try conv_ty_aux ctx t
  with Ill_typed msg ->
    Ty.ill_typed "at %a:@ %s" A.Loc.pp_opt (Ctx.loc ctx) msg

and conv_ty_aux ctx t = match t with
  | A.Ty_bool -> Ty.prop, Ctx.K_ty Ctx.K_other
  | A.Ty_const s ->
    let id = find_id_ ctx s in
    Ty.const id, Ctx.find_kind ctx id
  | A.Ty_arrow (args, ret) ->
    let args = List.map (conv_ty_fst ctx) args in
    let ret, _ = conv_ty ctx ret in
    Ty.arrow_l args ret, Ctx.K_ty Ctx.K_other

and conv_ty_fst ctx t = fst (conv_ty ctx t)

let rec conv_term ctx (t:A.term) : term =
  try conv_term_aux ctx t
  with Ill_typed msg ->
    Ty.ill_typed "at %a:@ %s" A.Loc.pp_opt (Ctx.loc ctx) msg

and conv_term_aux ctx t = match t with
  | A.True -> true_
  | A.False -> false_
  | A.Const s ->
    let id = find_id_ ctx s in
    begin match Ctx.find_kind ctx id with
      | Ctx.K_var v -> var v
      | Ctx.K_fun ty
      | Ctx.K_cstor ty -> const id ty
      | Ctx.K_ty _ ->
        errorf_ctx ctx "expected term, not type; got `%a`" ID.pp id
    end
  | A.If (a,b,c) ->
    let a = conv_term ctx a in
    let b = conv_term ctx b in
    let c = conv_term ctx c in
    if_ a b c
  | A.Fun ((v,ty), body) ->
    let ty, _ = conv_ty ctx ty in
    Ctx.with_var ctx v ty
      (fun var ->
         let body = conv_term ctx body in
         fun_ var body)
  | A.Forall ((v,ty), body) ->
    let ty, ty_k = conv_ty ctx ty in
    if ty_k <> Ctx.K_ty Ctx.K_uninterpreted
    then Ty.ill_typed
        "unexpected quantification over @[%a@];@ only quantification \
         over uninterpreted types is supported"
        Ty.pp ty;
    Ctx.with_var ctx v ty
      (fun var ->
         let body = conv_term ctx body in
         forall var body)
  | A.Exists ((v,ty), body) ->
    let ty, ty_k = conv_ty ctx ty in
    if ty_k <> Ctx.K_ty Ctx.K_uninterpreted
    then Ty.ill_typed
        "unexpected quantification over @[%a@];@ only quantification \
         over uninterpreted types is supported"
        Ty.pp ty;
    Ctx.with_var ctx v ty
      (fun var ->
         let body = conv_term ctx body in
         exists var body)
  | A.Let (v,t,u) ->
    let t = conv_term ctx t in
    Ctx.with_var ctx v t.ty
      (fun var ->
         let u = conv_term ctx u in
         let_ var t u)
  | A.Mu ((x,ty), body) ->
    let ty, _ = conv_ty ctx ty in
    Ctx.with_var ctx x ty
      (fun var ->
         let body = conv_term ctx body in
         mu var body)
  | A.And l ->
    let l = List.map (conv_term ctx) l in
    and_l l
  | A.Or l ->
    let l = List.map (conv_term ctx) l in
    or_l l
  | A.Not a ->
    let a = conv_term ctx a in
    not_ a
  | A.Eq (a,b) ->
    let a = conv_term ctx a in
    let b = conv_term ctx b in
    eq a b
  | A.Imply (a,b) ->
    let a = conv_term ctx a in
    let b = conv_term ctx b in
    imply a b
  | A.Match (lhs, l) ->
    (* convert a regular case *)
    let conv_case c vars rhs =
      let c_id = find_id_ ctx c in
      (* obtain the type *)
      let ty_args, _ty_ret = match Ctx.find_kind ctx c_id with
        | Ctx.K_cstor ty -> Ty.unfold ty
        | _ ->
          errorf_ctx ctx "expected `@[%a@]`@ to be a constructor" ID.pp c_id
      in
      (* pair variables with their type *)
      if List.length vars <> List.length ty_args
      then
        errorf_ctx ctx
          "in @[%a@] for case %a,@ wrong number of arguments (expected %d)"
          A.pp_term t ID.pp c_id (List.length ty_args);
      let vars = List.combine vars ty_args in
      Ctx.with_vars ctx vars
        (fun vars ->
           let rhs = conv_term ctx rhs in
           c_id, vars, rhs)
    in
    (* convert default case, where [m] contains the partial map. We have
       to complete this map *)
    let lhs = conv_term ctx lhs in
    let default, cases =
      List.fold_left
        (fun (def,cases) branch -> match branch with
           | A.Match_case (c,vars,rhs) ->
             let c, vars, rhs = conv_case c vars rhs in
             (* no duplicate *)
             if ID.Map.mem c cases
             then errorf_ctx ctx "constructor %a occurs twice" ID.pp c;
             def, ID.Map.add c (vars,rhs) cases
          | A.Match_default rhs ->
            (* check there is only one "default" case *)
            match def with
              | Some _ -> errorf_ctx ctx "cannot have two `default` cases"
              | None ->
                let rhs = conv_term ctx rhs in
                Some rhs, cases)
        (None,ID.Map.empty) l
    in
    (* now fill the blanks, check exhaustiveness *)
    let all_cstors = Ctx.as_data ctx lhs.ty in
    let cases = match default with
      | None ->
        (* check exhaustiveness *)
        let missing =
          all_cstors
          |> List.filter (fun (cstor,_) -> not (ID.Map.mem cstor cases))
          |> List.map fst
        in
        if missing<>[]
        then errorf_ctx ctx
            "missing cases in `@[%a@]`: @[%a@]"
            A.pp_term t (Utils.pp_list ID.pp) missing;
        cases
      | Some def_rhs ->
        List.fold_left
          (fun cases (cstor,ty_cstor) ->
             if ID.Map.mem cstor cases then cases
             else (
               let args, _ = Ty.unfold ty_cstor in
               let vars = List.mapi (fun i ty -> Var.makef ~ty "_%d" i) args in
               ID.Map.add cstor (vars, def_rhs) cases
             ))
          cases all_cstors
    in
    match_ lhs cases
  | A.App (f, args) ->
    let f = conv_term ctx f in
    let args = List.map (conv_term ctx) args in
    app f args

let find_file_ name ~dir : string option =
  Log.debugf 2 (fun k->k "search A.%sA. in A.%sA." name dir);
  let abs_path = Filename.concat dir name in
  if Sys.file_exists abs_path
  then Some abs_path
  else None

let rec conv_statement ctx (syn:syntax) (s:A.statement): statement list =
  Log.debugf 2 (fun k->k "(@[<1>statement_of_ast@ `@[%a@]`@])" A.pp_stmt s);
  Ctx.set_loc ctx ?loc:s.A.loc;
  conv_statement_aux ctx syn s

and conv_statement_aux ctx syn (t:A.statement) : statement list = match A.view t with
  | A.Stmt_include s ->
    (* include now! *)
    let dir = ctx.Ctx.include_dir in
    begin match find_file_ s ~dir with
      | None -> errorf "could not find included file `%s`" s
      | Some s' when StrTbl.mem ctx.Ctx.included s' ->
        [] (* already included *)
      | Some s' ->
        (* put in cache *)
        StrTbl.add ctx.Ctx.included s' ();
        Log.debugf 2 (fun k->k "(@[parse_include@ %S@])" s');
        parse_file_exn ctx syn ~file:s'
    end
  | A.Stmt_ty_decl s ->
    let id = Ctx.add_id ctx s (Ctx.K_ty Ctx.K_uninterpreted) in
    [TyDecl id]
  | A.Stmt_decl (s, ty) ->
    let ty, _ = conv_ty ctx ty in
    let id = Ctx.add_id ctx s (Ctx.K_fun ty) in
    [Decl (id,ty)]
  | A.Stmt_data l ->
    (* first, read and declare each datatype (it can occur in the other
       datatypes' construtors) *)
    let pre_parse (data_name,cases) =
      let data_id = Ctx.add_id ctx data_name (Ctx.K_ty Ctx.K_data) in
      data_id, cases
    in
    let l = List.map pre_parse l in
    (* now parse constructors *)
    let l =
      List.map
        (fun (data_id, cstors) ->
           let data_ty = Ty.const data_id in
           let parse_case (c, ty_args) =
             let ty_args = List.map (conv_ty_fst ctx) ty_args in
             let ty_c = Ty.arrow_l ty_args data_ty in
             let id = Ctx.add_id ctx c (Ctx.K_cstor ty_c) in
             id, ty_c
           in
           let cstors = List.map parse_case cstors in
           (* update info on [data] *)
           Ctx.add_data ctx data_id cstors;
           {Ty.data_id; data_cstors=ID.Map.of_list cstors})
        l
    in
    [Data l]
  | A.Stmt_def defs ->
    (* parse id,ty and declare them before parsing the function bodies *)
    let preparse (name, ty, rhs) =
      let ty, _ = conv_ty ctx ty in
      let id = Ctx.add_id ctx name (Ctx.K_fun ty) in
      id, ty, rhs
    in
    let defs = List.map preparse defs in
    let defs =
      List.map
        (fun (id,ty,rhs) ->
           let rhs = conv_term ctx rhs in
           id,ty,rhs)
        defs
    in
    [Define defs]
  | A.Stmt_assert t ->
    let t = conv_term ctx t in
    check_prop_ t;
    [Assert t]
  | A.Stmt_goal (vars, t) ->
    let vars =
      List.map
        (fun (s,ty) ->
           let ty, _ = conv_ty ctx ty in
           s, ty)
        vars
    in
    Ctx.with_vars ctx vars
      (fun vars ->
         let t = conv_term ctx t in
         [Goal (vars, t)])

and parse_file_exn ctx (syn:syntax) ~file : statement list =
  let syn = match syn with
    | Tip | Smbc -> syn
    | Auto ->
      (* try to guess *)
      if CCString.suffix ~suf:".smt2" file then Tip else Smbc
  in
  Log.debugf 2 (fun k->k "use syntax: %s" (string_of_syntax syn));
  let l = match syn with
    | Auto -> assert false
    | Tip ->
      (* delegate parsing to [Tip_parser] *)
      Tip_util.parse_file_exn file
      |> CCList.filter_map A.Tip.conv_stmt
    | Smbc ->
      CCIO.with_in file
        (fun ic ->
           let lexbuf = Lexing.from_channel ic in
           A.Loc.set_file lexbuf file;
           Parser_smbc.parse_list Lexer_smbc.token lexbuf)
  in
  CCList.flat_map (conv_statement ctx syn) l

let parse ~include_dir ~file syn =
  let ctx = Ctx.create ~include_dir () in
  try Result.Ok (parse_file_exn ctx ~file syn)
  with e -> Result.Error (Printexc.to_string e)
