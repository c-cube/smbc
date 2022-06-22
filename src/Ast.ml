(* This file is free software. See file "license" for more details. *)

(** {1 Preprocessing AST} *)

open Common_
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
  Fmt.ksprintf ~f:(fun e -> raise (Error e)) msg

(** {2 Types} *)

module Var = struct
  type 'ty t = {
    id: ID.t;
    ty: 'ty;
  }

  let make id ty = {id;ty}
  let makef ~ty fmt =
    Fmt.ksprintf fmt ~f:(fun s -> make (ID.make s) ty)
  let copy {id;ty} = {ty; id=ID.copy id}
  let id v = v.id
  let ty v = v.ty

  let equal a b = ID.equal a.id b.id
  let compare a b = ID.compare a.id b.id
  let pp out v = ID.pp out v.id
  let to_sexp v = `Atom (ID.to_string_full v.id)
  (* let Var.to_sexp v = ID.to_sexp v.Var.id *)
  let to_sexp_typed f v = S.of_list [to_sexp v; f v.ty]
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
    | Arrow _, _ -> CCInt.compare (to_int_ a) (to_int_ b)

  let equal a b = compare a b = 0

  let hash _ = 0 (* TODO *)

  let unfold ty =
    let rec aux acc ty = match ty with
      | Arrow (a,b) -> aux (a::acc) b
      | _ -> List.rev acc, ty
    in
    aux [] ty

  let rec to_sexp = function
    | Prop -> `Atom "prop"
    | Const id -> `Atom (ID.to_string id)
    | Arrow _ as ty ->
      let args, ret = unfold ty in
      S.of_list (`Atom "->":: List.map to_sexp args @ [to_sexp ret])

  let pp out t = CCSexp.pp out (to_sexp t)

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

  module Map = CCMap.Make(struct
      type _t = t
      type t = _t
      let compare = compare
    end)

  let ill_typed fmt =
    Fmt.ksprintf
      ~f:(fun s -> raise (Ill_typed s))
      fmt
end

type var = Ty.t Var.t

type binop =
  | And
  | Or
  | Imply
  | Eq

type binder =
  | Fun
  | Forall
  | Exists
  | Mu

type term = {
  term: term_cell;
  ty: Ty.t;
}
and term_cell =
  | Var of var
  | Const of ID.t
  | Unknown of var (* meta var *)
  | App of term * term list
  | If of term * term * term
  | Select of select * term
  | Match of term * (var list * term) ID.Map.t * (ID.Set.t * term) option
  | Switch of term * term ID.Map.t (* switch on constants *)
  | Bind of binder * var * term
  | Let of var * term * term
  | Not of term
  | Binop of binop * term * term
  | Asserting of term * term
  | Undefined_value
  | Bool of bool

and select = {
  select_name: ID.t lazy_t;
  select_cstor: ID.t;
  select_i: int;
}

type definition = ID.t * Ty.t * term

type statement =
  | Data of Ty.data list
  | TyDecl of ID.t (* new atomic cstor *)
  | Decl of ID.t * Ty.t
  | Define of definition list
  | Assert of term
  | Goal of {
      prove: bool;
      vars: var list;
      body: term;
    }

(** {2 Helper} *)

let unfold_fun t =
  let rec aux acc t = match t.term with
    | Bind (Fun, v, t') -> aux (v::acc) t'
    | _ -> List.rev acc, t
  in
  aux [] t

(** {2 To TIP} *)

module TA = Smtlib_utils.V_2_6.Ast

let id_to_tip : ID.t -> string =
  let id_to_tip_tbl = ID.Tbl.create 64 in
  let str_id : (string, ID.t) Hashtbl.t = Hashtbl.create 32 in
  let sanitize_name =
    CCString.map
      (function '\'' -> '_' | '/' -> '_' | c -> c)
  in
  fun id ->
    try ID.Tbl.find id_to_tip_tbl id
    with Not_found ->
      let prefix =
        let p = ID.to_string id |> sanitize_name in
        if CCString.for_all (function '-'|'0'..'9'->true | _ -> false) p
        then "num_" ^ p (* TODO: option to control that, once nunchaku parses it *)
        else p
      in
      let n = ref 0 in
      let s = ref prefix in
      while Hashtbl.mem str_id !s do
        incr n;
        s := prefix ^ "_" ^ string_of_int !n
      done;
      let name = !s in
      Hashtbl.add str_id name id;
      ID.Tbl.add id_to_tip_tbl id name;
      name

let rec ty_to_tip ty: TA.ty = match ty with
  | Ty.Prop -> TA.ty_bool
  | Ty.Const id -> TA.ty_const (id_to_tip id)
  | Ty.Arrow (a,b) -> TA.ty_arrow (ty_to_tip a)(ty_to_tip b)

let var_to_tip v : TA.var = id_to_tip (Var.id v)
let typed_var_to_tip v = var_to_tip v, ty_to_tip (Var.ty v)

let rec term_to_tip (t:term): TA.term = match t.term with
  | Var v | Unknown v -> TA.const (var_to_tip v)
  | Const c -> TA.const (id_to_tip c)
  | Select ({select_name=lazy n; _}, arg) ->
    TA.app (id_to_tip n) [term_to_tip arg]
  | App (f,l) ->
    let f = term_to_tip f in
    let l = List.map term_to_tip l in
    begin match f with
      | TA.Const f_id -> TA.app f_id l
      | _ -> List.fold_left TA.ho_app f l
    end
  | If (a,b,c) -> TA.if_ (term_to_tip a)(term_to_tip b)(term_to_tip c)
  | Match (t,m,o) ->
    let m =
      ID.Map.to_list m
       |> List.map
         (fun (c,(vars,rhs)) ->
            TA.Match_case (
              id_to_tip c,
              List.map var_to_tip vars,
              term_to_tip rhs))
    and o = match o with
      | None -> []
      | Some (_,rhs) -> [TA.Match_default (term_to_tip rhs)]
    in
    TA.match_ (term_to_tip t) (m @ o)
  | Switch (t,m) ->
    let t = term_to_tip t in
    begin match ID.Map.to_list m with
      | [] -> assert false
      | (_, last_rhs) :: tail ->
        List.fold_left
          (fun else_ (c, rhs) ->
             let test = TA.eq t (TA.const (id_to_tip c)) in
             TA.if_ test (term_to_tip rhs) else_)
          (term_to_tip last_rhs) tail
    end
  | Bool true -> TA.true_
  | Bool false -> TA.false_
  | Let (v,t,u) ->
    TA.let_ [var_to_tip v, term_to_tip t] (term_to_tip u)
  | Bind (Fun,v,t) ->
    TA.fun_ (typed_var_to_tip v) (term_to_tip t)
  | Bind (Forall,v,t) ->
    TA.forall [typed_var_to_tip v] (term_to_tip t)
  | Bind (Exists,v,t) ->
    TA.exists [typed_var_to_tip v] (term_to_tip t)
  | Not t -> TA.not_ (term_to_tip t)
  | Binop (op,a,b) ->
    let a = term_to_tip a in
    let b = term_to_tip b in
    begin match op with
      | And -> TA.and_ [a;b]
      | Or -> TA.or_ [a;b]
      | Imply -> TA.imply a b
      | Eq -> TA.eq a b
    end
  | Asserting(t,g) -> TA.app "asserting" [term_to_tip t; term_to_tip g]
  | Undefined_value -> failwith "cannot translate `undefined-value` to TIP"
  | Bind (Mu,_,_) -> assert false (* TODO? *)

let mk_tip_def id ty rhs =
  let args, body = unfold_fun rhs in
  let ty_args, ty_ret = Ty.unfold ty in
  assert (List.length ty_args = List.length args);
  let args = List.map (fun {Var.id=v;ty} -> id_to_tip v, ty_to_tip ty) args in
  let ty_ret = ty_to_tip ty_ret in
  let body = term_to_tip body in
  TA.mk_fun_decl ~ty_vars:[] (id_to_tip id) args ty_ret, body

let statement_to_tip (t:statement) : TA.statement list = match t with
  | TyDecl id -> [TA.decl_sort (id_to_tip id) ~arity:0]
  | Decl (id,ty) ->
    let args, ret = Ty.unfold ty in
    let args = List.map ty_to_tip args in
    let ret = ty_to_tip ret in
    [TA.decl_fun ~tyvars:[] (id_to_tip id) args ret]
  | Data l ->
    let l =
      List.map
        (fun {Ty.data_id; data_cstors} ->
           let cstors =
             ID.Map.to_list data_cstors
             |> List.map
               (fun (id, ty) ->
                  let c = id_to_tip id in
                  let ty_args, _ = Ty.unfold ty in
                  let ty_args =
                    List.mapi
                      (fun i ty_arg ->
                         Printf.sprintf "select_%s_%d" c i, ty_to_tip ty_arg)
                      ty_args
                  in
                  TA.mk_cstor c ~vars:[] ty_args)
           in
           (id_to_tip data_id, 0), cstors)
        l
    in
    [TA.data l]
  | Define l ->
    let l =
      List.map
        (fun (id,ty,rhs) -> mk_tip_def id ty rhs)
        l
    in
    let decls, bodies = List.split l in
    [TA.funs_rec decls bodies]
  | Assert t ->
    [TA.assert_ (term_to_tip t)]
  | Goal {prove;vars;body=e} ->
    let vars = List.map typed_var_to_tip vars in
    let e = term_to_tip e in
    let t =
      if prove
      then TA.assert_ (TA.forall vars e)
      else TA.assert_ (TA.not_ (TA.forall vars (TA.not_ e))) in
    [t; TA.check_sat ()]

let pp_term_tip out t = TA.pp_term out (term_to_tip t)
let pp_term = pp_term_tip

let pp_ty_tip out ty = TA.pp_ty out (ty_to_tip ty)

let pp_statement_tip out stmt =
  List.iter (TA.pp_stmt out) (statement_to_tip stmt)
let pp_statement = pp_statement_tip

(** {2 Constructors} *)

let term_view t = t.term

let rec app_ty_ ty l : Ty.t = match ty, l with
  | _, [] -> ty
  | Ty.Arrow (ty_a,ty_rest), a::tail ->
    if Ty.equal ty_a a.ty then (
      app_ty_ ty_rest tail
    ) else (
      Ty.ill_typed "expected `@[%a@]`,@ got `@[%a : %a@]`"
        Ty.pp ty_a pp_term a Ty.pp a.ty
    )
  | (Ty.Prop | Ty.Const _), a::_ ->
    Ty.ill_typed "cannot apply ty `@[%a@]`@ to `@[%a@]`" Ty.pp ty pp_term a

let mk_ term ty = {term; ty}
let ty t = t.ty

let true_ = mk_ (Bool true) Ty.prop
let false_ = mk_ (Bool false) Ty.prop
let undefined_value ty = mk_ Undefined_value ty

let asserting t g =
  if not (Ty.equal Ty.prop g.ty) then (
    Ty.ill_typed "asserting: test  must have type prop, not `@[%a@]`" Ty.pp g.ty;
  );
  mk_ (Asserting (t,g)) t.ty

let var v = mk_ (Var v) (Var.ty v)
let unknown v = mk_ (Unknown v) (Var.ty v)

let const id ty = mk_ (Const id) ty

let select (s:select) (t:term) ty = mk_ (Select (s,t)) ty

let app f l = match f.term, l with
  | _, [] -> f
  | App (f1, l1), _ ->
    let ty = app_ty_ f.ty l in
    mk_ (App (f1, l1 @ l)) ty
  | _ ->
    let ty = app_ty_ f.ty l in
    mk_ (App (f, l)) ty

let app_a f a = app f (Array.to_list a)

let if_ a b c =
  if a.ty <> Ty.Prop
  then Ty.ill_typed "if: test  must have type prop, not `@[%a@]`" Ty.pp a.ty;
  if not (Ty.equal b.ty c.ty)
  then Ty.ill_typed
      "if: both branches must have same type,@ not `@[%a@]` and `@[%a@]`"
      Ty.pp b.ty Ty.pp c.ty;
  mk_ (If (a,b,c)) b.ty

let match_ t m ~default =
  let c1, (_, rhs1) = ID.Map.choose m in
  let check_ty what rhs =
    if not (Ty.equal rhs1.ty rhs.ty) then (
      Ty.ill_typed
        "match: cases %a and %s disagree on return type,@ \
         between %a and %a"
        ID.pp c1 what Ty.pp rhs1.ty Ty.pp rhs.ty
    )
  in
  ID.Map.iter
    (fun c (_, rhs) -> check_ty (ID.to_string c) rhs)
    m;
  Option.iter (fun (_,rhs) -> check_ty "default" rhs) default;
  mk_ (Match (t,m,default)) rhs1.ty

let match_l t l ~default = match_ t ~default (ID.Map.of_list l)

let switch u m =
  try
    let _, t1 = ID.Map.choose m in
    mk_ (Switch (u,m)) t1.ty
  with Not_found ->
    invalid_arg "Ast.switch: empty list of cases"

let let_ v t u =
  if not (Ty.equal (Var.ty v) t.ty) then (
    Ty.ill_typed
      "let: variable %a : @[%a@]@ and bounded term : %a@ should have same type"
      Var.pp v Ty.pp (Var.ty v) Ty.pp t.ty;
  );
  mk_ (Let (v,t,u)) u.ty

let bind ~ty b v t = mk_ (Bind(b,v,t)) ty

let fun_ v t =
  let ty = Ty.arrow (Var.ty v) t.ty in
  mk_ (Bind (Fun,v,t)) ty

let quant_ q v t =
  if not (Ty.equal t.ty Ty.prop) then (
    Ty.ill_typed
      "quantifier: bounded term : %a@ should have type prop"
      Ty.pp t.ty;
  );
  let ty = Ty.prop in
  mk_ (q v t) ty

let forall = quant_ (fun v t -> Bind (Forall,v,t))
let exists = quant_ (fun v t -> Bind (Exists,v,t))

let mu v t =
  if not (Ty.equal (Var.ty v) t.ty) then (
    Ty.ill_typed "mu-term: var has type %a,@ body %a"
      Ty.pp (Var.ty v) Ty.pp t.ty;
  );
  let ty = Ty.arrow (Var.ty v) t.ty in
  mk_ (Bind (Fun,v,t)) ty

let fun_l = List.fold_right fun_
let fun_a = Array.fold_right fun_
let forall_l = List.fold_right forall
let exists_l = List.fold_right exists

let eq a b =
  if not (Ty.equal a.ty b.ty) then (
    Ty.ill_typed "eq: `@[%a@]` and `@[%a@]` do not have the same type"
      pp_term a pp_term b;
  );
  mk_ (Binop (Eq,a,b)) Ty.prop

let check_prop_ t =
  if not (Ty.equal t.ty Ty.prop) then (
    Ty.ill_typed "expected prop, got `@[%a : %a@]`" pp_term t Ty.pp t.ty
  )

let binop op a b = mk_ (Binop (op, a, b)) Ty.prop
let binop_prop op a b =
  check_prop_ a; check_prop_ b;
  binop op a b

let and_ = binop_prop And
let or_ = binop_prop Or
let imply = binop_prop Imply

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
  | Tip

let string_of_syntax = function
  | Auto -> "auto"
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
    | K_select of Ty.t * select
    | K_var of var (* local *)

  and ty_kind =
    | K_data (* data type *)
    | K_uninterpreted (* uninterpreted type *)
    | K_prop
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
    | K_select (ty,s) ->
      Format.fprintf out "(@[select-%a-%d : %a@])"
        ID.pp s.select_cstor s.select_i Ty.pp ty
    | K_fun ty ->
      Format.fprintf out "(@[fun : %a@])" Ty.pp ty
    | K_var v ->
      Format.fprintf out "(@[var : %a@])" Ty.pp (Var.ty v)

  let pp out t =
    Format.fprintf out "ctx {@[%a@]}"
      Fmt.(iter ~sep:(return "@ ") @@ pair ID.pp pp_kind) (ID.Tbl.to_iter t.kinds)
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
  | A.Ty_bool -> Ty.prop, Ctx.K_ty Ctx.K_prop
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

and conv_term_aux ctx t : term = match t with
  | A.True -> true_
  | A.False -> false_
  | A.Const s ->
    let id = find_id_ ctx s in
    begin match Ctx.find_kind ctx id with
      | Ctx.K_var v -> var v
      | Ctx.K_fun ty
      | Ctx.K_cstor ty -> const id ty
      | Ctx.K_select _ -> errorf_ctx ctx "unapplied `select` not supported"
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
    let ty, _ty_k = conv_ty ctx ty in
    Ctx.with_var ctx v ty
      (fun var ->
         let body = conv_term ctx body in
         forall var body)
  | A.Exists ((v,ty), body) ->
    let ty, _ = conv_ty ctx ty in
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
  | A.Is_a (c,t) ->
    (* transform into [match t with c _ -> true | default -> false] *)
    let t = conv_term ctx t in
    let c = find_id_ ctx c in
    let all_cstors = Ctx.as_data ctx t.ty in
    let missing = List.rev_map fst all_cstors |> ID.Set.of_list |> ID.Set.remove c in
    begin match Ctx.find_kind ctx c with
      | Ctx.K_cstor ty ->
        let ty_args, _ = Ty.unfold ty in
        let vars = List.mapi (fun i ty -> Var.makef ~ty "x_%d" i) ty_args in
        match_l t [c, (vars,true_)] ~default:(Some (missing,false_))
      | _ -> errorf "expected %a to be a constructor" ID.pp c
    end
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
             if ID.Map.mem c cases then (
               errorf_ctx ctx "constructor %a occurs twice" ID.pp c;
             );
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
    (* check exhaustiveness *)
    let missing =
      all_cstors
      |> List.filter (fun (cstor,_) -> not (ID.Map.mem cstor cases))
      |> List.rev_map fst |> ID.Set.of_list
    in
    let cases, default = match default with
      | None ->
        if not @@ ID.Set.is_empty missing then (
          errorf_ctx ctx
            "missing cases in `@[%a@]`:@ {@[%a@]}"
            A.pp_term t (Util.pp_iter ID.pp) (ID.Set.to_iter missing);
        );
        cases, None
      | Some def_rhs when ID.Set.cardinal missing > ID.Map.cardinal cases ->
        (* keep [default], gives smaller explanations *)
        cases, Some (missing, def_rhs)
      | Some def_rhs ->
        (* complete explicitely *)
        List.fold_left
          (fun cases (cstor,ty_cstor) ->
             if ID.Map.mem cstor cases then cases
             else (
               let args, _ = Ty.unfold ty_cstor in
               let vars = List.mapi (fun i ty -> Var.makef ~ty "_%d" i) args in
               ID.Map.add cstor (vars, def_rhs) cases
             ))
          cases all_cstors, None
    in
    match_ lhs cases ~default
  | A.App (A.Const s, args) ->
    let id = find_id_ ctx s in
    let args = List.map (conv_term ctx) args in
    begin match Ctx.find_kind ctx id, args with
      | Ctx.K_var v, _ -> app (var v) args
      | Ctx.K_fun ty, _
      | Ctx.K_cstor ty, _ -> app (const id ty) args
      | Ctx.K_select (ty, sel), [arg] -> select sel arg ty
      | Ctx.K_select _, _ ->
        errorf_ctx ctx "select `%a`@ should be applied to exactly one arg"
          A.pp_term t
      | Ctx.K_ty _, _ ->
        errorf_ctx ctx "expected term, not type; got `%a`" ID.pp id
    end
  | A.App (f, args) ->
    let f = conv_term ctx f in
    let args = List.map (conv_term ctx) args in
    app f args
  | A.Asserting (t,g) ->
    let t = conv_term ctx t in
    let g = conv_term ctx g in
    asserting t g

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
             let selectors =
               List.map (fun (n,ty) -> n, conv_ty_fst ctx ty) ty_args
             in
             let ty_args = List.map snd selectors in
             (* declare cstor *)
             let ty_c = Ty.arrow_l ty_args data_ty in
             let id_c = Ctx.add_id ctx c (Ctx.K_cstor ty_c) in
             (* now declare selectors *)
             List.iteri
               (fun i (name_opt,ty) -> match name_opt with
                  | None -> ()
                  | Some select_str ->
                    (* declare this selector *)
                    let rec select_name = lazy
                      (Ctx.add_id ctx select_str
                         (Ctx.K_select (ty,
                            {select_name; select_cstor=id_c; select_i=i})))
                    in
                    ignore (Lazy.force select_name))
               selectors;
             (* return cstor *)
             id_c, ty_c
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
  | A.Stmt_goal {prove;vars;body=t} ->
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
         [Goal {prove;vars;body=t}])

and parse_file_exn ctx (syn:syntax) ~file : statement list =
  let syn = match syn with
    | Tip -> syn
    | Auto -> Tip
  in
  Log.debugf 2 (fun k->k "use syntax: %s" (string_of_syntax syn));
  let l = match syn with
    | Auto -> assert false
    | Tip ->
      (* delegate parsing to [Tip_parser] *)
      Smtlib_utils.V_2_6.parse_file_exn file
      |> CCList.filter_map A.Tip.conv_stmt
  in
  CCList.flat_map (conv_statement ctx syn) l

let parse ~include_dir ~file syn =
  let ctx = Ctx.create ~include_dir () in
  try Result.Ok (parse_file_exn ctx ~file syn)
  with e -> Result.Error (Printexc.to_string e)

let parse_stdin syn = match syn with
  | Auto -> errorf "impossible to guess input format with <stdin>"
  | Tip ->
    let ctx = Ctx.create ~include_dir:"." () in
    try
      Smtlib_utils.V_2_6.parse_chan_exn ~filename:"<stdin>" stdin
      |> CCList.filter_map A.Tip.conv_stmt
      |> CCList.flat_map (conv_statement ctx syn)
      |> CCResult.return
    with e -> Result.Error (Printexc.to_string e)

(** {2 Environment} *)

type env_entry =
  | E_uninterpreted_ty
  | E_uninterpreted_cst (* domain element *)
  | E_const of Ty.t
  | E_data of Ty.t ID.Map.t (* list of cstors *)
  | E_cstor of Ty.t (* datatype it belongs to *)
  | E_defined of Ty.t * term (* if defined *)

type env = {
  defs: env_entry ID.Map.t;
}
(** Environment with definitions and goals *)

let env_empty = {
  defs=ID.Map.empty;
}

let add_def id def env = { defs=ID.Map.add id def env.defs}

let env_add_statement env st =
  match st with
    | Data l ->
      List.fold_left
        (fun env {Ty.data_id; data_cstors} ->
           let map = add_def data_id (E_data data_cstors) env in
           ID.Map.fold
             (fun c_id c_ty map -> add_def c_id (E_cstor c_ty) map)
             data_cstors map)
        env l
    | TyDecl id -> add_def id E_uninterpreted_ty env
    | Decl (id,ty) -> add_def id (E_const ty) env
    | Define l ->
      List.fold_left
        (fun map (id,ty,def) -> add_def id (E_defined (ty,def)) map)
        env l
    | Goal _
    | Assert _ -> env

let env_of_statements seq =
  Iter.fold env_add_statement env_empty seq

let env_find_def env id =
  try Some (ID.Map.find id env.defs)
  with Not_found -> None

let env_add_def env id def = add_def id def env
