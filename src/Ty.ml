
(* This file is free software. See file "license" for more details. *)

(** {1 Simple Types} *)

module S = CCSexp

type sexp = CCSexp.t
type 'a to_sexp = 'a -> sexp

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

let is_prop = function Prop -> true | _ -> false
let is_const = function (Const _) -> true | _ -> false
let is_arrow = function (Arrow (_,_)) -> true | _ -> false

let rec to_sexp = function
  | Prop -> S.atom "prop"
  | Const id -> S.atom (ID.to_string id)
  | Arrow _ as ty ->
    let args, ret = unfold ty in
    S.of_list (S.atom "->":: List.map to_sexp args @ [to_sexp ret])

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

exception Ill_typed of string

let () = Printexc.register_printer
    (function
      | Ill_typed msg -> Some ("ill-typed: " ^ msg)
      | _ -> None)

let ill_typed fmt =
  CCFormat.ksprintf
    ~f:(fun s -> raise (Ill_typed s))
    fmt
