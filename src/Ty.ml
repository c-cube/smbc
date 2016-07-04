
(* This file is free software. See file "license" for more details. *)

(** {1 Types} *)

type sexp = CCSexp.t
type 'a to_sexp = 'a -> sexp

(** {2 Base} *)

(* TODO hashconsing, physical equality, O(1) comparison *)

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

module S = CCSexp

let rec to_sexp = function
  | Prop -> S.atom "prop"
  | Const id -> S.atom (ID.to_string id)
  | Arrow (a,b) -> S.of_list [S.atom "->"; to_sexp a; to_sexp b]

let pp out t = CCSexpM.print out (to_sexp t)

(** {2 Datatypes} *)

type data = {
  data_id: ID.t;
  data_cstors: t ID.Map.t;
}


let data_to_sexp d =
  let cstors =
    ID.Map.fold
      (fun c ty acc -> S.of_list [ID.to_sexp c; to_sexp ty] :: acc)
      d.data_cstors []
  in
  S.of_list (ID.to_sexp d.data_id :: cstors)

exception Ill_typed of string

let ill_typed fmt =
  CCFormat.ksprintf
    ~f:(fun s -> raise (Ill_typed s))
    fmt
