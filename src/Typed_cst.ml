
(* This file is free software. See file "license" for more details. *)

(** {1 Typed Constant} *)

type kind =
  | Const of Ty.t
  | Cstor of Ty.t * Ty.data
  (* TODO: defined function (how? terms are not defined here) *)

type t = {
  id: ID.t;
  kind: kind;
}

let id t = t.id
let kind t = t.kind
let ty t = match t.kind with
  | Const ty
  | Cstor (ty,_) -> ty

(* TODO: also, pointer to the definition/declaration/datatype
   to get rid of environment *)

let make id kind = {id; kind}
let make_const id ty = make id (Const ty)
let make_cstor id ty data = make id (Cstor (ty,data))

let equal a b = ID.equal a.id b.id
let compare a b = ID.compare a.id b.id
let hash t = ID.hash t.id
let pp out a = ID.pp out a.id
