
(* This file is free software. See file "license" for more details. *)

(** {1 Typed Constant} *)

type 'term t = private {
  id: ID.t;
  kind: 'term kind;
}

(** The various kinds of constants *)
and 'term kind =
  | Const of Ty.t * 'term const_info
  | Cstor of Ty.t * Ty.data
  | Defined of Ty.t * 'term

and 'term const_info = {
  const_depth: int;
    (* refinement depth, used for iterative deepening *)
  const_parent: 'term t option;
    (* if const was created as argument of another const *)
  mutable const_cases : 'term list option;
    (* cover set (lazily evaluated) *)
}

(* TODO: replace Ty.data with something using Typed_cst so that
   there is no global environment *)

val make : ID.t -> 'term kind -> 'term t
val make_const : ?parent:'term t -> ID.t -> Ty.t -> 'term t
val make_cstor : ID.t -> Ty.t -> Ty.data -> _ t
val make_defined: ID.t -> Ty.t -> 'term -> 'term t

val id : _ t -> ID.t
val kind : 'term t -> 'term kind
val ty : _ t -> Ty.t

val ty_of_kind : _ kind -> Ty.t

val equal : _ t -> _ t -> bool
val compare : _ t -> _ t -> int
val hash : _ t -> int
val pp : _ t CCFormat.printer
