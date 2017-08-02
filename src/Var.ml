
(* This file is free software. See file "license" for more details. *)

(** {1 Named Variables} *)

module S = CCSexp

type sexp = CCSexp.t
type 'a to_sexp = 'a -> sexp

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
let compare a b = ID.compare a.id b.id
let hash a = ID.hash a.id
let pp out v = ID.pp out v.id
let to_sexp v = S.atom (ID.to_string_full v.id)
(* let Var.to_sexp v = ID.to_sexp v.Var.id *)
let to_sexp_typed f v = S.of_list [to_sexp v; f v.ty]
