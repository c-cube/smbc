
(* This file is free software. See file "license" for more details. *)

(** {1 Typed Constant} *)

type 'term t = {
  id: ID.t;
  kind: 'term kind;
}

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


let id t = t.id
let kind t = t.kind

let ty_of_kind = function
  | Defined (ty, _)
  | Const (ty, _)
  | Cstor (ty,_) -> ty

let ty t = ty_of_kind t.kind

let make id kind = {id; kind}
let make_cstor id ty data = make id (Cstor (ty,data))
let make_defined id ty t = make id (Defined (ty, t))

let make_const ?parent id ty =
  let info = match parent with
    | None -> { const_depth=0; const_parent=None; const_cases=None }
    | Some p ->
      let depth = match p.kind with
        | Const (_, i) -> i.const_depth + 1
        | _ -> invalid_arg "make_const: parent should be a constant"
      in
      { const_depth=depth; const_parent=Some p; const_cases=None }
  in
  make id (Const (ty, info))

let equal a b = ID.equal a.id b.id
let compare a b = ID.compare a.id b.id
let hash t = ID.hash t.id
let pp out a = ID.pp out a.id
