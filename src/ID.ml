
(* This file is free software. See file "license" for more details. *)

type t = {
  id: int;
  name: string;
}

let make =
  let n = ref 0 in
  fun name ->
    let x = { id= !n; name; } in
    incr n;
    x

let copy {name;_} = make name

let to_string id = id.name
let to_sexp id = CCSexp.atom id.name

let equal a b = a.id=b.id
let compare a b = CCOrd.int_ a.id b.id
let hash a = Hash.int a.id
let pp out a = Format.fprintf out "%s/%d" a.name a.id
let pp_name out a = CCFormat.string out a.name

module AsKey = struct
  type t_ = t
  type t = t_
  let equal = equal
  let compare = compare
end

module Map = CCMap.Make(AsKey)
module Set = CCSet.Make(AsKey)
