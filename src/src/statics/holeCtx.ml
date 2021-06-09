include Syntax
include Util
include IntMap

exception DuplicateHoleName of Hole.t

type hole_sort = ExpHole | PatHole

type t = (hole_sort * Typ.t) IntMap.t

let strict_union delta delta' =
  union (fun h _bind _bind' -> raise (DuplicateHoleName h)) delta delta'

let of_list ls = List.fold_left (fun (ctx : t) (h, a) -> add h a ctx) empty ls
