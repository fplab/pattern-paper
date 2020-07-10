include Syntax
include Util
include IntMap

exception DuplicateHoleName of Hole.t

type hole_sort = ExpHole | PatHole

type t = (hole_sort * Typ.t) IntMap.t

let strict_union delta delta' =
  union
    (fun h _bind _bind' -> raise (DuplicateHoleName h))
    delta
    delta'
