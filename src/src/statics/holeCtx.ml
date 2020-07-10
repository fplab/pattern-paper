include Syntax
include Util
include IntMap

exception DuplicateHoleName

type hole_sort = ExpHole | PatHole

type t = (hole_sort * Typ.t) IntMap.t

let union delta delta' =
  union
    (fun _key _bind _bind' -> raise DuplicateHoleName)
    delta
    delta'
