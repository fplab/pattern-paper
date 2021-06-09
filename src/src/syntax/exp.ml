type t =
  | EmptyHole of Hole.t
  | NonEmptyHole of Hole.t * t
  | Var of Var.t
  | Num of int
  | Lam of Var.t * Typ.t * t
  | Ap of t * t
  | Pair of t * t
  | Inj of InjSide.t * Typ.t * t
  | Match of t * zrules

and zrules = ZRules of rules * rule * rules

and rules = rule List.t

and rule = Rule of Pat.t * t
(* TODO: mark redundant rule*)

let rec rm_pointer = function
  | ZRules ([], r, rs) -> r :: rs
  | ZRules (r' :: rs', r, rs) -> r' :: rm_pointer (ZRules (rs', r, rs))
