type t =
  | EmptyHole
  | Var of Err.t * string
  | Num of Err.t * int
  | Lam of Err.t * Pat.t * Typ.t * t
  | Ap of t * t
  | Pair of t * t
  | Inj of Err.t * InjSide.t * Typ.t * t
  | Match of Err.t * t * zrules
and zrules = ZRules of rules * rule * rules
and rules = Empty | Rules of rule * rules
and rule = Rule of Pat.t * t
(* TODO: mark redundant rule*)

let rec zrs_unzip = function
  | ZRules (Empty, r, rs) -> Rules (r, rs)
  | ZRules (Rules(r', rs'), r, rs) -> Rules (r', zrs_unzip (ZRules (rs', r, rs)))
