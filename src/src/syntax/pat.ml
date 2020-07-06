type t =
  | EmptyHole of Hole.t
  | NonEmptyHole of Hole.t * t
  | Wild
  | Var of Var.t
  | Num of int
  | Pair of t * t
  | Inj of InjSide.t * t
