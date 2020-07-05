type t =
  | EmptyHole
  | Wild
  | Var of Err.t * string
  | Int of Err.t * int
  | Pair of Err.t * t * t
  | Inj of Err.t * InjSide.t * t
