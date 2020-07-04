type t =
  | Truth | Falsity | Unknown
  | Num of int
  | NotNum of int
  | Unit
  | And of t * t | Or of t * t
  | Inl of t | Inr of t
  | Pair of t * t

let rec dual =
  function
  | Truth -> Falsity
  | Falsity -> Truth
  | Unknown -> Unknown
  | Num n -> NotNum n
  | NotNum n -> Num n
  | Unit -> Falsity
  | And (xi_1, xi_2) -> Or (dual xi_1, dual xi_2)
  | Or (xi_1, xi_2) -> And (dual xi_1, dual xi_2)
  | Inl xi -> Or (Inl (dual xi), Inr Truth)
  | Inr xi -> Or (Inr (dual xi), Inl Truth)
  | Pair (xi_1, xi_2) ->
    Or (
      Pair (xi_1, dual xi_2),
      Or (
        Pair (dual xi_1, xi_2),
        Pair (dual xi_1, dual xi_2)
      )
    )
