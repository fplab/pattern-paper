type t =
  | Truth | Falsity | Unknown
  | Num of int
  | NotNum of int
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

let rec truify =
  function
  | Truth -> Truth
  | Falsity -> Falsity
  | Unknown -> Truth
  | Num n -> Num n
  | NotNum n -> NotNum n
  | And (xi_1, xi_2) -> And (truify xi_1, truify xi_2)
  | Or (xi_1, xi_2) -> Or (truify xi_1, truify xi_2)
  | Inl xi -> Inl (truify xi)
  | Inr xi -> Inr (truify xi)
  | Pair (xi_1, xi_2) -> Pair (truify xi_1, truify xi_2)

let rec falsify =
  function
  | Truth -> Truth
  | Falsity -> Falsity
  | Unknown -> Falsity
  | Num n -> Num n
  | NotNum n -> NotNum n
  | And (xi_1, xi_2) -> And (falsify xi_1, falsify xi_2)
  | Or (xi_1, xi_2) -> Or (falsify xi_1, falsify xi_2)
  | Inl xi -> Inl (falsify xi)
  | Inr xi -> Inr (falsify xi)
  | Pair (xi_1, xi_2) -> Pair (falsify xi_1, falsify xi_2)

