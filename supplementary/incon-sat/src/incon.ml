open Constraint
open Solver

let rec trans (var : string) (xi : t) =
  match xi with
  | Truth -> mk_true ()
  | Unknown -> mk_true ()
  | Falsity -> mk_false ()
  | Num n -> mk_const_s var (mk_int_sort ()) @= mk_numeral_i n
  | NotNum n -> mk_const_s var (mk_int_sort ()) @!= mk_numeral_i n
  | And (xi_1, xi_2) -> trans var xi_1 @& trans var xi_2
  | Or (xi_1, xi_2) -> trans var xi_1 @| trans var xi_2
  | Inl xi -> mk_const_s var (mk_bool_sort ()) @& trans (var ^ "0") xi
  | Inr xi -> mk_not (mk_const_s var (mk_bool_sort ())) @& trans (var ^ "0") xi
  | Pair (xi_1, xi_2) -> trans (var ^ "l") xi_1 @& trans (var ^ "r") xi_2

let is_incon xi = not @@ is_satisfiable (trans "x" xi)

let is_redundant (xi_cur : t) (xi_pre : t) : bool =
  is_incon (And (truify xi_cur, dual (falsify xi_pre)))
(* is_inconsistent ~may:false [ And (truify xi_cur, dual (falsify xi_pre)) ] *)

let is_exhaustive (xi : t) : bool = is_incon (dual (truify xi))
(* is_inconsistent ~may:true [ dual (truify xi) ] *)

exception ReduceEmptyList

let list_reduce f = function
  | [] -> raise ReduceEmptyList
  | hd :: tl -> List.fold_left f hd tl

let cor x y = Or (x, y)

let disjunct : t list -> t = list_reduce cor

let%test "exhaustive1" =
  is_exhaustive @@ disjunct [ Inl Truth; Inr Truth ] = true

let%test "exhaustive2" =
  is_exhaustive @@ disjunct [ Inl Truth; Inr Unknown ] = true

let%test "redundant1" = is_redundant (Inl Truth) (Inl Truth) = true

let%test "redundant2" =
  is_redundant
    (disjunct [ Num 2; Unknown ])
    (disjunct [ Num 2; Num 3 ])
  = false

let%test "redundant3" =
  is_redundant
    (disjunct [ Num 2; Num 3 ])
    (disjunct [ Num 3; Num 4 ])
  = false
