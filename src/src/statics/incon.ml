include Syntax
include Util
open Constraint

let is_inconsistent_nums (xis : t list) : bool =
  let (num_set, not_num_list) =
    List.fold_left 
      (fun (num_set, not_num_list) (xi : t) ->
         match xi with
         | Num n -> (NumSet.add n num_set, not_num_list)
         | NotNum n -> (num_set, n::not_num_list)
         | _ -> assert false
      )
      (NumSet.empty, [])
      xis
  in
  if NumSet.cardinal num_set > 1 then
    true
  else
    List.fold_left
      (fun incon n ->
         if incon then
           incon
         else
           NumSet.mem n num_set
      )
      false
      not_num_list

let rec is_inconsistent ?(may = false) (xis : t list) : bool =
  match xis with
  | [] -> false
  | xi::xis' -> (
      match xi with
      | Truth -> is_inconsistent ~may xis'
      | Falsity -> true
      | Unknown -> if may then true else (is_inconsistent ~may xis')
      | And (xi_1, xi_2) -> is_inconsistent ~may (xi_1::xi_2::xis')
      | Or (xi_1, xi_2) -> is_inconsistent ~may (xi_1::xis') && is_inconsistent ~may (xi_2::xis')
      | Inl _ -> 
        if List.exists
            (function Inr _ -> true | _ -> false)
            xis
        then
          true
        else (
          match
            List.partition
              (function Inl _ -> true | _ -> false)
              xis
          with
          | (inls, []) -> is_inconsistent ~may (
              List.map (function Inl xi -> xi | _ -> assert false) inls
            )
          | (inls, other) -> is_inconsistent ~may (other @ inls)
        )
      | Inr _ -> 
        if List.exists
            (function Inl _ -> true | _ -> false)
            xis
        then
          true
        else (
          match
            List.partition
              (function Inr _ -> true | _ -> false)
              xis
          with
          | (inrs, []) -> is_inconsistent ~may (
              List.map (function Inr xi -> xi | _ -> assert false) inrs
            )
          | (inrs, other) -> is_inconsistent ~may (other @ inrs)
        )
      | Num _
      | NotNum _ -> (
          match
            List.partition
              (function Num _ | NotNum _ -> true | _ -> false)
              xis
          with
          | (ns, []) -> is_inconsistent_nums ns
          | (ns, other) -> is_inconsistent ~may (other @ ns)
        )
      | Pair (_, _) -> (
          match
            List.partition
              (function Pair _ -> true | _ -> false)
              xis
          with
          | (pairs, []) ->
            let (xis_l, xis_r) =
              List.fold_left
                (fun (xis_l, xis_r) pair ->
                   let (xi_l, xi_r) =
                     match pair with
                     | Pair (xi_l, xi_r) -> (xi_l, xi_r)
                     | _ -> assert false
                   in (xi_l::xis_l, xi_r::xis_r)
                )
                ([], [])
                pairs
            in (is_inconsistent ~may xis_l) || (is_inconsistent ~may xis_r)
          | (pairs, other) ->
            is_inconsistent ~may (other @ pairs)
        )
    )

let is_redundant (xi_cur : t) (xi_pre : t) : bool =
  is_inconsistent ~may:false [And (truify xi_cur, dual (falsify xi_pre))]

let is_exhaustive (xi : t) : bool =
  is_inconsistent ~may:true [dual (truify xi)]

let%test "exhaustive1" =
  is_inconsistent [Inl Truth; Inr Truth] = true
let%test "exhaustive2" =
  is_inconsistent [Inl Truth; Inr Unknown] = true
