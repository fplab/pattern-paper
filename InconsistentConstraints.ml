exception UnImplemented
module Constraint = struct
  type t =
    | Truth | Falsity
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
end

module NumSet = Set.Make(struct type t = int let compare = compare end)

let partition2 (pred1 : 'a -> bool) (pred2 : 'a -> bool) (cs : 'a list) : ('a list * 'a list) option =
  let f (acc : ('a list * 'a list) option) (c : 'a) =
    match acc with
    | None -> None
    | Some (trues, falses) ->
        if pred2 c then None
        else if pred1 c then
          Some (c::trues, falses)
        else 
          Some (trues, c::falses)
  in
  List.fold_left f (Some ([], [])) cs

let is_inconsistent_nums (cs : Constraint.t list) : bool =
  let (num_set, not_num_list) =
    List.fold_left 
      (fun (num_set, not_num_list) (c : Constraint.t) ->
        match c with
        | Num n -> (NumSet.add n num_set, not_num_list)
        | NotNum n -> (num_set, n::not_num_list)
        | _ -> assert false
      )
      (NumSet.empty, [])
      cs
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

let rec is_inconsistent (cs : Constraint.t list) : bool =
  match cs with
  | [] -> false
  | c::cs' -> (
    match c with
    | Truth -> is_inconsistent cs'
    | Falsity -> true
    | And (c1, c2) -> is_inconsistent (c1::c2::cs')
    | Or (c1, c2) -> is_inconsistent (c1::cs') && is_inconsistent (c2::cs')
    | Inl _ -> (
      match
        partition2
        (function Constraint.Inl _ -> true | _ -> false)
        (function Constraint.Inr _ -> true | _ -> false)
        cs
      with
      | None -> true
      | Some (inls, []) -> is_inconsistent (
        List.map (function Constraint.Inl c -> c | _ -> assert false) inls
      )
      | Some (inls, other) -> is_inconsistent (other @ inls)
    )
    | Inr _ -> (
      match
        partition2
        (function Constraint.Inr _ -> true | _ -> false)
        (function Constraint.Inl _ -> true | _ -> false)
        cs
      with
      | None -> true
      | Some (inrs, []) -> is_inconsistent (
        List.map (function Constraint.Inr c -> c | _ -> assert false) inrs
      )
      | Some (inrs, other) -> is_inconsistent (other @ inrs)
    )
    | Num n -> (
      match
        partition2
        (function Constraint.Num _ | Constraint.NotNum _ -> true | _ -> false)
        (function Constraint.Num n' -> (n != n') | Constraint.NotNum n' -> (n = n') | _ -> false)
        cs
      with
      | None -> true
      | Some (ns, []) -> is_inconsistent_nums ns
      | Some (ns, other) -> is_inconsistent (other @ ns)
    )
    | NotNum n -> (
      match
        partition2
        (function Constraint.Num _ | Constraint.NotNum _ -> true | _ -> false)
        (function Constraint.Num n' -> (n = n') | _ -> false)
        cs
      with
      | None -> true
      | Some (ns, []) -> is_inconsistent_nums ns
      | Some (ns, other) -> is_inconsistent (other @ ns)
    )
    | Pair (c1, c2) -> raise UnImplemented
  )

let is_redundant (xi' : Constraint.t) (xi : Constraint.t) : bool =
  is_inconsistent [Or (Constraint.dual xi', xi)]

let is_exhaustive (xi : Constraint.t) : bool =
  is_inconsistent [Constraint.dual xi]

let is_inconsistent_tests : (Constraint.t list * bool) list = [
  ( [Truth; Inl Truth; Inr Truth], true ) ;
  ( [Truth; Falsity], true ) ;
  ( [And (Inl Truth, Truth); Inr Truth], true ) ;
  ( [Or (Falsity, Truth)], false ) ;
  ( [Num 1; NotNum 2; NotNum 3], false ) ;
  ( [Or (Num 1, Num 3); And (NotNum 1, NotNum 3)], true ) ;
  (*
  ( [Pair (Inr Falsity, Truth)], true) ;
  *)
]

let run_tests =
  List.map
    (function (cs, result) -> if is_inconsistent cs = result then () else assert false)
    is_inconsistent_tests
  ;;
run_tests
