exception UnImplemented
module Constraint = struct
  type t =
    | Truth | Falsity
    | And of t * t | Or of t * t
    | Inl of t | Inr of t
    | Pair of t * t
    | Num of int
    | NotNum of int
end

module IntSet = Set.Make(struct type t = int let compare = compare end)

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
  let (nums, not_nums) =
    List.fold_left 
      (fun (ns, not_ns) (c : Constraint.t) ->
        match c with
        | Num n -> (n::ns, not_ns)
        | NotNum n -> (ns, n::not_ns)
        | _ -> assert false
      )
      ([], [])
      cs
  in
  let (incon, num_set) =
    List.fold_left
      (fun (incon, num_set) n ->
        if incon then
          (incon, num_set)
        else
          if IntSet.mem n num_set then
            (true, num_set)
          else
            (false, IntSet.add n num_set)
      )
      (false, IntSet.empty)
      nums
  in
  if incon then
    incon
  else
    List.fold_left
      (fun incon n ->
        if incon then
          incon
        else
          IntSet.mem n num_set
      )
      false
      not_nums

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
