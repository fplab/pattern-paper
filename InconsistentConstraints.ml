module Constraint = struct
  type t =
    | Truth | Falsity
    | And of t * t | Or of t * t
    | Inl of t | Inr of t
    | Pair of t * t
end

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

let rec is_inconsistent (cs : Constraint.t list) : bool =
  match cs with
  | [] -> false
  | c::cs' -> (
    match c with
    | Truth -> is_inconsistent cs'
    | Falsity -> false
    | And (c1, c2) -> is_inconsistent (c1::c2::cs')
    | Or (c1, c2) -> is_inconsistent (c1::cs') && is_inconsistent (c2::cs')
    | Inl _ -> (
      match
        partition2
        (function Constraint.Inl _ -> true | _ -> false)
        (function Constraint.Inr _ -> true | _ -> false)
        cs
      with
      | None -> false
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
      | None -> false
      | Some (inrs, []) -> is_inconsistent (
        List.map (function Constraint.Inr c -> c | _ -> assert false) inrs
      )
      | Some (inrs, other) -> is_inconsistent (other @ inrs)
    )
    | Pair (c1, c2) -> is_inconsistent (c1::cs') || is_inconsistent (c2::cs')
  )

let is_inconsistent_tests : (Constraint.t list * bool) list = [
  ( [Inl Truth; Inr Truth; Truth], true ) ;
  ( [Truth; Falsity], false ) ;
  ( [And (Inl Truth, Truth); Inr Truth], false ) ;
  ( [Or (Falsity, Truth)], false ) ;
  ( [Pair (Inr Falsity, Truth)], true) ;
]
