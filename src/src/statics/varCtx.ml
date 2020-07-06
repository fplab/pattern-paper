include Syntax

type t = (Var.t * Typ.t) List.t 

let empty = []

let is_empty =
  function
  | [] -> true
  | _::_ -> false

let rec drop x ctx =
  match ctx with
  | [] -> ctx
  | (y, elt)::ctx' -> 
    if Var.eq x y then
      ctx'
    else
      (y, elt)::(drop x ctx')

let extend ctx (x, elt) = (x, elt)::(drop x ctx)


let union ctx1 ctx2 = List.fold_left extend ctx2 ctx1

let rec lookup x ctx =
  match ctx with
  | [] -> None
  | (y, elt)::ctx' ->
    if Var.eq x y then
      Some(elt)
    else
      lookup x ctx'


let contains x ctx =
  match (lookup x ctx) with
  | Some(_) -> true
  | None -> false
