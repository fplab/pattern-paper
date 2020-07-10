include Syntax

exception DuplicateVarInPat of Var.t

type t = (Var.t * Typ.t) List.t 

let empty = []

let is_empty =
  function
  | [] -> true
  | _::_ -> false

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

let rec drop x ctx =
  match ctx with
  | [] -> ctx
  | (y, elt)::ctx' -> 
    if Var.eq x y then
      ctx'
    else
      (y, elt)::(drop x ctx')

let extend ctx (x, elt) = (x, elt)::(drop x ctx)

let extend_opt ctx (x, elt) = 
  if contains x ctx then
    None
  else
    Some ((x, elt)::ctx)

let strict_extend ctx (x, elt) =
  if contains x ctx then
    raise (DuplicateVarInPat x)
  else
    (x, elt)::ctx

let union ctx1 ctx2 = List.fold_left extend ctx2 ctx1

let strict_union ctx1 ctx2 = List.fold_left strict_extend ctx2 ctx1

