include Syntax

(* fault that shouldn't appear *)
type our_fault =
  | FreeHole of Hole.t
  | DupHole of Hole.t
  | FreeVar of Var.t
  | DupVar of Var.t
  | FunNotArrow
  | TypeIncon
  | BranchIncon of int
  | EmptyRules
  | TypeAnnIncon

(* fault that is handled by us *)
type their_fault =
  | Redundant of int
  | NonExhaustive
  | ScrutNotFinal

type t =
  | Our of our_fault
  | Their of their_fault
