include Syntax
include Util
open List
open Constraint
open Z3
module Solver = Z3.Solver
module Symbol = Z3.Symbol
module Int = Z3.Arithmetic.Integer
module Sort = Z3.Sort
module Expr = Z3.Expr

exception Incon of string

let mk_new_ctx () =
  let cfg = [ ("model", "true"); ("proof", "false") ] in
  mk_context cfg

let ctx = ref @@ mk_new_ctx ()

let solver = ref @@ Solver.mk_solver !ctx None

let ctx_to_string () = Solver.to_string !solver

let reset () =
  ctx := mk_new_ctx ();
  solver := Solver.mk_solver !ctx None

(*
 * Z3 API for the current ctx
 *)
let sym s = Symbol.mk_string !ctx s

let mk_app f args = Expr.mk_app !ctx f args

let mk_int_sort () = Int.mk_sort !ctx

let mk_bool_sort () = Boolean.mk_sort !ctx

let mk_numeral_i i = Int.mk_numeral_i !ctx i

let mk_uninterpreted_s s = Sort.mk_uninterpreted_s !ctx s

let mk_const_s str sort = Expr.mk_const_s !ctx str sort

let mk_constructor_s a b c d e = Datatype.mk_constructor_s !ctx a b c d e

let mk_sort_s a b = Datatype.mk_sort_s !ctx a b

let mk_func_decl_s name arg_sorts res_sort =
  FuncDecl.mk_func_decl_s !ctx name arg_sorts res_sort

let mk_and conjs = Boolean.mk_and !ctx conjs

let mk_or conjs = Boolean.mk_or !ctx conjs

let mk_eq e1 e2 = Boolean.mk_eq !ctx e1 e2

let mk_gt e1 e2 = Arithmetic.mk_gt !ctx e1 e2

let mk_lt e1 e2 = Arithmetic.mk_lt !ctx e1 e2

let mk_ge e1 e2 = Arithmetic.mk_ge !ctx e1 e2

let mk_le e1 e2 = Arithmetic.mk_le !ctx e1 e2

let mk_not e = Boolean.mk_not !ctx e

let mk_true () = Boolean.mk_true !ctx

let mk_false () = Boolean.mk_false !ctx

let mk_ite e1 e2 e3 = Boolean.mk_ite !ctx e1 e2 e3

let mk_distinct es = Boolean.mk_distinct !ctx es

let mk_add es = Arithmetic.mk_add !ctx es

let mk_sub es = Arithmetic.mk_sub !ctx es

let mk_mul es = Arithmetic.mk_mul !ctx es

let _assert e = Solver.add !solver [ e ]

let _assert_all e = Solver.add !solver e

let push () = Solver.push !solver

let pop () = Solver.pop !solver 1

let check_sat () = Solver.check !solver []

let get_model () =
  match Solver.get_model !solver with
  | Some model -> model
  | None -> failwith "No model exists!"

let ( @=> ) e1 e2 = Boolean.mk_implies !ctx e1 e2

let ( @<=> ) e1 e2 = Boolean.mk_iff !ctx e1 e2

let ( @& ) e1 e2 = mk_and [ e1; e2 ]

let ( @| ) e1 e2 = mk_or [ e1; e2 ]

let ( @= ) e1 e2 = mk_eq e1 e2

let ( @< ) e1 e2 = mk_lt e1 e2

let ( @> ) e1 e2 = mk_gt e1 e2

let ( @>= ) e1 e2 = mk_ge e1 e2

let ( @<= ) e1 e2 = mk_le e1 e2

let ( @!= ) e1 e2 = mk_not (e1 @= e2)

let ( !@ ) e = mk_not e

let rec trans (var : string) (xi : t) : Expr.expr =
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

let solve_incon (xi : t) : bool =
  let c = trans "x" xi in
  let result = Solver.check !solver [ c ] in
  match result with
  | Solver.SATISFIABLE -> false
  | Solver.UNSATISFIABLE -> true
  | Solver.UNKNOWN -> raise (Incon "unknown")

let is_inconsistent_nums (xis : t list) : bool =
  let num_set, not_num_list =
    List.fold_left
      (fun (num_set, not_num_list) (xi : t) ->
        match xi with
        | Num n -> (NumSet.add n num_set, not_num_list)
        | NotNum n -> (num_set, n :: not_num_list)
        | _ -> assert false)
      (NumSet.empty, []) xis
  in
  if NumSet.cardinal num_set > 1 then true
  else
    List.fold_left
      (fun incon n -> if incon then incon else NumSet.mem n num_set)
      false not_num_list

let rec is_inconsistent ?(may = false) (xis : t list) : bool =
  match xis with
  | [] -> false
  | xi :: xis' -> (
      match xi with
      | Truth -> is_inconsistent ~may xis'
      | Falsity -> true
      | Unknown -> if may then true else is_inconsistent ~may xis'
      | And (xi_1, xi_2) -> is_inconsistent ~may (xi_1 :: xi_2 :: xis')
      | Or (xi_1, xi_2) ->
          is_inconsistent ~may (xi_1 :: xis')
          && is_inconsistent ~may (xi_2 :: xis')
      | Inl _ -> (
          if List.exists (function Inr _ -> true | _ -> false) xis then true
          else
            match
              List.partition (function Inl _ -> true | _ -> false) xis
            with
            | inls, [] ->
                is_inconsistent ~may
                  (List.map (function Inl xi -> xi | _ -> assert false) inls)
            | inls, other -> is_inconsistent ~may (other @ inls))
      | Inr _ -> (
          if List.exists (function Inl _ -> true | _ -> false) xis then true
          else
            match
              List.partition (function Inr _ -> true | _ -> false) xis
            with
            | inrs, [] ->
                is_inconsistent ~may
                  (List.map (function Inr xi -> xi | _ -> assert false) inrs)
            | inrs, other -> is_inconsistent ~may (other @ inrs))
      | Num _ | NotNum _ -> (
          match
            List.partition
              (function Num _ | NotNum _ -> true | _ -> false)
              xis
          with
          | ns, [] -> is_inconsistent_nums ns
          | ns, other -> is_inconsistent ~may (other @ ns))
      | Pair (_, _) -> (
          match List.partition (function Pair _ -> true | _ -> false) xis with
          | pairs, [] ->
              let xis_l, xis_r =
                List.fold_left
                  (fun (xis_l, xis_r) pair ->
                    let xi_l, xi_r =
                      match pair with
                      | Pair (xi_l, xi_r) -> (xi_l, xi_r)
                      | _ -> assert false
                    in
                    (xi_l :: xis_l, xi_r :: xis_r))
                  ([], []) pairs
              in
              is_inconsistent ~may xis_l || is_inconsistent ~may xis_r
          | pairs, other -> is_inconsistent ~may (other @ pairs)))

let is_redundant (xi_cur : t) (xi_pre : t) : bool =
  solve_incon (And (truify xi_cur, dual (falsify xi_pre)))
(* is_inconsistent ~may:false [ And (truify xi_cur, dual (falsify xi_pre)) ] *)

let is_exhaustive (xi : t) : bool = solve_incon (dual (truify xi))
(* is_inconsistent ~may:true [ dual (truify xi) ] *)

let%test "exhaustive1" = is_inconsistent [ Inl Truth; Inr Truth ] = true

let%test "exhaustive2" = is_inconsistent [ Inl Truth; Inr Unknown ] = true
