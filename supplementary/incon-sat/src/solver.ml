open Z3
module Int = Arithmetic.Integer

exception Z3Unknown

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

let is_satisfiable c : bool =
  let result = Solver.check !solver [ c ] in
  match result with
  | Solver.SATISFIABLE -> true
  | Solver.UNSATISFIABLE -> false
  | Solver.UNKNOWN -> raise Z3Unknown
