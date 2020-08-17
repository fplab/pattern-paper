include Util
include Syntax
include Dynamics
include Seq

exception Unimplemented

exception Error of Err.t

(*TODO change option to different error*)
let rec syn_exp (gamma: VarCtx.t) (delta: HoleCtx.t) : (Exp.t -> Typ.t) =
  function
  | EmptyHole h -> (
      match HoleCtx.find_opt h delta with
      | Some (_sort, typ) -> typ
      | None -> raise (Error (Our (FreeHole h)))
    )
  | NonEmptyHole (h, e) -> 
    let _ = syn_exp gamma delta e in (
      match HoleCtx.find_opt h delta with
      | Some (_sort, typ) -> typ
      | None -> raise (Error (Our (FreeHole h)))
    )
  | Var x -> (
      match VarCtx.lookup x gamma with
      | Some typ -> typ
      | None -> raise (Error (Our (FreeVar x)))
    )
  | Num _ -> Num
  | Lam (x, typ, exp) ->
    let gamma = VarCtx.extend gamma (x, typ) in
    syn_exp gamma delta exp
  | Ap (f, exp) -> (
      match syn_exp gamma delta f with
      | Arrow (typ1, typ2) ->
        let typ1' = syn_exp gamma delta exp in
        if typ1 == typ1' then
          typ2
        else
          raise (Error (Our (TypeIncon)))
      | _ -> raise (Error (Our (FunNotArrow)))
    )
  | Pair (e1, e2) ->
    let (typ1, typ2) = (
      syn_exp gamma delta e1,
      syn_exp gamma delta e2
    ) in
    Prod (typ1, typ2)
  | Inj (side, typ2, e) ->
    let typ1 = syn_exp gamma delta e in (
      match side with
      | InjSide.L -> Sum (typ1, typ2)
      | InjSide.R -> Sum (typ2, typ1)
    )
  | Match (scrut, zrules) -> (
      match zrules with
      | ZRules ([], r, rs) -> 
        let typ = syn_exp gamma delta scrut in
        let  (_, xi, typ') =
          syn_rules
            gamma delta
            (r::rs) typ Constraint.Falsity
        in
        if Incon.is_exhaustive xi then
          typ'
        else 
          raise (Error (Their (NonExhaustive)))
      | ZRules (rs_pre, r, rs_post) ->
        let typ = syn_exp gamma delta scrut in
        if not (Eval.is_final scrut) then 
          raise (Error (Our (ScrutNotFinal)))
        else
          let (count_pre, xi_pre, typ') =
            syn_rules
              gamma delta
              rs_pre typ Constraint.Falsity
          in
          (* TODO check if e mustn't satisfy xi_pre *)
          let (_, xi_rest, typ'') =
            syn_rules
              gamma delta
              ~index:(count_pre)
              (r::rs_post) typ xi_pre
          in
          if typ' <> typ'' then
            raise (Error (Our (BranchIncon (count_pre))))
          else if not (Incon.is_exhaustive (Constraint.Or (xi_pre, xi_rest))) then
            raise (Error (Their (NonExhaustive)))
          else
            typ'
    )
and syn_rules gamma delta ?(index=1) rules typ xi_pre : (int * Constraint.t * Typ.t) =
  match 
    rules
    |> List.map 
      (fun rule -> syn_rule gamma delta rule typ)
  with
  | [] -> raise (Error (Our (EmptyRules))) 
  | (xi_r, typ')::xi_typ_s -> 
    if Incon.is_redundant xi_r xi_pre then
      raise (Error (Their (Redundant index)))
    else
      List.fold_left (
        fun (i, xi_pre, typ'_last) (xi_r, typ') ->
          if Incon.is_redundant xi_r xi_pre then
            raise (Error (Their (Redundant i)))
          else if typ'_last <> typ' then
            raise (Error (Our (BranchIncon index)))
          else
            (i + 1, Constraint.Or (xi_pre, xi_r), typ')
      )
        (index + 1, Constraint.Or (xi_pre, xi_r), typ')
        xi_typ_s
and syn_rule gamma delta (Exp.Rule (pat, exp)) typ : (Constraint.t * Typ.t) =
  let (xi, gamma', delta') = ana_pat pat typ in
  let typ' =
    try
      syn_exp
        (VarCtx.union gamma gamma') 
        (HoleCtx.strict_union delta delta') 
        exp
    with
    | VarCtx.DuplicateVarInPat x ->
      raise (Error (Our (DupVar x)))
    | HoleCtx.DuplicateHoleName h ->
      raise (Error (Our (DupHole h)))
  in (xi, typ')
and ana_pat (pat: Pat.t) (typ: Typ.t) : (Constraint.t * VarCtx.t * HoleCtx.t) =
  match (pat, typ) with
  | (EmptyHole h, typ) -> (
      Unknown,
      VarCtx.empty,
      HoleCtx.add h (HoleCtx.PatHole, typ) HoleCtx.empty
    )
  | (NonEmptyHole (h, typ', p), typ) -> 
    let (_xi, ctx, delta) = ana_pat p typ' in
    (Constraint.Unknown, ctx, HoleCtx.add h (HoleCtx.PatHole, typ) delta)
  | (Wild, _typ) -> (Truth, VarCtx.empty, HoleCtx.empty)
  | (Var x, typ) -> (Truth, [(x, typ)], HoleCtx.empty)
  | (Num n, Num) -> (Num n, VarCtx.empty, HoleCtx.empty)
  | (Inj (L, p), Sum (typ1, _typ2)) ->
    let (xi, gamma, delta) = ana_pat p typ1 in
    (Constraint.Inl xi, gamma, delta)
  | (Inj (R, p), Sum (_typ1, typ2)) ->
    let (xi, gamma, delta) = ana_pat p typ2 in
    (Constraint.Inr xi, gamma, delta)
  | (Pair (p1, p2), Prod (typ1, typ2)) -> (
      let
        ((xi1, gamma1, delta1), (xi2, gamma2, delta2)) =
        ((ana_pat p1 typ1), (ana_pat p2 typ2))
      in
      try
        (Constraint.Pair (xi1, xi2),
         VarCtx.strict_union gamma1 gamma2,
         HoleCtx.strict_union delta1 delta2)
      with
      | VarCtx.DuplicateVarInPat x ->
        raise (Error (Our (DupVar x)))
      | HoleCtx.DuplicateHoleName h ->
        raise (Error (Our (DupHole h)))
    )
  | _ -> raise (Error (Our (TypeAnnIncon)))

let syn gamma delta exp : unit =
  try let _ = syn_exp gamma delta exp in () with
  | Error (Our fault) -> (
      match fault with
      | FreeHole h -> Printf.printf "Free hole %s\n" (Hole.to_string h)
      | DupHole h -> Printf.printf "Duplicate hole %s\n" (Hole.to_string h)
      | FreeVar x -> Printf.printf "Free variable %s\n" (Var.to_string x)
      | DupVar x -> Printf.printf "Duplicate variable %s in a pattern\n" (Var.to_string x)
      | FunNotArrow -> Printf.printf "A non-arrow-type expression is used like a function\n"
      | TypeIncon -> Printf.printf "Type inconsistency occurs\n"
      | BranchIncon i -> Printf.printf "Branch %d breaks the consistency\n" i
      | EmptyRules -> Printf.printf "Match expression should at least have one rule\n"
      | TypeAnnIncon -> Printf.printf "The annotated type is inconsistent with the pattern\n"
      | ScrutNotFinal -> Printf.printf "The scrutinee of intermediate match expressions must be final\n"
    )
  | Error (Their fault) -> (
      match fault with
      | Redundant i -> Printf.printf "Redundant rule %d\n" i
      | NonExhaustive -> Printf.printf "The match expression mustn't be exhaustive\n"
    )

let%expect_test "[no-pat-hole]well-typed"=
  syn VarCtx.empty (HoleCtx.singleton 1 (HoleCtx.ExpHole, Typ.Num)) (
    Match (
      Pair (Inj(L, Num, EmptyHole 1), Num 2),
      ZRules (
        [],
        Rule (Pair (Inj(R, Var "x"), Wild), Var "x"),
        [Rule (Pair (Wild, Var "x"), Var "x")]
      )
    )
  );
  syn VarCtx.empty (HoleCtx.singleton 1 (HoleCtx.ExpHole, Typ.Num)) (
    Match (
      Pair (Inj(L, Num, EmptyHole 1), Num 2),
      ZRules (
        [],
        Rule (Pair (Inj(R, Num 0), Var "x"), Var "x"),
        [
          Rule (Pair (Inj(R, Num 1), Var "x"), Var "x");
          Rule (Pair (Wild, Var "x"), Var "x")
        ]
      )
    )
  );
  syn VarCtx.empty (HoleCtx.singleton 1 (HoleCtx.ExpHole, Typ.Num)) (
    Match (
      Pair (Inj(L, Num, EmptyHole 1), Num 2),
      ZRules (
        [],
        Rule (Pair (Inj(R, Num 0), Var "x"), Var "x"),
        [
          Rule (Pair (Inj(R, Num 1), Var "x"), Var "x");
          Rule (Wild, Num 3)
        ]
      )
    )
  );
  [%expect{| |}]

let%expect_test "[no-pat-hole]not-exhaustive"=
  syn VarCtx.empty (HoleCtx.singleton 1 (HoleCtx.ExpHole, Typ.Num)) (
    Match (
      Pair (Inj(L, Num, EmptyHole 1), Num 2),
      ZRules (
        [],
        Rule (Pair (Inj(R, Var "x"), Wild), Var "x"),
        [Rule (Pair (Inj(L, Var "x"), Num 2), Var "x")]
      )
    )
  );
  syn VarCtx.empty (HoleCtx.singleton 1 (HoleCtx.ExpHole, Typ.Num)) (
    Match (
      Pair (Inj(L, Num, EmptyHole 1), Num 2),
      ZRules (
        [],
        Rule (Pair (Inj(R, Num 0), Var "x"), Var "x"),
        [
          Rule (Pair (Inj(L, Var "x"), Num 1), Var "x");
          Rule (Pair (Inj(L, Num 1), Var "x"), Var "x")
        ]
      )
    )
  ); 
  syn VarCtx.empty (HoleCtx.singleton 1 (HoleCtx.ExpHole, Typ.Num)) (
    Match (
      Pair (Inj(L, Num, Num 0), Num 2),
      ZRules (
        [],
        Rule (Pair (Inj(R, Num 0), Var "x"), EmptyHole 1),
        [
          Rule (Pair (Wild, Num 1), Num 1);
          Rule (Pair (Inj(L, Num 1), Wild), Num 2)
        ]
      )
    )
  );
  syn VarCtx.empty HoleCtx.empty (
    Match (
      Pair (Num 1, Num 2),
      ZRules (
        [],
        Rule (Pair (Num 2, Num 2), Num 1),
        [
          Rule (Pair (Num 1, Wild), Num 1);
        ]
      )
    )
  );
  [%expect{|
    The match expression mustn't be exhaustive
    The match expression mustn't be exhaustive
    The match expression mustn't be exhaustive
    The match expression mustn't be exhaustive |}]

let%expect_test "[no-pat-hole]redundant"=
  syn (VarCtx.singleton "x" Typ.Num) (HoleCtx.singleton 1 (HoleCtx.ExpHole, Typ.Num)) (
    Match (
      Pair (Inj(L, Num, EmptyHole 1), Num 2),
      ZRules (
        [],
        Rule (Pair (Inj(R, Num 2), Var "x"), Var "x"), (* (inr(2), x) *)
        [
          Rule (Pair (Inj(R, Var "x"), Num 3), Var "x"); (* (inr(x), 3) *)
          Rule (Pair (Inj(L, Var "x"), Num 2), Var "x");
          Rule (Pair (Inj(R, Num 2), Num 3), Var "x"); (* (inr(2), 3) *)
        ]
      )
    )
  );
  syn VarCtx.empty (HoleCtx.singleton 1 (HoleCtx.ExpHole, Typ.Num)) (
    Match (
      Pair (Inj(L, Num, EmptyHole 1), Num 2),
      ZRules (
        [],
        Rule (Pair (Inj(R, Var "x"), Num 1), Var "x"),
        [
          Rule (Pair (Inj(L, Var "x"), Num 1), Var "x");
          Rule (Pair (Var "x", Num 1), Num 0);
          Rule (Pair (Wild, Var "x"), Var "x")
        ]
      )
    )
  );
  syn VarCtx.empty (HoleCtx.singleton 1 (HoleCtx.ExpHole, Typ.Num)) (
    Match (
      Pair (Inj(L, Num, EmptyHole 1), Num 2),
      ZRules (
        [],
        Rule (Pair (Var "x", Num 1), Num 1),
        [
          Rule (Pair (Inj(L, Var "x"), Var "z"), Var "x");
          Rule (Pair (Inj(R, Var "y"), Wild), Num 0);
          Rule (Pair (Wild, Var "x"), Var "x")
        ]
      )
    )
  );
  syn VarCtx.empty (HoleCtx.singleton 1 (HoleCtx.ExpHole, Typ.Num)) (
    Match (
      Pair (Inj(L, Num, EmptyHole 1), Num 2),
      ZRules (
        [],
        Rule (Pair (Var "x", Num 1), Num 1),
        [
          Rule (Wild, Num 0);
          Rule (Pair (Inj(R, Var "y"), Wild), Num 0);
          Rule (Pair (Wild, Var "x"), Var "x")
        ]
      )
    )
  ); 
  [%expect{|
    Redundant rule 4
    Redundant rule 3
    Redundant rule 4
    Redundant rule 3 |}]

let%expect_test "[pat-hole]well-typed"=
  syn
    (VarCtx.singleton "x" Typ.Num)
    (HoleCtx.singleton 1 (HoleCtx.ExpHole, Typ.Num)) (
    Match (
      Pair (Inj(L, Num, EmptyHole 1), Num 2),
      ZRules (
        [],
        Rule (Pair (Inj(R, Num 2), Var "x"), Var "x"), (* (inr(2), x) *)
        [
          Rule (Pair (Inj(R, Var "x"), Num 3), Var "x"); (* (inr(x), 3) *)
          Rule (Pair (Inj(L, Var "x"), EmptyHole 4), Var "x");
          Rule (Pair (Inj(R, EmptyHole 2), EmptyHole 3), Var "x"); (* (inr(hole), hole) *)
        ]
      )
    )
  );
  syn VarCtx.empty (HoleCtx.singleton 1 (HoleCtx.ExpHole, Typ.Num)) (
    Match (
      Pair (Inj(L, Num, EmptyHole 1), Num 2),
      ZRules (
        [],
        Rule (Pair (Inj(R, Var "x"), Num 1), Var "x"),
        [
          Rule (Pair (Inj(L, Var "x"), Num 1), Var "x");
          Rule (Pair (Var "x", EmptyHole 2), Num 0);
          Rule (Pair (Wild, Var "x"), Var "x")
        ]
      )
    )
  ); 
  syn
    (VarCtx.singleton "x" Typ.Num) HoleCtx.empty (
    Match (
      Pair (Inj(L, Num, Num 1), Num 2),
      ZRules (
        [],
        Rule (Pair (Inj(R, Num 1), Num 1), Var "x"),
        [
          Rule (Pair (Inj(R, Var "x"),
               (NonEmptyHole (3, Prod(Num, Num), Pair(Num 1, Num 2)))), Var "x");
          Rule (Pair (Inj(L, Var "y"), Var "z"), Var "x");
        ]
      )
    )
  );
  [%expect{| |}]

let%expect_test "[pat-hole]not-exhaustive"=
  syn
    (VarCtx.singleton "x" Typ.Num)
    (HoleCtx.singleton 1 (HoleCtx.ExpHole, Typ.Num)) (
    Match (
      Pair (Num 1, Num 2),
      ZRules (
        [],
          Rule (Pair (Num 2, EmptyHole 3), Var "x"),
        [
        ]
      )
    )
  );
  syn
    (VarCtx.singleton "x" Typ.Num)
    (HoleCtx.singleton 1 (HoleCtx.ExpHole, Typ.Num)) (
    Match (
      Pair (Inj(L, Num, EmptyHole 1), Num 2),
      ZRules (
        [],
        Rule (Pair (Inj(R, EmptyHole 2), Var "x"), Var "x"), (* (inr(2), x) *)
        [
          Rule (Pair (Inj(R, Var "x"), EmptyHole 3), Var "x"); (* (inr(x), 3) *)
          Rule (Pair (Inj(L, Num 2), Var "x"), Var "x");
        ]
      )
    )
  );
  syn
    (VarCtx.singleton "x" Typ.Num)
    (HoleCtx.singleton 1 (HoleCtx.ExpHole, Typ.Num)) (
    Match (
      Pair (Inj(L, Num, EmptyHole 1), Num 2),
      ZRules (
        [],
        Rule (Pair (Inj(R, EmptyHole 2), Var "x"), Var "x"), (* (inr(2), x) *)
        [
          Rule (Pair (Inj(R, Var "x"), EmptyHole 3), Var "x"); (* (inr(x), 3) *)
          Rule (Pair (Inj(L, Num 2), EmptyHole 4), Var "x"); (* If this and rule below are flipped, redundant*)
          Rule (Pair (Inj(L, Num 2), Var "x"), Var "x");
        ]
      )
    )
  );
  [%expect{|
    The match expression mustn't be exhaustive
    The match expression mustn't be exhaustive
    The match expression mustn't be exhaustive |}]


let%expect_test "[pat-hole]redundant"=
  syn
    (VarCtx.singleton "x" Typ.Num)
    (HoleCtx.singleton 1 (HoleCtx.ExpHole, Typ.Num)) (
    Match (
      Pair (Inj(L, Num, EmptyHole 1), Num 2),
      ZRules (
        [],
        Rule (Pair (Inj(R, Num 2), Var "x"), Var "x"), (* (inr(2), x) *)
        [
          Rule (Pair (Inj(R, Var "x"), Num 3), Var "x"); (* (inr(x), 3) *)
          Rule (Pair (Inj(L, Var "x"), Num 2), Var "x");
          Rule (Pair (Inj(R, EmptyHole 2), Num 3), Var "x"); (* (inr(hole), 3) *)
        ]
      )
    )
  );
  syn VarCtx.empty (HoleCtx.singleton 1 (HoleCtx.ExpHole, Typ.Num)) (
    Match (
      Pair (Inj(L, Num, EmptyHole 1), Num 2),
      ZRules (
        [],
        Rule (Pair (Inj(R, Var "x"), Num 1), Var "x"),
        [
          Rule (Pair (Inj(L, Var "x"), Num 1), Var "x");
          Rule (Pair (EmptyHole 2, Num 1), Num 0);
          Rule (Pair (Wild, Var "x"), Var "x")
        ]
      )
    )
  ); 
  syn
    (VarCtx.singleton "x" Typ.Num)
    (HoleCtx.singleton 1 (HoleCtx.ExpHole, Typ.Num)) (
    Match (
      Pair (Inj(L, Num, EmptyHole 1), Num 2),
      ZRules (
        [],
        Rule (Pair (Inj(R, EmptyHole 2), Var "x"), Var "x"), (* (inr(2), x) *)
        [
          Rule (Pair (Inj(R, Var "x"), EmptyHole 3), Var "x"); (* (inr(x), 3) *)
          Rule (Pair (Inj(L, Num 2), Var "x"), Var "x"); (* If this and rule below are flipped, not exhaustive*)
          Rule (Pair (Inj(L, Num 2), EmptyHole 4), Var "x");
        ]
      )
    )
  );
  [%expect{|
    Redundant rule 4
    Redundant rule 3
    Redundant rule 4 |}]
