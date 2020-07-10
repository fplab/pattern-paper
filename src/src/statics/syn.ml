include Util
include Syntax
include Dynamics

exception Unimplemented

(*TODO change option to different error*)
let rec syn_exp (gamma: VarCtx.t) (delta: HoleCtx.t) : (Exp.t -> Typ.t Option.t) =
  function
  | EmptyHole h -> (HoleCtx.find_opt h delta)
                   |> (Option.map (fun (_sort, typ) -> typ))
  | NonEmptyHole (h, e) -> 
    if (syn_exp gamma delta e) |> Option.is_some
    then
      (HoleCtx.find_opt h delta)
      |> (Option.map (fun (_sort, typ) -> typ))
    else None
  | Var x -> VarCtx.lookup x gamma
  | Num _ -> Some Num
  | Lam (x, typ, exp) ->
    let gamma = VarCtx.extend gamma (x, typ) in
    syn_exp gamma delta exp
  | Ap (f, exp) -> (
      match syn_exp gamma delta f with
      | Some (Arrow (typ1, typ2)) -> (
          match syn_exp gamma delta exp with
          | Some typ1' ->
            if typ1 == typ1' then Some typ2 else None
          | None -> None
        )
      | Some _ | None -> None
    )
  | Pair (e1, e2) -> (
      match (
        (syn_exp gamma delta e1),
        (syn_exp gamma delta e2)
      ) with
      | (Some typ1, Some typ2) -> Some (Prod (typ1, typ2))
      | _ -> None
    )
  | Inj (side, typ2, e) ->
    (syn_exp gamma delta e)
    |> Option.map (
      fun typ1 : Typ.t ->
        match side with
        | InjSide.L -> Sum (typ1, typ2)
        | InjSide.R -> Sum (typ2, typ1)
    )
  | Match (scrut, zrules) -> (
      match zrules with
      | ZRules ([], r, rs) -> (
          match syn_exp gamma delta scrut with
          | Some typ -> (
              match syn_rules
                      gamma delta
                      (r::rs) typ Constraint.Falsity
              with
              | Some (xi, typ') ->
                if Incon.is_exhaustive xi then
                  Some typ'
                else 
                  None
              | None -> None
            )
          | None -> None
        )
      | ZRules (rs_pre, r, rs_post) -> (
          match syn_exp gamma delta scrut with
          | Some typ -> 
            if Eval.is_final scrut then (
              match syn_rules
                      gamma delta
                      rs_pre typ Constraint.Falsity
              with
              | Some (xi_pre, typ') ->
                (* TODO check if e mustn't satisfy xi_pre *)
                (match
                   syn_rules
                     gamma delta
                     (r::rs_post) typ xi_pre
                 with
                 | Some (xi_rest, typ'') ->
                   if typ' <> typ'' then
                     None (* type inconsistency *)
                   else if not (Incon.is_exhaustive (Constraint.Or (xi_pre, xi_rest))) then
                     None (* not exhaustive, the original match expression not well typed *)
                   else
                     Some typ'
                 | None -> None (* rs_pre not well typed *)
                )
              | None -> None
            )
            else None (* scrut not final *)
          | None -> None
        )

    )
and syn_rules gamma delta rules typ xi_pre : (Constraint.t * Typ.t) option =
  match 
    rules
    |> List.map 
      (fun rule -> syn_rule gamma delta rule typ)
  with
  | [] (* empty rule shouldn't exist *)
  | None::_ -> None (* first rule not well typed *)
  | Some (xi_r, typ')::xi_typ_opts -> 
    List.fold_left
      (fun acc xi_typ_opt ->
         match (acc, xi_typ_opt) with
         | (None, _) (* error pass through *)
         | (_, None) -> None (* rule not well typed *)
         | (Some (xi_pre, typ'_last), Some (xi_r, typ')) ->
           if Incon.is_redundant xi_r xi_pre then
             None (* rule is redundant *)
           else if typ'_last <> typ' then
             None (* type inconsistency *)
           else
             Some (Constraint.Or (xi_pre, xi_r), typ')
      )
      (Some (Constraint.Or (xi_pre, xi_r), typ'))
      xi_typ_opts
and syn_rule gamma delta (Exp.Rule (pat, exp)) typ : (Constraint.t * Typ.t) option =
  match ana_pat pat typ with
  | Some (xi, gamma', delta') -> (
      match
        syn_exp
          (VarCtx.union gamma gamma') 
          (HoleCtx.union delta delta') 
          exp
      with
      | Some (typ') -> Some (xi, typ')
      | None -> None
    )
  | None -> None
and ana_pat (pat: Pat.t) (typ: Typ.t) : (Constraint.t * VarCtx.t * HoleCtx.t) option =
  match (pat, typ) with
  | (EmptyHole h, typ) -> Some (
      Unknown,
      VarCtx.empty,
      HoleCtx.add h (HoleCtx.PatHole, typ) HoleCtx.empty
    )
  | (NonEmptyHole (h, typ', p), typ) -> 
    (ana_pat p typ')
    |> Option.map (
      fun (_xi, ctx, delta) ->
        (Constraint.Unknown, ctx, HoleCtx.add h (HoleCtx.PatHole, typ) delta)
    )
  | (Var x, typ) -> Some (Truth, [(x, typ)], HoleCtx.empty)
  | (Num n, Num) -> Some (Num n, VarCtx.empty, HoleCtx.empty)
  | (Inj (L, p), Sum (typ1, _typ2)) ->
    (ana_pat p typ1)
    |> Option.map (
      function (xi, gamma, delta) ->
        (Constraint.Inl xi, gamma, delta)
    )
  | (Inj (R, p), Sum (_typ1, typ2)) ->
    (ana_pat p typ2)
    |> Option.map (
      function (xi, gamma, delta) ->
        (Constraint.Inr xi, gamma, delta)
    )
  | (Pair (p1, p2), Prod (typ1, typ2)) -> (
      match (
        (ana_pat p1 typ1),
        (ana_pat p2 typ2)
      ) with
      | (Some (xi1, gamma1, delta1), Some (xi2, gamma2, delta2)) ->
        Some
          (Constraint.Pair (xi1, xi2),
           VarCtx.strict_union gamma1 gamma2,
           HoleCtx.union delta1 delta2)
      | _ -> None
    )
  | _ -> None

let%test _= syn_rules VarCtx.empty HoleCtx.empty [Rule (Var "x", Num 1); Rule (EmptyHole 1, Num 2)] Num Constraint.Falsity = None
let%expect_test _ = 
  try
    raise Unimplemented
  with Unimplemented ->
    print_endline "unimplemented";
    [%expect{| unimplemented |}]
;;
