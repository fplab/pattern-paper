include Util
include Syntax

exception Unimplemented

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
      | ZRules (Empty, r, rs) -> (
          match syn_exp gamma delta scrut with
          | Some typ -> (
              match syn_rules
                      gamma delta
                      (Exp.Rules (r, rs)) typ Constraint.Falsity
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
      | ZRules (rs_pre, r, rs_post) -> raise Unimplemented (* is it okay to assume xi_pre is of the form of disjunction *)
    )
and syn_rules gamma delta rules typ xi_pre : (Constraint.t * Typ.t) option =
  raise Unimplemented (* state explicited for the return type of match? *)
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
  | (NonEmptyHole (h, p), typ) -> 
    raise Unimplemented 
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
           VarCtx.union gamma1 gamma2, (* TODO duplicate var *)
           HoleCtx.union delta1 delta2)
      | _ -> None
    )
