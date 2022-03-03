open import List
open import Nat
open import Prelude
open import constraints-core
open import core
open import dynamics-core
open import freshness-decidable
open import lemmas-patterns
open import lemmas-subst-type
open import patterns-core
open import statics-core

-- substituting an exhaustive expression
-- into another exhaustive expression produces
-- something exhaustive
module lemmas-subst-exhaustive where
  mutual
    subst-exhaustive : ∀{Δp e1 x e2} →
                       Δp ⊢ e1 exhaustive →
                       Δp ⊢ e2 exhaustive →
                       Δp ⊢ ([ e2 / x ] e1) exhaustive
    subst-exhaustive EXUnit ex2 = EXUnit
    subst-exhaustive EXNum ex2 = EXNum
    subst-exhaustive {x = x} (EXVar {x = y}) ex2
      with nat-dec y x
    ... | Inl refl = ex2
    ... | Inr x≠y = EXVar
    subst-exhaustive {x = x} (EXLam {x = y} ex1) ex2
      with nat-dec y x
    ... | Inl refl = EXLam ex1
    ... | Inr x≠y = EXLam (subst-exhaustive ex1 ex2)
    subst-exhaustive (EXAp ex1₁ ex1₂) ex2 =
      EXAp (subst-exhaustive ex1₁ ex2) (subst-exhaustive ex1₂ ex2)
    subst-exhaustive (EXInl ex1) ex2 =
      EXInl (subst-exhaustive ex1 ex2)
    subst-exhaustive (EXInr ex1) ex2 =
      EXInr (subst-exhaustive ex1 ex2)
    subst-exhaustive (EXMatchZPre ex rst ent exts) ex2 =
      EXMatchZPre (subst-exhaustive ex ex2)
                  (subst-type-rs-no-target rst)
                  ent
                  (subst-exhaustive-targets exts ex2)
    subst-exhaustive (EXMatchNZPre ex pret restt ent expret exrestt) ex2 =
      EXMatchNZPre (subst-exhaustive ex ex2)
                   (subst-type-rs-no-target pret)
                   (subst-type-rs-no-target restt)
                   ent
                   (subst-exhaustive-targets expret ex2)
                   (subst-exhaustive-targets exrestt ex2)
    subst-exhaustive (EXPair ex1₁ ex1₂) ex2 =
      EXPair (subst-exhaustive ex1₁ ex2) (subst-exhaustive ex1₂ ex2)
    subst-exhaustive (EXFst ex1) ex2 =
      EXFst (subst-exhaustive ex1 ex2)
    subst-exhaustive (EXSnd ex1) ex2 =
      EXSnd (subst-exhaustive ex1 ex2)
    subst-exhaustive (EXEHole w∈Δ) ex2 =
      EXEHole (EXσSubst w∈Δ ex2)
    subst-exhaustive (EXHole w∈Δ ex1) ex2 =
      EXHole (EXσSubst w∈Δ ex2) (subst-exhaustive ex1 ex2)

    subst-exhaustive-targets : ∀{Δp rs x e2} →
                               Δp ⊢ rs exhaustive-targets →
                               Δp ⊢ e2 exhaustive →
                               Δp ⊢ ([ e2 / x ]rs rs) exhaustive-targets
    subst-exhaustive-targets EXNoRules ex2 = EXNoRules
    subst-exhaustive-targets {x = x} (EXRules {p = p} ex exrs) ex2
      with unbound-in-p-dec x p
    ... | Inl ub =
      EXRules (subst-exhaustive ex ex2)
              (subst-exhaustive-targets exrs ex2)
    ... | Inr ¬ub =
      EXRules ex (subst-exhaustive-targets exrs ex2)

  -- if each part of a substitution list is exhaustive,
  -- then so is the whole list
  substs-concat-exhaustive : ∀{Δp θ1 θ2} →
                             Δp ⊢ θ1 exhaustive-θ →
                             Δp ⊢ θ2 exhaustive-θ →
                             Δp ⊢ (θ1 ++ θ2) exhaustive-θ
  substs-concat-exhaustive EXθEmpty ex2 = ex2
  substs-concat-exhaustive (EXθExtend ex1 exd) ex2 =
    EXθExtend (substs-concat-exhaustive ex1 ex2) exd

  -- if an expression is exhaustive, then each of the
  -- substitutions it emits consists of exhaustive expressions
  mat-substs-exhaustive : ∀{Δp e τ p θ} →
                          Δp ⊢ e exhaustive →
                          e ·: τ ▹ p ⊣ θ →
                          Δp ⊢ θ exhaustive-θ
  mat-substs-exhaustive ex MUnit = EXθEmpty
  mat-substs-exhaustive ex MNum = EXθEmpty
  mat-substs-exhaustive ex MVar = EXθExtend EXθEmpty ex
  mat-substs-exhaustive (EXInl ex) (MInl mat) =
    mat-substs-exhaustive ex mat
  mat-substs-exhaustive (EXInr ex) (MInr mat) =
    mat-substs-exhaustive ex mat
  mat-substs-exhaustive ex (MPair mat1 mat2)
    with ex
  ... | EXPair ex1 ex2 =
    substs-concat-exhaustive
      (mat-substs-exhaustive ex1 mat1)
      (mat-substs-exhaustive ex2 mat2)
  mat-substs-exhaustive ex (MNotIntroPair ni mat1 mat2) =
    substs-concat-exhaustive
      (mat-substs-exhaustive (EXFst ex) mat1)
      (mat-substs-exhaustive (EXSnd ex) mat2)
  mat-substs-exhaustive ex MWild = EXθEmpty

  -- applying a series of substitutions for exhaustive
  -- expressions produces something exhaustive
  substs-exhaustive : ∀{Δp θ e} →
                      Δp ⊢ θ exhaustive-θ →
                      Δp ⊢ e exhaustive →
                      Δp ⊢ (apply-substs θ e) exhaustive
  substs-exhaustive EXθEmpty ex = ex
  substs-exhaustive (EXθExtend exθ exd) ex =
    EXAp (EXLam (substs-exhaustive exθ ex)) exd
