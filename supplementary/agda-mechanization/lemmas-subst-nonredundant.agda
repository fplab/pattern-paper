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

-- substituting a nonredundant expression
-- into another nonredundant expression produces
-- something nonredundant
module lemmas-subst-nonredundant where
  mutual
    subst-nonredundant : ∀{Δp e1 x e2} →
                         Δp ⊢ e1 nonredundant →
                         Δp ⊢ e2 nonredundant →
                         Δp ⊢ ([ e2 / x ] e1) nonredundant
    subst-nonredundant NRUnit nr2 = NRUnit
    subst-nonredundant NRNum nr2 = NRNum
    subst-nonredundant {x = x} (NRVar {x = y}) nr2
      with nat-dec y x
    ... | Inl refl = nr2
    ... | Inr y≠x = NRVar
    subst-nonredundant {x = x} (NRLam {x = y} nr1) nr2
      with nat-dec y x
    ... | Inl refl = NRLam nr1
    ... | Inr y≠x = NRLam (subst-nonredundant nr1 nr2)
    subst-nonredundant (NRAp nr1₁ nr1₂) nr2 =
      NRAp (subst-nonredundant nr1₁ nr2)
           (subst-nonredundant nr1₂ nr2)
    subst-nonredundant (NRInl nr1) nr2 =
      NRInl (subst-nonredundant nr1 nr2)
    subst-nonredundant (NRInr nr1) nr2 =
      NRInr (subst-nonredundant nr1 nr2)
    subst-nonredundant (NRMatchZPre nr1 rst nrt) nr2 =
      NRMatchZPre (subst-nonredundant nr1 nr2)
                  (subst-type-rs-nonredundant rst)
                  (subst-nonredundant-targets nrt nr2)
    subst-nonredundant (NRMatchNZPre nr1 pret restt nrpret nrrestt) nr2 =
      NRMatchNZPre (subst-nonredundant nr1 nr2)
                   (subst-type-rs-nonredundant pret)
                   (subst-type-rs-nonredundant restt)
                   (subst-nonredundant-targets nrpret nr2)
                   (subst-nonredundant-targets nrrestt nr2)
    subst-nonredundant (NRPair nr1₁ nr1₂) nr2 =
      NRPair (subst-nonredundant nr1₁ nr2)
             (subst-nonredundant nr1₂ nr2)
    subst-nonredundant (NRFst nr1) nr2 =
      NRFst (subst-nonredundant nr1 nr2)
    subst-nonredundant (NRSnd nr1) nr2 =
      NRSnd (subst-nonredundant nr1 nr2)
    subst-nonredundant NREHole nr2 = NREHole
    subst-nonredundant (NRHole nr1) nr2 =
      NRHole (subst-nonredundant nr1 nr2)

    subst-nonredundant-targets : ∀{Δp rs x e2} →
                                 Δp ⊢ rs nonredundant-targets →
                                 Δp ⊢ e2 nonredundant →
                                 Δp ⊢ ([ e2 / x ]rs rs) nonredundant-targets
    subst-nonredundant-targets NRNoRules nr2 = NRNoRules
    subst-nonredundant-targets {x = x} (NRRules {p = p} nre nrt) nr2
      with unbound-in-p-dec x p
    ... | Inl ub =
      NRRules (subst-nonredundant nre nr2)
              (subst-nonredundant-targets nrt nr2)
    ... | Inr ¬ub =
      NRRules nre (subst-nonredundant-targets nrt nr2)

  -- if each part of a substitution list is nonredundant,
  -- then so is the whole list
  substs-concat-nonredundant : ∀{Δp θ1 θ2} →
                               Δp ⊢ θ1 nonredundant-θ →
                               Δp ⊢ θ2 nonredundant-θ →
                               Δp ⊢ (θ1 ++ θ2) nonredundant-θ
  substs-concat-nonredundant NRθEmpty nr2 = nr2
  substs-concat-nonredundant (NRθExtend nrθ nrd) nr2 =
    NRθExtend (substs-concat-nonredundant nrθ nr2) nrd


  -- if an expression is nonredundant, then each of the
  -- substitutions it emits consists of nonredundant expressions
  mat-substs-nonredundant : ∀{Δp e τ p θ} →
                            Δp ⊢ e nonredundant →
                            e ·: τ ▹ p ⊣ θ →
                            Δp ⊢ θ nonredundant-θ
  mat-substs-nonredundant nr MUnit = NRθEmpty
  mat-substs-nonredundant nr MNum = NRθEmpty
  mat-substs-nonredundant nr MVar = NRθExtend NRθEmpty nr
  mat-substs-nonredundant (NRInl nr) (MInl mat) =
    mat-substs-nonredundant nr mat
  mat-substs-nonredundant (NRInr nr) (MInr mat) =
    mat-substs-nonredundant nr mat
  mat-substs-nonredundant nr (MPair mat1 mat2)
    with nr
  ... | NRPair nr1 nr2 =
    substs-concat-nonredundant
      (mat-substs-nonredundant nr1 mat1)
      (mat-substs-nonredundant nr2 mat2)
  mat-substs-nonredundant nr (MNotIntroPair ni mat1 mat2) =
    substs-concat-nonredundant
      (mat-substs-nonredundant (NRFst nr) mat1)
      (mat-substs-nonredundant (NRSnd nr) mat2)
  mat-substs-nonredundant nr MWild = NRθEmpty

  -- applying a series of substitutions for nonredundant
  -- expressions produces something nonredundant
  substs-nonredundant : ∀{Δp θ e} →
                        Δp ⊢ θ nonredundant-θ →
                        Δp ⊢ e nonredundant →
                        Δp ⊢ (apply-substs θ e) nonredundant
  substs-nonredundant NRθEmpty nr = nr
  substs-nonredundant (NRθExtend nrθ nrd) nr =
    NRAp (NRLam (substs-nonredundant nrθ nr)) nrd
