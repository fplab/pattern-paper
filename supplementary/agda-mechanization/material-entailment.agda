open import Prelude
open import contexts
open import core
open import complete-constraints-core
open import complete-satisfy-exclusive
open import statics-core
open import value-judgements

-- theorem showing that material entailment holds,
-- analogous to the fact that P → Q is equivalent
-- to ¬P ∨ Q
module material-entailment where
  -- entailment of constraint can instead be rephrased in terms
  -- of exhaustiveness
  entailment-material : ∀{ξ1 ξ2 τ} →
                        ξ1 ·: τ cc⊧ ξ2 →
                        ·⊤ ·: τ cc⊧ ((ξ1 ◆d) ∨ ξ2)
  entailment-material {ξ1 = ξ1} {ξ2 = ξ2} (Entails {τ = τ} ct1 ct2 ent) =
    Entails CTTruth (CTOr (dual-same-type ct1) ct2) material
    where
      material : ∀{Δ Δp e} →
            ∅ , Δ , Δp ⊢ e :: τ →
            e val →
            e ⊧ ·⊤ →
            e ⊧ ((ξ1 ◆d) ∨ ξ2)
      material wt eval CSTruth
        with comp-satisfy-exclusive ct1 wt eval
      ... | Satisfy sat1 _ = CSOrR (ent wt eval sat1)
      ... | SatisfyDual _ satd1 = CSOrL satd1

  material-entailment : ∀{ξ1 ξ2 τ} →
                        ·⊤ ·: τ cc⊧ ((ξ1 ◆d) ∧ ξ2) →
                        ξ1 ·: τ cc⊧ ξ2
  material-entailment {ξ1 = ξ1} {ξ2 = ξ2}
                      (Entails tct (CTnd {τ = τ} ctd1 ct2) ment) =
    Entails (same-type-dual ctd1) ct2 ent
    where
      ent : ∀{Δ Δp e} →
            ∅ , Δ , Δp ⊢ e :: τ →
            e val →
            e ⊧ ξ1 →
            e ⊧ ξ2
      ent wt eval sat1
        with ment wt eval CSTruth
      ... | CSAnd satd1 sat2 = sat2
