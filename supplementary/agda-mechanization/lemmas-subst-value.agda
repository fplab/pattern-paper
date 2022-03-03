open import Nat
open import Prelude
open import core
open import dynamics-core
open import value-judgements

-- substituting a variable preserves the
-- value and notintro judgements
module lemmas-subst-value where
  subst-notintro : ∀{x e1 e2} →
                   e1 notintro →
                   ([ e2 / x ] e1) notintro
  subst-notintro NVAp = NVAp
  subst-notintro NVMatch = NVMatch
  subst-notintro NVFst = NVFst
  subst-notintro NVSnd = NVSnd
  subst-notintro NVEHole = NVEHole
  subst-notintro NVHole = NVHole
                            
  subst-val : ∀{x e1 e2} →
              e1 val →
              ([ e2 / x ] e1) val
  subst-val VUnit = VUnit
  subst-val VNum = VNum
  subst-val {x = x} (VLam {x = y})
    with nat-dec y x
  ... | Inl refl = VLam
  ... | Inr y≠x = VLam
  subst-val (VInl val1) =
    VInl (subst-val val1)
  subst-val (VInr val1) =
    VInr (subst-val val1)
  subst-val (VPair val1₁ val1₂) =
    VPair (subst-val val1₁)
          (subst-val val1₂)
