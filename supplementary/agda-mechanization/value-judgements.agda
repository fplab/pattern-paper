open import Bool
open import Prelude
open import core

module value-judgements where
  -- these judgements are placed into their own module separate from the
  -- final and indet judgements in order to break some dependency cycles

  -- e is a value
  data _val : (e : ihexp) → Set where
    VUnit : unit val
    VNum  : ∀{n} →
            (N n) val
    VLam  : ∀{x τ e} →
            (·λ x ·[ τ ] e) val
    VInl  : ∀{e τ} →
            e val →
            (inl τ e) val
    VInr  : ∀{e τ} →
            e val →
            (inr τ e) val
    VPair : ∀{e1 e2} →
            e1 val →
            e2 val →
            ⟨ e1 , e2 ⟩ val
 
  -- e cannot be a value statically
  data _notintro : (e : ihexp) → Set where
    NVAp     : ∀{e1 e2} →
               (e1 ∘ e2) notintro
    NVMatch  : ∀{e τ rs} →
               (match e ·: τ of rs) notintro
    NVFst    : ∀{e} →
               (fst e) notintro
    NVSnd    : ∀{e} →
               (snd e) notintro
    NVEHole  : ∀{u σ} →
               ⦇-⦈⟨ u , σ ⟩ notintro
    NVHole : ∀{e u σ} →
               ⦇⌜ e ⌟⦈⟨ u , σ ⟩ notintro

  
  val-notintro-not : ∀{e} →
                     e val →
                     e notintro →
                     ⊥
  val-notintro-not VNum ()
  val-notintro-not VLam ()
  val-notintro-not (VInl eval) ()
  val-notintro-not (VInr eval) ()
  val-notintro-not (VPair eval1 eval2) ()

  notintro-pair-not : ∀{e} →
                      e notintro →
                      (e1 e2 : ihexp) →
                      e == ⟨ e1 , e2 ⟩ →
                      ⊥
  notintro-pair-not () e1 e2 refl
