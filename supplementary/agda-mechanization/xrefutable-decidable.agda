open import Bool
open import Prelude
open import constraints-core

module xrefutable-decidable where
  xrefutable-bool : constr → Bool
  xrefutable-bool ·⊤ = false
  xrefutable-bool ·⊥ = true
  xrefutable-bool ·? = true
  xrefutable-bool (N n) = true
  xrefutable-bool (inl ξ) = true
  xrefutable-bool (inr ξ) = true
  xrefutable-bool ⟨ ξ1 , ξ2 ⟩ = xrefutable-bool ξ1 or xrefutable-bool ξ2
  xrefutable-bool (ξ1 ∨ ξ2) = xrefutable-bool ξ1 and xrefutable-bool ξ2

  xrefutable-sound : ∀{ξ} →
                     ξ xrefutable →
                     xrefutable-bool ξ == true
  xrefutable-sound RXUnknown = refl
  xrefutable-sound RXFalsity = refl
  xrefutable-sound RXNum = refl
  xrefutable-sound RXInl = refl
  xrefutable-sound RXInr = refl
  xrefutable-sound (RXPairL xr) = or-true-l (xrefutable-sound xr)
  xrefutable-sound (RXPairR xr) = or-true-r (xrefutable-sound xr)
  xrefutable-sound (RXOr xr1 xr2) = and-true (xrefutable-sound xr1) (xrefutable-sound xr2)
  
  xrefutable-complete : ∀{ξ} →
                        xrefutable-bool ξ == true →
                        ξ xrefutable
  xrefutable-complete {·⊥} xreq = RXFalsity
  xrefutable-complete {·?} xreq = RXUnknown
  xrefutable-complete {N n} xreq = RXNum
  xrefutable-complete {inl ξ} xreq = RXInl
  xrefutable-complete {inr ξ} xreq = RXInr
  xrefutable-complete {⟨ ξ1 , ξ2 ⟩} xreq with true-or xreq
  ... | Inl xr1 = RXPairL (xrefutable-complete xr1)
  ... | Inr xr2 = RXPairR (xrefutable-complete xr2)
  xrefutable-complete {ξ1 ∨ ξ2} xreq with true-and xreq
  ... | xr1 , xr2 = RXOr (xrefutable-complete xr1) (xrefutable-complete xr2)
  
  xrefutable-dec : (ξ : constr) →
                   (ξ xrefutable) + (ξ xrefutable → ⊥)
  xrefutable-dec ξ with xrefutable-bool ξ in eq
  ... | false = Inr (λ ni → false-neq-true eq (xrefutable-sound ni))
  ... | true = Inl (xrefutable-complete eq)
