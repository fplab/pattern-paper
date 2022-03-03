open import Bool
open import Prelude
open import constraints-core

module possible-decidable where
  possible-bool : constr → Bool
  possible-bool ·⊤ = true
  possible-bool ·⊥ = false
  possible-bool ·? = true
  possible-bool (N n) = true
  possible-bool (inl ξ) = possible-bool ξ
  possible-bool (inr ξ) = possible-bool ξ
  possible-bool ⟨ ξ1 , ξ2 ⟩ = possible-bool ξ1 and possible-bool ξ2
  possible-bool (ξ1 ∨ ξ2) = possible-bool ξ1 or possible-bool ξ2

  possible-sound : ∀{ξ} →
                     ξ possible →
                     possible-bool ξ == true
  possible-sound PTruth = refl
  possible-sound PUnknown = refl
  possible-sound PNum = refl
  possible-sound (PInl pos) = possible-sound pos
  possible-sound (PInr pos) = possible-sound pos
  possible-sound (PPair pos1 pos2) = and-true (possible-sound pos1) (possible-sound pos2)
  possible-sound (POrL pos) = or-true-l (possible-sound pos)
  possible-sound {ξ = ξ1 ∨ ξ2} (POrR pos) =
    or-true-r {P = possible-bool ξ1} (possible-sound pos)
  
  possible-complete : ∀{ξ} →
                      possible-bool ξ == true →
                      ξ possible
  possible-complete {·⊤} poseq = PTruth
  possible-complete {·?} poseq = PUnknown
  possible-complete {N n} poseq = PNum
  possible-complete {inl ξ} poseq = PInl (possible-complete poseq)
  possible-complete {inr ξ} poseq = PInr (possible-complete poseq)
  possible-complete {⟨ ξ1 , ξ2 ⟩} poseq
    with true-and poseq
  ... | pos1 , pos2 = PPair (possible-complete pos1) (possible-complete pos2)
  possible-complete {ξ1 ∨ ξ2} poseq
    with true-or poseq
  ... | Inl pos1 = POrL (possible-complete pos1)
  ... | Inr pos2 = POrR (possible-complete pos2)
  
  possible-dec : (ξ : constr) →
                   (ξ possible) + (ξ possible → ⊥)
  possible-dec ξ with possible-bool ξ in eq
  ... | false = Inr (λ ni → false-neq-true eq (possible-sound ni))
  ... | true = Inl (possible-complete eq)
