open import Nat
open import Prelude
open import core
open import contexts

module htyp-decidable where
  arr-htyp-eq : ∀{τ1 τ2 τ3 τ4} →
                τ1 ==> τ2 == τ3 ==> τ4 →
                τ1 == τ3 × τ2 == τ4
  arr-htyp-eq refl = refl , refl

  sum-htyp-eq : ∀{τ1 τ2 τ3 τ4} →
                τ1 ⊕ τ2 == τ3 ⊕ τ4 →
                τ1 == τ3 × τ2 == τ4
  sum-htyp-eq refl = refl , refl
  
  prod-htyp-eq : ∀{τ1 τ2 τ3 τ4} →
                 τ1 ⊠ τ2 == τ3 ⊠ τ4 →
                 τ1 == τ3 × τ2 == τ4
  prod-htyp-eq refl = refl , refl
  
  htyp-dec : (τ1 τ2 : htyp) →
             τ1 == τ2 + (τ1 == τ2 → ⊥)
  htyp-dec unit unit = Inl refl
  htyp-dec unit num = Inr (λ ())
  htyp-dec unit (τ3 ==> τ4) = Inr (λ ())
  htyp-dec unit (τ3 ⊕ τ4) = Inr (λ ())
  htyp-dec unit (τ3 ⊠ τ4) = Inr (λ ())
  htyp-dec num unit = Inr (λ ())
  htyp-dec num num = Inl refl
  htyp-dec num (τ1 ==> τ2) = Inr (λ ())
  htyp-dec num (τ1 ⊕ τ2) = Inr (λ ())
  htyp-dec num (τ3 ⊠ τ4) = Inr (λ ())
  htyp-dec (τ1 ==> τ2) unit = Inr (λ ())
  htyp-dec (τ1 ==> τ2) num = Inr (λ ())
  htyp-dec (τ1 ==> τ2) (τ3 ==> τ4)
    with htyp-dec τ1 τ3 | htyp-dec τ2 τ4
  ... | Inl refl | Inl refl = Inl refl
  ... | Inl refl | Inr τ2≠τ4 =
    Inr (λ eq → τ2≠τ4 (π2 (arr-htyp-eq eq)))
  ... | Inr τ1≠τ3 | Inl refl =
    Inr (λ eq → τ1≠τ3 (π1 (arr-htyp-eq eq)))
  ... | Inr τ1≠τ3 | Inr τ2≠τ4 =
    Inr (λ eq → τ1≠τ3 (π1 (arr-htyp-eq eq)))
  htyp-dec (τ1 ==> τ2) (τ3 ⊕ τ4) = Inr (λ ())
  htyp-dec (τ1 ==> τ2) (τ3 ⊠ τ4) = Inr (λ ())
  htyp-dec (τ1 ⊕ τ2) unit = Inr (λ ())
  htyp-dec (τ1 ⊕ τ2) num = Inr (λ ())
  htyp-dec (τ1 ⊕ τ2) (τ3 ==> τ4) = Inr (λ ())
  htyp-dec (τ1 ⊕ τ2) (τ3 ⊕ τ4)
    with htyp-dec τ1 τ3 | htyp-dec τ2 τ4
  ... | Inl refl | Inl refl = Inl refl
  ... | Inl refl | Inr τ2≠τ4 =
    Inr (λ eq → τ2≠τ4 (π2 (sum-htyp-eq eq)))
  ... | Inr τ1≠τ3 | Inl refl =
    Inr (λ eq → τ1≠τ3 (π1 (sum-htyp-eq eq)))
  ... | Inr τ1≠τ3 | Inr τ2≠τ4 =
    Inr (λ eq → τ1≠τ3 (π1 (sum-htyp-eq eq)))
  htyp-dec (τ1 ⊕ τ2) (τ3 ⊠ τ4) = Inr (λ ())
  htyp-dec (τ1 ⊠ τ2) unit = Inr (λ ())
  htyp-dec (τ1 ⊠ τ2) num = Inr (λ ())
  htyp-dec (τ1 ⊠ τ2) (τ3 ==> τ4) = Inr (λ ())
  htyp-dec (τ1 ⊠ τ2) (τ3 ⊕ τ4) = Inr (λ ())
  htyp-dec (τ1 ⊠ τ2) (τ3 ⊠ τ4)
    with htyp-dec τ1 τ3 | htyp-dec τ2 τ4
  ... | Inl refl | Inl refl = Inl refl
  ... | Inl refl | Inr τ2≠τ4 =
    Inr (λ eq → τ2≠τ4 (π2 (prod-htyp-eq eq)))
  ... | Inr τ1≠τ3 | Inl refl =
    Inr (λ eq → τ1≠τ3 (π1 (prod-htyp-eq eq)))
  ... | Inr τ1≠τ3 | Inr τ2≠τ4 =
    Inr (λ eq → τ1≠τ3 (π1 (prod-htyp-eq eq)))
  
  htyp-prod-dec : (τ : htyp) →
                  (Σ[ τ1 ∈ htyp ] Σ[ τ2 ∈ htyp ]
                    τ == τ1 ⊠ τ2) +
                  ((Σ[ τ1 ∈ htyp ] Σ[ τ2 ∈ htyp ]
                    τ == τ1 ⊠ τ2) → ⊥)
  htyp-prod-dec unit = Inr (λ{(_ , _ , ())})
  htyp-prod-dec num = Inr (λ{(_ , _ , ())})
  htyp-prod-dec (τ1 ==> τ2) = Inr (λ{(_ , _ , ())})
  htyp-prod-dec (τ1 ⊕ τ2) = Inr (λ{(_ , _ , ())})
  htyp-prod-dec (τ1 ⊠ τ2) = Inl (τ1 , τ2 , refl)
  
