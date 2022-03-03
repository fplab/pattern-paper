open import List
open import Nat
open import Prelude
open import binders-disjointness
open import binders-disjoint-symmetric
open import binders-uniqueness
open import core
open import dynamics-core
open import freshness
open import freshness-decidable
open import hole-binders-disjoint-symmetric

-- substituting a variable preserves binder
-- disjointness conditions
module lemmas-subst-disjointness where
  mutual
    subst-binders-disjoint : ∀{x e1 e2} {e : ihexp} →
                             binders-disjoint e1 e →
                             binders-disjoint e2 e →
                             unbound-in x e →
                             binders-disjoint ([ e2 / x ] e1) e
    subst-binders-disjoint {e1 = unit} BDUnit bd2 ube = BDUnit
    subst-binders-disjoint {e1 = N n} BDNum bd2 ube = BDNum
    subst-binders-disjoint {x = x} {e1 = X y} (BDVar) bd2 ube
      with nat-dec y x
    ... | Inl refl = bd2
    ... | Inr y≠x = BDVar
    subst-binders-disjoint {x = x} {e1 = ·λ y ·[ τ ] e1}
                           (BDLam ub bd1) bd2 ube
      with nat-dec y x
    ... | Inl refl = BDLam ub bd1
    ... | Inr y≠x = BDLam ub (subst-binders-disjoint bd1 bd2 ube)
    subst-binders-disjoint {e1 = e1₁ ∘ e1₂} (BDAp bd1₁ bd1₂) bd2 ube =
      BDAp (subst-binders-disjoint bd1₁ bd2 ube)
           (subst-binders-disjoint bd1₂ bd2 ube)
    subst-binders-disjoint {e1 = inl τ e1} (BDInl bd1) bd2 ube =
      BDInl (subst-binders-disjoint bd1 bd2 ube)
    subst-binders-disjoint {e1 = inr τ e1} (BDInr bd1) bd2 ube =
      BDInr (subst-binders-disjoint bd1 bd2 ube)
    subst-binders-disjoint {e1 = match e1 ·: τ of rs}
                           (BDMatch bd1 bdrs) bd2 ube =
      BDMatch (subst-binders-disjoint bd1 bd2 ube)
              (subst-binders-disjoint-zrs bdrs bd2 ube)
    subst-binders-disjoint {e1 = ⟨ e1₁ , e1₂ ⟩}
                           (BDPair bd1₁ bd1₂) bd2 ube =
      BDPair (subst-binders-disjoint bd1₁ bd2 ube)
             (subst-binders-disjoint bd1₂ bd2 ube)
    subst-binders-disjoint {e1 = fst e1} (BDFst bd1) bd2 ube =
      BDFst (subst-binders-disjoint bd1 bd2 ube)
    subst-binders-disjoint {e1 = snd e1} (BDSnd bd1) bd2 ube =
      BDSnd (subst-binders-disjoint bd1 bd2 ube)
    subst-binders-disjoint {e1 = ⦇-⦈⟨ u , σ ⟩} (BDEHole bdσ) bd2 ube =
      BDEHole (subst-binders-disjoint-σ bdσ bd2 ube)
    subst-binders-disjoint {e1 = ⦇⌜ e1 ⌟⦈⟨ u , σ ⟩}
                           (BDHole bdσ bd1) bd2 ube =
      BDHole (subst-binders-disjoint-σ bdσ bd2 ube)
               (subst-binders-disjoint bd1 bd2 ube)

    subst-binders-disjoint-σ : ∀{x σ e2} {e : ihexp} →
                               binders-disjoint-σ σ e →
                               binders-disjoint e2 e →
                               unbound-in x e →
                               binders-disjoint-σ (Subst e2 x σ) e
    subst-binders-disjoint-σ BDσId bd2 ube = BDσSubst bd2 ube BDσId
    subst-binders-disjoint-σ (BDσSubst bde ub bdσ) bd2 ube =
      BDσSubst bd2 ube (subst-binders-disjoint-σ bdσ bde ub)
    
    subst-binders-disjoint-zrs : ∀{x zrs e2} {e : ihexp} →
                                 binders-disjoint-zrs zrs e →
                                 binders-disjoint e2 e →
                                 unbound-in x e →
                                 binders-disjoint-zrs ([ e2 / x ]zrs zrs) e
    subst-binders-disjoint-zrs (BDZRules bdpre bdpost) bd2 ube =
      BDZRules (subst-binders-disjoint-rs bdpre bd2 ube)
               (subst-binders-disjoint-rs bdpost bd2 ube)
    
    subst-binders-disjoint-rs : ∀{x rs e2} {e : ihexp} →
                                binders-disjoint-rs rs e →
                                binders-disjoint e2 e →
                                unbound-in x e →
                                binders-disjoint-rs ([ e2 / x ]rs rs) e
    subst-binders-disjoint-rs BDNoRules bd2 ube = BDNoRules
    subst-binders-disjoint-rs (BDRules bdr bdrs) bd2 ube = 
      BDRules (subst-binders-disjoint-r bdr bd2 ube)
             (subst-binders-disjoint-rs bdrs bd2 ube)
  
    subst-binders-disjoint-r : ∀{x r e2} {e : ihexp} →
                               binders-disjoint-r r e →
                               binders-disjoint e2 e →
                               unbound-in x e →
                               binders-disjoint-r ([ e2 / x ]r r) e
    subst-binders-disjoint-r {x = x} (BDRule {p = p} bdp bd) bd2 ube
      with unbound-in-p-dec x p
    ... | Inr ¬ub = BDRule bdp bd
    ... | Inl ub = BDRule bdp (subst-binders-disjoint bd bd2 ube)
  
  mutual
    subst-hole-binders-disjoint : ∀{x e1 e2} {e : ihexp} →
                                  hole-binders-disjoint e1 e →
                                  hole-binders-disjoint e2 e →
                                  hole-binders-disjoint ([ e2 / x ] e1) e
    subst-hole-binders-disjoint {e1 = unit} HBDUnit bd2 = HBDUnit
    subst-hole-binders-disjoint {e1 = N n} HBDNum bd2 = HBDNum
    subst-hole-binders-disjoint {x = x} {e1 = X y} HBDVar bd2
      with nat-dec y x
    ... | Inl refl = bd2
    ... | Inr y≠x = HBDVar
    subst-hole-binders-disjoint
      {x = x} {e1 = ·λ y ·[ τ ] e1} (HBDLam bd1) bd2
      with nat-dec y x
    ... | Inl refl = HBDLam bd1
    ... | Inr y≠x = HBDLam (subst-hole-binders-disjoint bd1 bd2)
    subst-hole-binders-disjoint {e1 = e1₁ ∘ e1₂} (HBDAp bd1₁ bd1₂) bd2 =
      HBDAp (subst-hole-binders-disjoint bd1₁ bd2)
           (subst-hole-binders-disjoint bd1₂ bd2)
    subst-hole-binders-disjoint {e1 = inl τ e1} (HBDInl bd1) bd2 =
      HBDInl (subst-hole-binders-disjoint bd1 bd2)
    subst-hole-binders-disjoint {e1 = inr τ e1} (HBDInr bd1) bd2 =
      HBDInr (subst-hole-binders-disjoint bd1 bd2)
    subst-hole-binders-disjoint {e1 = match e1 ·: τ of rs}
                                (HBDMatch bd1 bdrs) bd2 =
      HBDMatch (subst-hole-binders-disjoint bd1 bd2)
              (subst-hole-binders-disjoint-zrs bdrs bd2)
    subst-hole-binders-disjoint {e1 = ⟨ e1₁ , e1₂ ⟩}
                                (HBDPair bd1₁ bd1₂) bd2 =
      HBDPair (subst-hole-binders-disjoint bd1₁ bd2)
             (subst-hole-binders-disjoint bd1₂ bd2)
    subst-hole-binders-disjoint {e1 = fst e1} (HBDFst bd1) bd2 =
      HBDFst (subst-hole-binders-disjoint bd1 bd2)
    subst-hole-binders-disjoint {e1 = snd e1} (HBDSnd bd1) bd2 =
      HBDSnd (subst-hole-binders-disjoint bd1 bd2)
    subst-hole-binders-disjoint {e1 = ⦇-⦈⟨ u , σ ⟩} (HBDEHole bdσ) bd2 =
      HBDEHole (HBDσSubst bd2 bdσ)
    subst-hole-binders-disjoint {e1 = ⦇⌜ e1 ⌟⦈⟨ u , σ ⟩} (HBDHole bdσ bd1) bd2 =
      HBDHole (HBDσSubst bd2 bdσ) (subst-hole-binders-disjoint bd1 bd2)

    subst-hole-binders-disjoint-zrs : ∀{x zrs e2} {e : ihexp} →
                                      hole-binders-disjoint-zrs zrs e →
                                      hole-binders-disjoint e2 e →
                                      hole-binders-disjoint-zrs ([ e2 / x ]zrs zrs) e
    subst-hole-binders-disjoint-zrs (HBDZRules bdpre bdpost) bd2 =
      HBDZRules (subst-hole-binders-disjoint-rs bdpre bd2)
               (subst-hole-binders-disjoint-rs bdpost bd2)
    
    subst-hole-binders-disjoint-rs : ∀{x rs e2} {e : ihexp} →
                                     hole-binders-disjoint-rs rs e →
                                     hole-binders-disjoint e2 e →
                                     hole-binders-disjoint-rs ([ e2 / x ]rs rs) e
    subst-hole-binders-disjoint-rs HBDNoRules bd2 = HBDNoRules
    subst-hole-binders-disjoint-rs (HBDRules bdr bdrs) bd2 = 
      HBDRules (subst-hole-binders-disjoint-r bdr bd2)
             (subst-hole-binders-disjoint-rs bdrs bd2)
  
    subst-hole-binders-disjoint-r : ∀{x r e2} {e : ihexp} →
                                    hole-binders-disjoint-r r e →
                                    hole-binders-disjoint e2 e →
                                    hole-binders-disjoint-r ([ e2 / x ]r r) e
    subst-hole-binders-disjoint-r {x = x} (HBDRule {p = p} bdp bd) bd2
      with unbound-in-p-dec x p
    ... | Inr ¬ub = HBDRule bdp bd
    ... | Inl ub = HBDRule bdp (subst-hole-binders-disjoint bd bd2)

