open import List
open import Nat
open import Prelude
open import contexts
open import core
open import freshness
open import patterns-core

-- this module contains various judgements which
-- state that two term do not share any binders, or
-- do not share any hole binders. to avoid duplication,
-- each judgement is generic in its second argument.
-- we insert these assumptions as needed to follow
-- Barendregt's convention
module binders-disjointness where
  mutual
    data binders-disjoint-p {T : Set} {{_ : UnboundIn T}} :
                            pattrn → T → Set where
      BDPUnit   : ∀{t} →
                  binders-disjoint-p unit t
      BDPNum    : ∀{n t} →
                  binders-disjoint-p (N n) t
      BDPVar    : ∀{x t} →
                  unbound-in x t →
                  binders-disjoint-p (X x) t
      BDPInl    : ∀{p t} →
                  binders-disjoint-p p t →
                  binders-disjoint-p (inl p) t
      BDPInr    : ∀{p t} →
                  binders-disjoint-p p t →
                  binders-disjoint-p (inr p) t
      BDPPair   : ∀{p1 p2 t} →
                  binders-disjoint-p p1 t →
                  binders-disjoint-p p2 t →
                  binders-disjoint-p ⟨ p1 , p2 ⟩ t
      BDPWild   : ∀{t} →
                  binders-disjoint-p wild t
      BDPEHole  : ∀{w t} →
                  binders-disjoint-p ⦇-⦈[ w ] t
      BDPHole : ∀{p w τ t} →
                  binders-disjoint-p p t →
                  binders-disjoint-p ⦇⌜ p ⌟⦈[ w , τ ] t
      
    data binders-disjoint-r {T : Set} {{_ : UnboundIn T}} :
                            rule → T → Set where
      BDRule : ∀{p e t} →
               binders-disjoint-p p t →
               binders-disjoint e t →
               binders-disjoint-r (p => e) t
               
    data binders-disjoint-rs {T : Set} {{_ : UnboundIn T}} :
                             rules → T → Set where
      BDNoRules : ∀{t} →
                  binders-disjoint-rs nil t
      BDRules   : ∀{r rs t} →
                  binders-disjoint-r r t →
                  binders-disjoint-rs rs t →
                  binders-disjoint-rs (r / rs) t
                  
    data binders-disjoint-zrs {T : Set} {{_ : UnboundIn T}} :
                              zrules → T → Set where
      BDZRules : ∀{rs-pre r rs-post t} →
                 binders-disjoint-rs rs-pre t →
                 binders-disjoint-rs (r / rs-post) t →
                 binders-disjoint-zrs (rs-pre / r / rs-post) t

    data binders-disjoint-σ {T : Set} {{_ : UnboundIn T}} :
                            subst-env → T → Set where
      BDσId    : ∀{Γ t} →
                 binders-disjoint-σ (Id Γ) t
      BDσSubst : ∀{d y σ t} →
                 binders-disjoint d t →
                 unbound-in y t →
                 binders-disjoint-σ σ t →
                 binders-disjoint-σ (Subst d y σ) t
                 
    data binders-disjoint {T : Set} {{_ : UnboundIn T}} :
                          ihexp → T → Set where
      BDUnit   : ∀{t} →
                 binders-disjoint unit t
      BDNum    : ∀{n t} →
                 binders-disjoint (N n) t
      BDVar    : ∀{x t} →
                 binders-disjoint (X x) t
      BDLam    : ∀{x τ e t} →
                 unbound-in x t →
                 binders-disjoint e t →
                 binders-disjoint (·λ x ·[ τ ] e) t
      BDAp     : ∀{e1 e2 t} →
                 binders-disjoint e1 t →
                 binders-disjoint e2 t →
                 binders-disjoint (e1 ∘ e2) t
      BDInl    : ∀{e τ t} →
                 binders-disjoint e t →
                 binders-disjoint (inl τ e) t
      BDInr    : ∀{e τ t} →
                 binders-disjoint e t →
                 binders-disjoint (inr τ e) t
      BDMatch  : ∀{e τ rs t} →
                 binders-disjoint e t →
                 binders-disjoint-zrs rs t →
                 binders-disjoint (match e ·: τ of rs) t
      BDPair   : ∀{e1 e2 t} →
                 binders-disjoint e1 t →
                 binders-disjoint e2 t →
                 binders-disjoint ⟨ e1 , e2 ⟩ t
      BDFst    : ∀{e t} →
                 binders-disjoint e t →
                 binders-disjoint (fst e) t
      BDSnd    : ∀{e t} →
                 binders-disjoint e t →
                 binders-disjoint (snd e) t
      BDEHole  : ∀{u σ t} →
                 binders-disjoint-σ σ t →
                 binders-disjoint ⦇-⦈⟨ u , σ ⟩ t
      BDHole : ∀{e u σ t} →
                 binders-disjoint-σ σ t →
                 binders-disjoint e t →
                 binders-disjoint ⦇⌜ e ⌟⦈⟨ u , σ ⟩ t
                  
  mutual
    data hole-binders-disjoint-p {T : Set} {{_ : HoleUnboundIn T}} :
                                 pattrn → T → Set where
      HBDPUnit   : ∀{t} →
                   hole-binders-disjoint-p unit t
      HBDPNum    : ∀{n t} →
                   hole-binders-disjoint-p (N n) t
      HBDPVar    : ∀{x t} →
                   hole-binders-disjoint-p (X x) t
      HBDPInl    : ∀{p t} →
                   hole-binders-disjoint-p p t →
                   hole-binders-disjoint-p (inl p) t
      HBDPInr    : ∀{p t} →
                   hole-binders-disjoint-p p t →
                   hole-binders-disjoint-p (inr p) t
      HBDPPair   : ∀{p1 p2 t} →
                   hole-binders-disjoint-p p1 t →
                   hole-binders-disjoint-p p2 t →
                   hole-binders-disjoint-p ⟨ p1 , p2 ⟩ t
      HBDPWild   : ∀{t} →
                   hole-binders-disjoint-p wild t
      HBDPEHole  : ∀{w t} →
                   hole-unbound-in w t →
                   hole-binders-disjoint-p ⦇-⦈[ w ] t
      HBDPHole : ∀{p w τ t} →
                   hole-unbound-in w t →
                   hole-binders-disjoint-p p t →
                   hole-binders-disjoint-p ⦇⌜ p ⌟⦈[ w , τ ] t
      
    data hole-binders-disjoint-r {T : Set} {{_ : HoleUnboundIn T}} :
                                 rule → T → Set where
      HBDRule : ∀{p e t} →
                hole-binders-disjoint-p p t →
                hole-binders-disjoint e t →
                hole-binders-disjoint-r (p => e) t
                
    data hole-binders-disjoint-rs {T : Set} {{_ : HoleUnboundIn T}} :
                                  rules → T → Set where
      HBDNoRules : ∀{t} →
                   hole-binders-disjoint-rs nil t
      HBDRules   : ∀{r rs t} →
                   hole-binders-disjoint-r r t →
                   hole-binders-disjoint-rs rs t →
                   hole-binders-disjoint-rs (r / rs) t
                  
    data hole-binders-disjoint-zrs {T : Set} {{_ : HoleUnboundIn T}} :
                                   zrules → T → Set where
      HBDZRules : ∀{rs-pre r rs-post t} →
                  hole-binders-disjoint-rs rs-pre t →
                  hole-binders-disjoint-rs (r / rs-post) t →
                  hole-binders-disjoint-zrs (rs-pre / r / rs-post) t

    data hole-binders-disjoint-σ {T : Set} {{_ : HoleUnboundIn T}} :
                                 subst-env → T → Set where
      HBDσId    : ∀{Γ t} →
                  hole-binders-disjoint-σ (Id Γ) t
      HBDσSubst : ∀{d y σ t} →
                  hole-binders-disjoint d t →
                  hole-binders-disjoint-σ σ t →
                  hole-binders-disjoint-σ (Subst d y σ) t
                  
    data hole-binders-disjoint {T : Set} {{_ : HoleUnboundIn T}} :
                               ihexp → T → Set where
      HBDUnit   : ∀{t} →
                  hole-binders-disjoint unit t
      HBDNum    : ∀{n t} →
                  hole-binders-disjoint (N n) t
      HBDVar    : ∀{x t} →
                  hole-binders-disjoint (X x) t
      HBDLam    : ∀{x τ e t} →
                  hole-binders-disjoint e t →
                  hole-binders-disjoint (·λ x ·[ τ ] e) t
      HBDAp     : ∀{e1 e2 t} →
                  hole-binders-disjoint e1 t →
                  hole-binders-disjoint e2 t →
                  hole-binders-disjoint (e1 ∘ e2) t
      HBDInl    : ∀{e τ t} →
                  hole-binders-disjoint e t →
                  hole-binders-disjoint (inl τ e) t
      HBDInr    : ∀{e τ t} →
                  hole-binders-disjoint e t →
                  hole-binders-disjoint (inr τ e) t
      HBDMatch  : ∀{e τ rs t} →
                  hole-binders-disjoint e t →
                  hole-binders-disjoint-zrs rs t →
                  hole-binders-disjoint (match e ·: τ of rs) t
      HBDPair   : ∀{e1 e2 t} →
                  hole-binders-disjoint e1 t →
                  hole-binders-disjoint e2 t →
                  hole-binders-disjoint ⟨ e1 , e2 ⟩ t
      HBDFst    : ∀{e t} →
                  hole-binders-disjoint e t →
                  hole-binders-disjoint (fst e) t
      HBDSnd    : ∀{e t} →
                  hole-binders-disjoint e t →
                  hole-binders-disjoint (snd e) t
      HBDEHole  : ∀{u σ t} →
                  hole-binders-disjoint-σ σ t →
                  hole-binders-disjoint ⦇-⦈⟨ u , σ ⟩ t
      HBDHole : ∀{e u σ t} →
                  hole-binders-disjoint-σ σ t →
                  hole-binders-disjoint e t →
                  hole-binders-disjoint ⦇⌜ e ⌟⦈⟨ u , σ ⟩ t

