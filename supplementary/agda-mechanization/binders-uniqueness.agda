open import List
open import Nat
open import Prelude
open import binders-disjointness
open import core
open import freshness
open import patterns-core

-- various judgements stating that all binders
-- or hole binders in a term are unique à la
-- Barendregt's convention
module binders-uniqueness where
  mutual
    data binders-unique-p : pattrn → Set where
      BUPUnit   : binders-unique-p unit
      BUPNum    : ∀{n} →
                  binders-unique-p (N n)
      BUPVar    : ∀{x} →
                  binders-unique-p (X x)
      BUPInl    : ∀{p} →
                  binders-unique-p p →
                  binders-unique-p (inl p)
      BUPInr    : ∀{p} →
                  binders-unique-p p →
                  binders-unique-p (inr p)
      BUPPair   : ∀{p1 p2} →
                  binders-unique-p p1 →
                  binders-unique-p p2 →
                  binders-disjoint-p p1 p2 →
                  binders-unique-p ⟨ p1 , p2 ⟩
      BUPWild   : binders-unique-p wild
      BUPEHole  : ∀{w} →
                  binders-unique-p ⦇-⦈[ w ]
      BUPHole : ∀{p w τ} →
                  binders-unique-p p →
                  binders-unique-p ⦇⌜ p ⌟⦈[ w , τ ]

    data binders-unique-r : rule → Set where
      BURule : ∀{p e} →
               binders-unique-p p →
               binders-unique e →
               binders-disjoint-p p e →
               binders-unique-r (p => e)

    data binders-unique-rs : rules → Set where
      BUNoRules : binders-unique-rs nil
      BURules   : ∀{r rs} →
                  binders-unique-r r →
                  binders-unique-rs rs →
                  binders-disjoint-r r rs →
                  binders-unique-rs (r / rs)

    data binders-unique-zrs : zrules → Set where
      BUZRules : ∀{rs-pre r rs-post} →
                 binders-unique-rs rs-pre →
                 binders-unique-rs (r / rs-post) →
                 binders-disjoint-rs rs-pre (r / rs-post) →
                 binders-unique-zrs (rs-pre / r / rs-post)

    data binders-unique-σ : subst-env → Set where
      BUσId    : ∀{Γ} →
                 binders-unique-σ (Id Γ)
      BUσSubst : ∀{d y σ} →
                 binders-unique d →
                 binders-unique-σ σ →
                 binders-disjoint-σ σ d →
                 binders-unique-σ (Subst d y σ)
              
    data binders-unique : ihexp → Set where
      BUUnit   : binders-unique unit
      BUNum    : ∀{n} →
                 binders-unique (N n)
      BUVar    : ∀{x} →
                 binders-unique (X x)
      BULam    : ∀{x τ e} →
                 binders-unique e →
                 unbound-in-e x e →
                 binders-unique (·λ x ·[ τ ] e)
      BUEHole  : ∀{u σ} →
                 binders-unique-σ σ →
                 binders-unique ⦇-⦈⟨ u , σ ⟩
      BUHole : ∀{e u σ} →
                 binders-unique-σ σ →
                 binders-unique e →
                 binders-disjoint-σ σ e →
                 binders-unique ⦇⌜ e ⌟⦈⟨ u , σ ⟩
      BUAp     : ∀{e1 e2} →
                 binders-unique e1 →
                 binders-unique e2 →
                 binders-disjoint e1 e2 →
                 binders-unique (e1 ∘ e2)
      BUInl    : ∀{e τ} →
                 binders-unique e →
                 binders-unique (inl τ e)
      BUInr    : ∀{e τ} →
                 binders-unique e →
                 binders-unique (inr τ e)
      BUMatch  : ∀{e τ rs} →
                 binders-unique e →
                 binders-unique-zrs rs →
                 binders-disjoint-zrs rs e →
                 binders-unique (match e ·: τ of rs)
      BUPair   : ∀{e1 e2} →
                 binders-unique e1 →
                 binders-unique e2 →
                 binders-disjoint e1 e2 →
                 binders-unique ⟨ e1 , e2 ⟩
      BUFst    : ∀{e} →
                 binders-unique e →
                 binders-unique (fst e)
      BUSnd    : ∀{e} →
                 binders-unique e →
                 binders-unique (snd e)
              
  mutual
    data hole-binders-unique-p : pattrn → Set where
      HBUPUnit   : hole-binders-unique-p unit
      HBUPNum    : ∀{n} →
                   hole-binders-unique-p (N n)
      HBUPVar    : ∀{x} →
                   hole-binders-unique-p (X x)
      HBUPInl    : ∀{p} →
                   hole-binders-unique-p p →
                   hole-binders-unique-p (inl p)
      HBUPInr    : ∀{p} →
                   hole-binders-unique-p p →
                   hole-binders-unique-p (inr p)
      HBUPPair   : ∀{p1 p2} →
                   hole-binders-unique-p p1 →
                   hole-binders-unique-p p2 →
                   hole-binders-disjoint-p p1 p2 →
                   hole-binders-unique-p ⟨ p1 , p2 ⟩
      HBUPWild   : hole-binders-unique-p wild
      HBUPEHole  : ∀{w} →
                   hole-binders-unique-p ⦇-⦈[ w ]
      HBUPHole : ∀{p w τ} →
                   hole-binders-unique-p p →
                   hole-unbound-in-p w p →
                   hole-binders-unique-p ⦇⌜ p ⌟⦈[ w , τ ]

    data hole-binders-unique-r : rule → Set where
      HBURule : ∀{p e} →
                hole-binders-unique-p p →
                hole-binders-unique e →
                hole-binders-disjoint-p p e →
                hole-binders-unique-r (p => e)

    data hole-binders-unique-rs : rules → Set where
      HBUNoRules : hole-binders-unique-rs nil
      HBURules   : ∀{r rs} →
                   hole-binders-unique-r r →
                   hole-binders-unique-rs rs →
                   hole-binders-disjoint-r r rs →
                   hole-binders-unique-rs (r / rs)

    data hole-binders-unique-zrs : zrules → Set where
      HBUZRules : ∀{rs-pre r rs-post} →
                  hole-binders-unique-rs rs-pre →
                  hole-binders-unique-rs (r / rs-post) →
                  hole-binders-disjoint-rs rs-pre (r / rs-post) →
                  hole-binders-unique-zrs (rs-pre / r / rs-post)

    data hole-binders-unique-σ : subst-env → Set where
      HBUσId    : ∀{Γ} →
                  hole-binders-unique-σ (Id Γ)
      HBUσSubst : ∀{d y σ} →
                  hole-binders-unique d →
                  hole-binders-unique-σ σ →
                  hole-binders-disjoint-σ σ d →
                  hole-binders-unique-σ (Subst d y σ)

    data hole-binders-unique : ihexp → Set where
      HBUUnit   : hole-binders-unique unit
      HBUNum    : ∀{n} →
                  hole-binders-unique (N n)
      HBUVar    : ∀{x} →
                  hole-binders-unique (X x)
      HBULam    : ∀{x τ e} →
                  hole-binders-unique e →
                  hole-binders-unique (·λ x ·[ τ ] e)
      HBUEHole  : ∀{u σ} →
                  hole-binders-unique-σ σ →
                  hole-binders-unique ⦇-⦈⟨ u , σ ⟩
      HBUHole : ∀{e u σ} →
                  hole-binders-unique-σ σ →
                  hole-binders-unique e →
                  hole-binders-disjoint-σ σ e →
                  hole-binders-unique ⦇⌜ e ⌟⦈⟨ u , σ ⟩
      HBUAp     : ∀{e1 e2} →
                  hole-binders-unique e1 →
                  hole-binders-unique e2 →
                  hole-binders-disjoint e1 e2 →
                  hole-binders-unique (e1 ∘ e2)
      HBUInl    : ∀{e τ} →
                  hole-binders-unique e →
                  hole-binders-unique (inl τ e)
      HBUInr    : ∀{e τ} →
                  hole-binders-unique e →
                  hole-binders-unique (inr τ e)
      HBUMatch  : ∀{e τ rs} →
                  hole-binders-unique e →
                  hole-binders-unique-zrs rs →
                  hole-binders-disjoint-zrs rs e →
                  hole-binders-unique (match e ·: τ of rs)
      HBUPair   : ∀{e1 e2} →
                  hole-binders-unique e1 →
                  hole-binders-unique e2 →
                  hole-binders-disjoint e1 e2 →
                  hole-binders-unique ⟨ e1 , e2 ⟩
      HBUFst    : ∀{e} →
                  hole-binders-unique e →
                  hole-binders-unique (fst e)
      HBUSnd    : ∀{e} →
                  hole-binders-unique e →
                  hole-binders-unique (snd e)
