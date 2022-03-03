open import Prelude
open import constraints-core
open import contexts
open import core
open import lemmas-patterns
open import lemmas-satisfy
open import patterns-core
open import result-judgements
open import statics-core

-- For the ITFailMatch instruction transition, we move the pointer
-- of a zippered list of rules one step forward. Essentially, we step
-- (rs-pre / r / (r-post / rs-post)) ↦
--     (rs-pre ++ [ r ] / r-post / rs-post).
-- 
-- To prove, say, preservation, we need to reason about the constraint
-- emitted by all previously seen rules. However, our judgement for
-- determining this constraint builds it inductively from the head
-- of the list, e.g., if r emits ξr, r' emits ξr', and rs emits ξrs,
-- then ξr / (ξr' / ξrs) emits ξr ∨ (ξr' ∨ ξrs). Thus, appending to
-- the end of a list must ∨ the constraint at the deepest nested level,
-- not the top level. That is, rs ++ [ r ] does not emit ξrs ∨ ξr,
-- but rather ξrs is a sequence of nested ∨s, and ξr must be added to the
-- end of this list. This necessitates the ∨+ function below which
-- performs that operation.
--
-- Most of this module consists of easy lemmas showing that
-- ξ1 ∨+ ξ2 is semantically equivalent to ξ1 ∨ ξ2, then proves
-- the result mentioned above.
module lemmas-or-append where
  _∨+_ : constr → constr → constr
  ·⊤ ∨+ ξ = ·⊤ ∨ ξ
  ·⊥ ∨+ ξ = ·⊥ ∨ ξ
  ·? ∨+ ξ = ·? ∨ ξ
  (N n) ∨+ ξ = (N n) ∨ ξ
  (inl ξ1) ∨+ ξ = (inl ξ1) ∨ ξ
  (inr ξ1) ∨+ ξ = (inr ξ1) ∨ ξ
  ⟨ ξ1 , ξ2 ⟩ ∨+ ξ = ⟨ ξ1 , ξ2 ⟩ ∨ ξ
  (ξ1 ∨ ξ2) ∨+ ξ = ξ1 ∨ (ξ2 ∨+ ξ)

  ∨+-type : ∀{ξ1 ξ2 τ} →
            ξ1 :c: τ →
            ξ2 :c: τ →
            (ξ1 ∨+ ξ2) :c: τ
  ∨+-type CTTruth ct2 = CTOr CTTruth ct2
  ∨+-type CTFalsity ct2 = CTOr CTFalsity ct2
  ∨+-type CTUnknown ct2 = CTOr CTUnknown ct2
  ∨+-type CTNum ct2 = CTOr CTNum ct2
  ∨+-type (CTInl ct1) ct2 = CTOr (CTInl ct1) ct2
  ∨+-type (CTInr ct1) ct2 = CTOr (CTInr ct1) ct2
  ∨+-type (CTPair ct1₁ ct1₂) ct2 =
    CTOr (CTPair ct1₁ ct1₂) ct2
  ∨+-type (CTOr ct1₁ ct1₂) ct2 =
    CTOr ct1₁ (∨+-type ct1₂ ct2)
  
  ref-∨+-ref-∨ : ∀{ξ1 ξ2} →
                 (ξ1 ∨+ ξ2) xrefutable →
                 (ξ1 ∨ ξ2) xrefutable
  ref-∨+-ref-∨ {ξ1 = ·⊤} ref = ref
  ref-∨+-ref-∨ {ξ1 = ·⊥} ref = ref
  ref-∨+-ref-∨ {ξ1 = ·?} ref = ref
  ref-∨+-ref-∨ {ξ1 = N n} ref = ref
  ref-∨+-ref-∨ {ξ1 = inl ξ1} ref = ref
  ref-∨+-ref-∨ {ξ1 = inr ξ1} ref = ref
  ref-∨+-ref-∨ {ξ1 = ⟨ ξ1₁ , ξ1₂ ⟩} ref = ref
  ref-∨+-ref-∨ {ξ1 = ξ1₁ ∨ ξ1₂} (RXOr ref1₁ ref)
    with ref-∨+-ref-∨ ref
  ... | RXOr ref1₂ ref2 =
    RXOr (RXOr ref1₁ ref1₂) ref2

  ref-∨-ref-∨+ : ∀{ξ1 ξ2} →
                 (ξ1 ∨ ξ2) xrefutable →
                 (ξ1 ∨+ ξ2) xrefutable
  ref-∨-ref-∨+ {ξ1 = ·⊤} ref = ref
  ref-∨-ref-∨+ {ξ1 = ·⊥} ref = ref
  ref-∨-ref-∨+ {ξ1 = ·?} ref = ref
  ref-∨-ref-∨+ {ξ1 = N n} ref = ref
  ref-∨-ref-∨+ {ξ1 = inl ξ1} ref = ref
  ref-∨-ref-∨+ {ξ1 = inr ξ1} ref = ref
  ref-∨-ref-∨+ {ξ1 = ⟨ ξ1₁ , ξ1₂ ⟩} ref = ref
  ref-∨-ref-∨+ {ξ1 = ξ1₁ ∨ ξ1₂}
               (RXOr (RXOr ref1₁ ref1₂) ref2) =
    RXOr ref1₁ (ref-∨-ref-∨+ (RXOr ref1₂ ref2))
  
  pos-∨+-pos-∨ : ∀{ξ1 ξ2} →
                 (ξ1 ∨+ ξ2) possible →
                 (ξ1 ∨ ξ2) possible
  pos-∨+-pos-∨ {ξ1 = ·⊤} pos = pos
  pos-∨+-pos-∨ {ξ1 = ·⊥} pos = pos
  pos-∨+-pos-∨ {ξ1 = ·?} pos = pos
  pos-∨+-pos-∨ {ξ1 = N n} pos = pos
  pos-∨+-pos-∨ {ξ1 = inl ξ1} pos = pos
  pos-∨+-pos-∨ {ξ1 = inr ξ1} pos = pos
  pos-∨+-pos-∨ {ξ1 = ⟨ ξ1₁ , ξ1₂ ⟩} pos = pos
  pos-∨+-pos-∨ {ξ1 = ξ1₁ ∨ ξ1₂} (POrL pos1₁) =
    POrL (POrL pos1₁)
  pos-∨+-pos-∨ {ξ1 = ξ1₁ ∨ ξ1₂} (POrR pos)
    with pos-∨+-pos-∨ pos
  ... | POrL pos1₂ = POrL (POrR pos1₂)
  ... | POrR pos2 = POrR pos2

  pos-∨-pos-∨+ : ∀{ξ1 ξ2} →
                 (ξ1 ∨ ξ2) possible →
                 (ξ1 ∨+ ξ2) possible
  pos-∨-pos-∨+ {ξ1 = ·⊤} pos = pos
  pos-∨-pos-∨+ {ξ1 = ·⊥} pos = pos
  pos-∨-pos-∨+ {ξ1 = ·?} pos = pos
  pos-∨-pos-∨+ {ξ1 = N n} pos = pos
  pos-∨-pos-∨+ {ξ1 = inl ξ1} pos = pos
  pos-∨-pos-∨+ {ξ1 = inr ξ1} pos = pos
  pos-∨-pos-∨+ {ξ1 = ⟨ ξ1₁ , ξ1₂ ⟩} pos = pos
  pos-∨-pos-∨+ {ξ1 = ξ1₁ ∨ ξ1₂} (POrL (POrL pos1₁)) =
    POrL pos1₁
  pos-∨-pos-∨+ {ξ1 = ξ1₁ ∨ ξ1₂} (POrL (POrR pos1₂)) =
    POrR (pos-∨-pos-∨+ (POrL pos1₂))
  pos-∨-pos-∨+ {ξ1 = ξ1₁ ∨ ξ1₂} (POrR pos) =
    POrR (pos-∨-pos-∨+ (POrR pos))
  
  sat-∨+-sat-∨ : ∀{e ξ1 ξ2} →
                 e ⊧̇ (ξ1 ∨+ ξ2) →
                 e ⊧̇ (ξ1 ∨ ξ2)
  sat-∨+-sat-∨ {ξ1 = ·⊤} sat = sat
  sat-∨+-sat-∨ {ξ1 = ·⊥} sat = sat
  sat-∨+-sat-∨ {ξ1 = ·?} sat = sat
  sat-∨+-sat-∨ {ξ1 = N n} sat = sat
  sat-∨+-sat-∨ {ξ1 = inl ξ1} sat = sat
  sat-∨+-sat-∨ {ξ1 = inr ξ1} sat = sat
  sat-∨+-sat-∨ {ξ1 = ⟨ ξ1₁ , ξ1₂ ⟩} sat = sat
  sat-∨+-sat-∨ {ξ1 = ξ1₁ ∨ ξ1₂} (CSOrL sat) = CSOrL (CSOrL sat)
  sat-∨+-sat-∨ {ξ1 = ξ1₁ ∨ ξ1₂} (CSOrR sat)
    with sat-∨+-sat-∨ sat
  ... | CSOrL sat1₂ = CSOrL (CSOrR sat1₂)
  ... | CSOrR sat2 = CSOrR sat2

  sat-∨-sat-∨+ : ∀{e ξ1 ξ2} →
                 e ⊧̇ (ξ1 ∨ ξ2) →
                 e ⊧̇ (ξ1 ∨+ ξ2)
  sat-∨-sat-∨+ {ξ1 = ·⊤} sat = sat
  sat-∨-sat-∨+ {ξ1 = ·⊥} sat = sat
  sat-∨-sat-∨+ {ξ1 = ·?} sat = sat
  sat-∨-sat-∨+ {ξ1 = N n} sat = sat
  sat-∨-sat-∨+ {ξ1 = inl ξ1} sat = sat
  sat-∨-sat-∨+ {ξ1 = inr ξ1} sat = sat
  sat-∨-sat-∨+ {ξ1 = ⟨ ξ1₁ , ξ1₂ ⟩} sat = sat
  sat-∨-sat-∨+ {ξ1 = ξ1₁ ∨ ξ1₂} (CSOrL (CSOrL sat1₁)) =
    CSOrL sat1₁
  sat-∨-sat-∨+ {ξ1 = ξ1₁ ∨ ξ1₂} (CSOrL (CSOrR sat1₂)) =
    CSOrR (sat-∨-sat-∨+ (CSOrL sat1₂))
  sat-∨-sat-∨+ {ξ1 = ξ1₁ ∨ ξ1₂} (CSOrR sat2) =
    CSOrR (sat-∨-sat-∨+ (CSOrR sat2))
  
  maysat-∨+-maysat-∨ : ∀{e ξ1 ξ2} →
                       e ⊧̇? (ξ1 ∨+ ξ2) →
                       e ⊧̇? (ξ1 ∨ ξ2)
  maysat-∨+-maysat-∨ {ξ1 = ·⊤} msat = msat
  maysat-∨+-maysat-∨ {ξ1 = ·⊥} msat = msat
  maysat-∨+-maysat-∨ {ξ1 = ·?} msat = msat
  maysat-∨+-maysat-∨ {ξ1 = N n} msat = msat
  maysat-∨+-maysat-∨ {ξ1 = inl ξ1} msat = msat
  maysat-∨+-maysat-∨ {ξ1 = inr ξ1} msat = msat
  maysat-∨+-maysat-∨ {ξ1 = ⟨ ξ1₁ , ξ1₂ ⟩} msat = msat
  maysat-∨+-maysat-∨ {ξ1 = ξ1₁ ∨ ξ1₂} (CMSOrL msat1₁ ¬sat) =
    CMSOrL (CMSOrL msat1₁
                   (λ sat1₂ → ¬sat (sat-∨-sat-∨+ (CSOrL sat1₂))))
           (λ sat2 → ¬sat (sat-∨-sat-∨+ (CSOrR sat2)))
  maysat-∨+-maysat-∨ {ξ1 = ξ1₁ ∨ ξ1₂} (CMSOrR ¬sat1₁ msat)
    with maysat-∨+-maysat-∨ msat
  ... | CMSOrL msat1₂ ¬sat2 =
    CMSOrL (CMSOrR ¬sat1₁ msat1₂) ¬sat2
  ... | CMSOrR ¬sat1₂ msat2 =
    CMSOrR (λ{(CSOrL sat1₁) → ¬sat1₁ sat1₁
            ; (CSOrR sat1₂) → ¬sat1₂ sat1₂})
           msat2
  ... | CMSNotIntro ni (RXOr ref1₂ ref2) (POrL pos1₂) =
    CMSNotIntro ni
                (RXOr (RXOr (notintro-not-sat-ref ni ¬sat1₁)
                            ref1₂)
                      ref2)
                (POrL (POrR pos1₂))
  ... | CMSNotIntro ni (RXOr ref1₂ ref2) (POrR pos2) =
    CMSNotIntro ni (RXOr (RXOr (notintro-not-sat-ref ni ¬sat1₁)
                               ref1₂)
                         ref2)
                (POrR pos2)
  maysat-∨+-maysat-∨ {ξ1 = ξ1₁ ∨ ξ1₂}
                     (CMSNotIntro ni (RXOr ref1₁ ref)
                                  (POrL pos1₁))
    with ref-∨+-ref-∨ ref
  ... | RXOr ref1₂ ref2 =
    CMSNotIntro ni (RXOr (RXOr ref1₁ ref1₂) ref2)
                (POrL (POrL pos1₁))
  maysat-∨+-maysat-∨ {ξ1 = ξ1₁ ∨ ξ1₂}
                     (CMSNotIntro ni (RXOr ref1₁ ref)
                                  (POrR pos))
    with ref-∨+-ref-∨ ref | pos-∨+-pos-∨ pos
  ... | RXOr ref1₂ ref2 | POrL pos1₂ =
    CMSNotIntro ni (RXOr (RXOr ref1₁ ref1₂) ref2)
                (POrL (POrR pos1₂))
  ... | RXOr ref1₂ ref2 | POrR pos2 =
    CMSNotIntro ni (RXOr (RXOr ref1₁ ref1₂) ref2)
                (POrR pos2)

  maysat-∨-maysat-∨+ : ∀{e ξ1 ξ2} →
                       e ⊧̇? (ξ1 ∨ ξ2) →
                       e ⊧̇? (ξ1 ∨+ ξ2)
  maysat-∨-maysat-∨+ {ξ1 = ·⊤} msat = msat
  maysat-∨-maysat-∨+ {ξ1 = ·⊥} msat = msat
  maysat-∨-maysat-∨+ {ξ1 = ·?} msat = msat
  maysat-∨-maysat-∨+ {ξ1 = N n} msat = msat
  maysat-∨-maysat-∨+ {ξ1 = inl ξ1} msat = msat
  maysat-∨-maysat-∨+ {ξ1 = inr ξ1} msat = msat
  maysat-∨-maysat-∨+ {ξ1 = ⟨ ξ1₁ , ξ1₂ ⟩} msat = msat
  maysat-∨-maysat-∨+ {e = e} {ξ1 = ξ1₁ ∨ ξ1₂} {ξ2 = ξ2}
                     (CMSOrL (CMSOrL msat1₁ ¬sat1₂) ¬sat2) =
    CMSOrL msat1₁ ¬sat
    where
      ¬sat : e ⊧̇ (ξ1₂ ∨+ ξ2) → ⊥
      ¬sat sat with sat-∨+-sat-∨ sat
      ... | CSOrL sat1₂ = ¬sat1₂ sat1₂
      ... | CSOrR sat2 = ¬sat2 sat2
  maysat-∨-maysat-∨+ {ξ1 = ξ1₁ ∨ ξ1₂}
                     (CMSOrL (CMSOrR ¬sat1₁ msat1₂) ¬sat2) =
    CMSOrR ¬sat1₁
           (maysat-∨-maysat-∨+ (CMSOrL msat1₂ ¬sat2))
 
  maysat-∨-maysat-∨+ {ξ1 = ξ1₁ ∨ ξ1₂}
                     (CMSOrL (CMSNotIntro ni (RXOr ref1₁ ref1₂)
                                          (POrL pos1₁))
                             ¬sat2) =
    CMSNotIntro ni
                (RXOr ref1₁
                      (ref-∨-ref-∨+
                        (RXOr ref1₂
                              (notintro-not-sat-ref ni ¬sat2))))
                (POrL pos1₁)
  maysat-∨-maysat-∨+ {ξ1 = ξ1₁ ∨ ξ1₂}
                     (CMSOrL (CMSNotIntro ni (RXOr ref1₁ ref1₂)
                                          (POrR pos1₂))
                             ¬sat2) =
    CMSNotIntro ni
                (RXOr ref1₁
                      (ref-∨-ref-∨+
                        (RXOr ref1₂
                              (notintro-not-sat-ref ni ¬sat2))))
                (POrR (pos-∨-pos-∨+ (POrL pos1₂)))
  maysat-∨-maysat-∨+ {ξ1 = ξ1₁ ∨ ξ1₂} (CMSOrR ¬sat1 msat2) =
    CMSOrR (λ sat1₁ → ¬sat1 (CSOrL sat1₁))
           (maysat-∨-maysat-∨+
             (CMSOrR (λ sat1₂ → ¬sat1 (CSOrR sat1₂)) msat2))
  maysat-∨-maysat-∨+ {ξ1 = ξ1₁ ∨ ξ1₂}
                     (CMSNotIntro ni (RXOr (RXOr ref1₁ ref1₂) ref2)
                     (POrL (POrL pos1₁))) =
    CMSNotIntro ni (RXOr ref1₁ (ref-∨-ref-∨+ (RXOr ref1₂ ref2)))
                (POrL pos1₁)
  maysat-∨-maysat-∨+ {ξ1 = ξ1₁ ∨ ξ1₂}
                     (CMSNotIntro ni (RXOr (RXOr ref1₁ ref1₂) ref2)
                     (POrL (POrR pos1₂))) =
    CMSNotIntro ni (RXOr ref1₁ (ref-∨-ref-∨+ (RXOr ref1₂ ref2)))
                (POrR (pos-∨-pos-∨+ (POrL pos1₂)))
  maysat-∨-maysat-∨+ {ξ1 = ξ1₁ ∨ ξ1₂}
                     (CMSNotIntro ni (RXOr (RXOr ref1₁ ref1₂) ref2)
                                  (POrR pos2)) =
    CMSNotIntro ni (RXOr ref1₁ (ref-∨-ref-∨+ (RXOr ref1₂ ref2)))
                (POrR (pos-∨-pos-∨+ (POrR pos2)))

  satormay-∨+-satormay-∨ : ∀{e ξ1 ξ2} →
                           e ⊧̇†? (ξ1 ∨+ ξ2) →
                           e ⊧̇†? (ξ1 ∨ ξ2)
  satormay-∨+-satormay-∨ (CSMSSat sat) =
    CSMSSat (sat-∨+-sat-∨ sat)
  satormay-∨+-satormay-∨ (CSMSMay msat) =
    CSMSMay (maysat-∨+-maysat-∨ msat)

  satormay-∨-satormay-∨+ : ∀{e ξ1 ξ2} →
                           e ⊧̇†? (ξ1 ∨ ξ2) →
                           e ⊧̇†? (ξ1 ∨+ ξ2)
  satormay-∨-satormay-∨+ (CSMSSat sat) =
    CSMSSat (sat-∨-sat-∨+ sat)
  satormay-∨-satormay-∨+ (CSMSMay msat) =
    CSMSMay (maysat-∨-maysat-∨+ msat)
  
  -- a pattern by itself should never emit a constraint involving
  -- an ∨, so ξp ∨+ ξ behaves just like ξp ∨ ξ
  pattern-∨+ : ∀{Δp p τ ξp Γp} →
               Δp ⊢ p :: τ [ ξp ]⊣ Γp →
               (ξ : constr) →
               ξp ∨+ ξ == ξp ∨ ξ
  pattern-∨+ PTUnit ξ = refl
  pattern-∨+ PTVar ξ = refl
  pattern-∨+ PTNum ξ = refl
  pattern-∨+ (PTInl pt) ξ = refl
  pattern-∨+ (PTInr pt) ξ = refl
  pattern-∨+ (PTPair Γ1##Γ2 pt1 pt2) ξ = refl
  pattern-∨+ (PTEHole w∈Δp) ξ = refl
  pattern-∨+ (PTHole w∈Δp pt) ξ = refl
  pattern-∨+ PTWild ξ = refl

  -- appending more rules to the end of a list of rules
  -- ∨+s the emitted constraints
  rules-erase-constr : ∀{rs-pre r rs-post rss Γ Δ Δp τ ξpre ξrest τ'} →
                       erase-r (rs-pre / r / rs-post) rss →
                       Γ , Δ , Δp ⊢ rs-pre ::s τ [ ξpre ]=> τ' →
                       Γ , Δ , Δp ⊢ (r / rs-post) ::s τ [ ξrest ]=> τ' →
                       Γ , Δ , Δp ⊢ rss ::s τ [ ξpre ∨+ ξrest ]=> τ'
  rules-erase-constr
    {rs-pre = (p => e) / nil} {r = r} {rs-post = rs-post}
    {Γ = Γ} {Δ = Δ} {Δp = Δp}
    {τ = τ} {ξpre = ξpre} {ξrest = ξrest} {τ' = τ'}
    (ERNZPre ERZPre)
    (RTOneRule (RTRule pt Γ##Γp wt')) restt =
    tr (λ qq → Γ , Δ , Δp ⊢ (p => e) / (r / rs-post) ::s τ [ qq ]=> τ')
       (! (pattern-∨+ pt ξrest))
       (RTRules (RTRule pt Γ##Γp wt') restt)
  rules-erase-constr
    {rs-pre = r' / (_ / _)}
    (ERNZPre (ERNZPre er))
    (RTRules (RTRule pt Γ##Γp wt') rst') restt =
    RTRules (RTRule pt Γ##Γp wt')
            (rules-erase-constr (ERNZPre er) rst' restt)


  -- same as above but for the rule typing judgement
  -- without the target type
  rules-erase-constr-no-target : ∀{rs-pre r rs-post rss Δp τ ξpre ξrest} →
                                 erase-r (rs-pre / r / rs-post) rss →
                                 Δp ⊢ rs-pre ::s τ [ ξpre ] →
                                 Δp ⊢ (r / rs-post) ::s τ [ ξrest ] →
                                 Δp ⊢ rss ::s τ [ ξpre ∨+ ξrest ]
  rules-erase-constr-no-target
    {rs-pre = (p => e) / nil} {r = r} {rs-post = rs-post}
    {Δp = Δp} {τ = τ} {ξpre = ξpre} {ξrest = ξrest}
    (ERNZPre ERZPre) (RTOneRule pt) restt =
    tr (λ qq → Δp ⊢ (p => e) / (r / rs-post) ::s τ [ qq ])
       (! (pattern-∨+ pt ξrest))
       (RTRules pt restt)
  rules-erase-constr-no-target
    {rs-pre = r' / (_ / _)}
    (ERNZPre (ERNZPre er)) (RTRules rt' rst') restt =
    RTRules rt' (rules-erase-constr-no-target (ERNZPre er) rst' restt)

  -- same as above but for the rule typing judgement
  -- keeping track of nonredundancy
  rules-erase-constr-nonredundant : ∀{rs-pre r rs-post rss Δp τ ξnr ξpre ξrest} →
                                    ξnr :c: τ →
                                    erase-r (rs-pre / r / rs-post) rss →
                                    Δp ⊢ rs-pre ::s τ [ ξnr nr/ ξpre ] →
                                    Δp ⊢ (r / rs-post) ::s τ [ ξnr ∨ ξpre nr/ ξrest ] →
                                    Δp ⊢ rss ::s τ [ ξnr nr/ ξpre ∨+ ξrest ]
  rules-erase-constr-nonredundant
    {rs-pre = (p => e) / nil} {r = r} {rs-post = rs-post}
    {Δp = Δp} {τ = τ} {ξnr = ξnr} {ξpre = ξpre} {ξrest = ξrest}
    ctnr  (ERNZPre ERZPre) (RTOneRule pt ¬red) restt =
    tr (λ qq → Δp ⊢ (p => e) / (r / rs-post) ::s τ [ ξnr nr/ qq ])
       (! (pattern-∨+ pt ξrest))
       (RTRules pt ¬red restt)
  rules-erase-constr-nonredundant
    {rs-pre = r' / (_ / _)} {τ = τ} {ξnr = ξnr} {ξpre = ξr ∨ ξrs}
    ctnr (ERNZPre (ERNZPre er)) (RTRules pt ¬red rst) restt =
      RTRules pt ¬red
              (rules-erase-constr-nonredundant
                (CTOr ctnr (pattern-constr-same-type pt))
                (ERNZPre er)
                rst
                (weaken-nonredundant
                  (CTOr ctnr
                        (CTOr (pattern-constr-same-type pt)
                              (rules-constr-same-type-nonredundant rst)))
                  restt
                  ent))
    where
      ent : ∀{Δ Δp e} →
            ∅ , Δ , Δp ⊢ e :: τ →
            e val →
            e ⊧̇ ((ξnr ∨ ξr) ∨ ξrs) →
            e ⊧̇ (ξnr ∨ (ξr ∨ ξrs))
      ent wt eval (CSOrL (CSOrL sat)) = CSOrL sat
      ent wt eval (CSOrL (CSOrR sat)) = CSOrR (CSOrL sat)
      ent wt eval (CSOrR sat) = CSOrR (CSOrR sat)
