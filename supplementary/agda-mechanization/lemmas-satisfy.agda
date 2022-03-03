open import Prelude
open import constraints-core
open import contexts
open import core
open import notintro-decidable
open import result-judgements
open import satisfy-decidable
open import statics-core
open import value-judgements
open import xrefutable-decidable

module lemmas-satisfy where
  maysat-truth-not : ∀{e} →
                     (e ⊧̇? ·⊤ → ⊥)
  maysat-truth-not (CMSNotIntro _ () _)

  maysat-falsity-not : ∀{e} →
                       (e ⊧̇? ·⊥ → ⊥)
  maysat-falsity-not (CMSNotIntro _ _ ())

  satormay-falsity-not : ∀{e} →
                         (e ⊧̇†? ·⊥ → ⊥)
  satormay-falsity-not (CSMSMay (CMSNotIntro _ _ ()))

  notintro-sat-ref-not : ∀{e ξ} →
                         e notintro →
                         e ⊧̇ ξ →
                         ξ xrefutable →
                         ⊥
  notintro-sat-ref-not ni (CSNotIntroPair ni' sat1 sat2)
                       (RXPairL ref1) =
    notintro-sat-ref-not NVFst sat1 ref1
  notintro-sat-ref-not ni (CSNotIntroPair ni' sat1 sat2)
                       (RXPairR ref2) =
    notintro-sat-ref-not NVSnd sat2 ref2
  notintro-sat-ref-not ni (CSOrL sat1) (RXOr ref1 ref2) =
    notintro-sat-ref-not ni sat1 ref1
  notintro-sat-ref-not ni (CSOrR sat2) (RXOr ref1 ref2) =
    notintro-sat-ref-not ni sat2 ref2

                         
  not-ref-not-pos-not : ∀{ξ} →
                        (ξ xrefutable → ⊥) →
                        (ξ possible → ⊥) →
                        ⊥
  not-ref-not-pos-not {·⊤} ¬ref ¬pos = ¬pos PTruth
  not-ref-not-pos-not {·⊥} ¬ref ¬pos = ¬ref RXFalsity
  not-ref-not-pos-not {·?} ¬ref ¬pos = ¬pos PUnknown
  not-ref-not-pos-not {N n} ¬ref ¬pos = ¬pos PNum
  not-ref-not-pos-not {inl ξ} ¬ref ¬pos = ¬ref RXInl
  not-ref-not-pos-not {inr ξ} ¬ref ¬pos = ¬ref RXInr
  not-ref-not-pos-not {⟨ ξ1 , ξ2 ⟩} ¬ref ¬pos =
    not-ref-not-pos-not (λ ref1 → ¬ref (RXPairL ref1))
                        (λ pos1 →
                           not-ref-not-pos-not
                             (λ ref2 → ¬ref (RXPairR ref2))
                             (λ pos2 → ¬pos (PPair pos1 pos2)))
  not-ref-not-pos-not {ξ1 ∨ ξ2} ¬ref ¬pos =
    not-ref-not-pos-not (λ ref1 →
                           not-ref-not-pos-not
                             (λ ref2 → ¬ref (RXOr ref1 ref2))
                             (λ pos2 → ¬pos (POrR pos2)))
                        (λ pos1 → ¬pos (POrL pos1))

  sat-pos : ∀{ξ e} →
            e ⊧̇ ξ →
            ξ possible
  sat-pos CSTruth = PTruth
  sat-pos CSNum = PNum
  sat-pos (CSInl sat) = PInl (sat-pos sat)
  sat-pos (CSInr sat) = PInr (sat-pos sat)
  sat-pos (CSPair sat1 sat2) =
    PPair (sat-pos sat1) (sat-pos sat2)
  sat-pos (CSNotIntroPair ni sat1 sat2) =
    PPair (sat-pos sat1) (sat-pos sat2)
  sat-pos (CSOrL sat) = POrL (sat-pos sat)
  sat-pos (CSOrR sat) = POrR (sat-pos sat)
  
  maysat-pos : ∀{ξ e} →
               e ⊧̇? ξ →
               ξ possible
  maysat-pos CMSUnknown = PUnknown
  maysat-pos (CMSInl msat) = PInl (maysat-pos msat)
  maysat-pos (CMSInr msat) = PInr (maysat-pos msat)
  maysat-pos (CMSPairL msat1 sat2) =
    PPair (maysat-pos msat1) (sat-pos sat2)
  maysat-pos (CMSPairR sat1 msat2) =
    PPair (sat-pos sat1) (maysat-pos msat2)
  maysat-pos (CMSPair msat1 msat2) =
    PPair (maysat-pos msat1) (maysat-pos msat2)
  maysat-pos (CMSOrL msat1 ¬sat2) = POrL (maysat-pos msat1)
  maysat-pos (CMSOrR ¬sat1 msat2) = POrR (maysat-pos msat2)
  maysat-pos (CMSNotIntro ni ref pos) = pos

  satormay-pos : ∀{ξ e} →
                 e ⊧̇†? ξ →
                 ξ possible
  satormay-pos (CSMSSat sat) = sat-pos sat
  satormay-pos (CSMSMay msat) = maysat-pos msat
  
  not-ref-sat : ∀{ξ Γ Δ Δp e τ} →
                ξ :c: τ →
                Γ , Δ , Δp ⊢ e :: τ →
                e final →
                (ξ xrefutable → ⊥) →
                e ⊧̇ ξ
  not-ref-sat CTTruth wt fin ¬ref = CSTruth
  not-ref-sat CTFalsity wt fin ¬ref = abort (¬ref RXFalsity)
  not-ref-sat CTUnknown wt fin ¬ref = abort (¬ref RXUnknown)
  not-ref-sat CTNum wt fin ¬ref = abort (¬ref RXNum)
  not-ref-sat (CTInl ct) wt fin ¬ref = abort (¬ref RXInl)
  not-ref-sat (CTInr ct) wt fin ¬ref = abort (¬ref RXInr)
  not-ref-sat {ξ = ⟨ ξ1 , ξ2 ⟩} (CTPair ct1 ct2) wt fin ¬ref
    with xrefutable-dec ξ1
  ... | Inl ref1 = abort (¬ref (RXPairL ref1))
  ... | Inr ¬ref1
    with xrefutable-dec ξ2
  ... | Inl ref2 = abort (¬ref (RXPairR ref2))
  ... | Inr ¬ref2 with wt | fin
  ... | TVar x | FVal ()
  ... | TVar x | FIndet ()
  ... | TAp wt1 wt2 | FIndet ind =
    CSNotIntroPair NVAp
                   (not-ref-sat ct1 (TFst wt)
                                (FIndet (IFst (λ e1 e2 ()) ind)) ¬ref1)
                   (not-ref-sat ct2 (TSnd wt)
                                (FIndet (ISnd (λ e1 e2 ()) ind)) ¬ref2)
  ... | TMatchZPre wt' x | FIndet ind =
    CSNotIntroPair NVMatch
                   (not-ref-sat ct1 (TFst wt)
                                (FIndet (IFst (λ e1 e2 ()) ind)) ¬ref1)
                   (not-ref-sat ct2 (TSnd wt)
                                (FIndet (ISnd (λ e1 e2 ()) ind)) ¬ref2)
  ... | TMatchNZPre wt' x x₁ x₂ x₃ | FIndet ind =
    CSNotIntroPair NVMatch
                   (not-ref-sat ct1 (TFst wt)
                                (FIndet (IFst (λ e1 e2 ()) ind)) ¬ref1)
                   (not-ref-sat ct2 (TSnd wt)
                                (FIndet (ISnd (λ e1 e2 ()) ind)) ¬ref2)
  ... | TFst wt' | FIndet ind =
    CSNotIntroPair NVFst
                   (not-ref-sat ct1 (TFst wt)
                                (FIndet (IFst (λ e1 e2 ()) ind)) ¬ref1)
                   (not-ref-sat ct2 (TSnd wt)
                                (FIndet (ISnd (λ e1 e2 ()) ind)) ¬ref2)
  ... | TSnd wt' | FIndet ind =
    CSNotIntroPair NVSnd
                   (not-ref-sat ct1 (TFst wt)
                                (FIndet (IFst (λ e1 e2 ()) ind)) ¬ref1)
                   (not-ref-sat ct2 (TSnd wt)
                                (FIndet (ISnd (λ e1 e2 ()) ind)) ¬ref2)
  ... | TEHole u∈Δ st | FIndet ind =
    CSNotIntroPair NVEHole
                   (not-ref-sat ct1 (TFst wt)
                                (FIndet (IFst (λ e1 e2 ()) ind)) ¬ref1)
                   (not-ref-sat ct2 (TSnd wt)
                                (FIndet (ISnd (λ e1 e2 ()) ind)) ¬ref2)
  ... | THole u∈Δ st wt' | FIndet ind = 
    CSNotIntroPair NVHole
                   (not-ref-sat ct1 (TFst wt)
                                (FIndet (IFst (λ e1 e2 ()) ind)) ¬ref1)
                   (not-ref-sat ct2 (TSnd wt)
                                (FIndet (ISnd (λ e1 e2 ()) ind)) ¬ref2)
  ... | TPair wt1 wt2 | fin
    with pair-final fin
  ... | fin1 , fin2 =
    CSPair (not-ref-sat ct1 wt1 fin1 ¬ref1)
           (not-ref-sat ct2 wt2 fin2 ¬ref2)
  not-ref-sat {ξ = ξ1 ∨ ξ2} (CTOr ct1 ct2) wt fin ¬ref
    with xrefutable-dec ξ1
  ... | Inr ¬ref1 = CSOrL (not-ref-sat ct1 wt fin ¬ref1)
  ... | Inl ref1
    with xrefutable-dec ξ2
  ... | Inr ¬ref2 = CSOrR (not-ref-sat ct2 wt fin ¬ref2)
  ... | Inl ref2 = abort (¬ref (RXOr ref1 ref2))


  notintro-not-sat-ref : ∀{ξ e} →
                         e notintro →
                         (e ⊧̇ ξ → ⊥) →
                         ξ xrefutable
  notintro-not-sat-ref {·⊤} ni ¬sat = abort (¬sat CSTruth)
  notintro-not-sat-ref {·⊥} ni ¬sat = RXFalsity
  notintro-not-sat-ref {·?} ni ¬sat = RXUnknown
  notintro-not-sat-ref {N n} ni ¬sat = RXNum
  notintro-not-sat-ref {inl ξ} ni ¬sat = RXInl
  notintro-not-sat-ref {inr ξ} ni ¬sat = RXInr
  notintro-not-sat-ref {⟨ ξ1 , ξ2 ⟩} {e = e} ni ¬sat
    with satisfy-dec (fst e) ξ1 | satisfy-dec (snd e) ξ2
  ... | Inl sat1 | Inl sat2 =
    abort (¬sat (CSNotIntroPair ni sat1 sat2))
  ... | Inl sat1 | Inr ¬sat2 =
    RXPairR (notintro-not-sat-ref NVSnd ¬sat2)
  ... | Inr ¬sat1 | Inl sat2 =
    RXPairL (notintro-not-sat-ref NVFst ¬sat1)
  ... | Inr ¬sat1 | Inr ¬sat2 =
    RXPairL (notintro-not-sat-ref NVFst ¬sat1)
  notintro-not-sat-ref {ξ1 ∨ ξ2} ni ¬sat =
    RXOr (notintro-not-sat-ref ni (λ sat1 → ¬sat (CSOrL sat1)))
         (notintro-not-sat-ref ni (λ sat2 → ¬sat (CSOrR sat2)))
  
  notintro-maysat-ref : ∀{ξ e} →
                        e notintro →
                        e ⊧̇? ξ →
                        ξ xrefutable
  notintro-maysat-ref ni CMSUnknown = RXUnknown
  notintro-maysat-ref ni (CMSInl msat) = RXInl
  notintro-maysat-ref ni (CMSInr msat) = RXInr
  notintro-maysat-ref () (CMSPairL _ _)
  notintro-maysat-ref () (CMSPairR _ _)
  notintro-maysat-ref () (CMSPair msat1 msat2)
  notintro-maysat-ref ni (CMSOrL msat1 ¬sat2) =
    RXOr (notintro-maysat-ref ni msat1)
         (notintro-not-sat-ref ni ¬sat2)
  notintro-maysat-ref ni (CMSOrR ¬sat1 msat2) =
    RXOr (notintro-not-sat-ref ni ¬sat1)
         (notintro-maysat-ref ni msat2)
  notintro-maysat-ref ni (CMSNotIntro ni' ref pos) = ref
  
  satormay-inl : ∀{e τ ξ} →
                 e ⊧̇†? ξ →
                 inl τ e ⊧̇†? inl ξ
  satormay-inl (CSMSSat sat) = CSMSSat (CSInl sat)
  satormay-inl (CSMSMay msat) = CSMSMay (CMSInl msat)

  inl-satormay : ∀{e τ ξ} →
                 inl τ e ⊧̇†? inl ξ →
                 e ⊧̇†? ξ
  inl-satormay (CSMSSat (CSInl sat)) = CSMSSat sat
  inl-satormay (CSMSMay (CMSInl msat)) = CSMSMay msat

  satormay-inr : ∀{e τ ξ} →
                 e ⊧̇†? ξ →
                 inr τ e ⊧̇†? inr ξ
  satormay-inr (CSMSSat sat) = CSMSSat (CSInr sat)
  satormay-inr (CSMSMay msat) = CSMSMay (CMSInr msat)

  inr-satormay : ∀{e τ ξ} →
                 inr τ e ⊧̇†? inr ξ →
                 e ⊧̇†? ξ
  inr-satormay (CSMSSat (CSInr sat)) = CSMSSat sat
  inr-satormay (CSMSMay (CMSInr msat)) = CSMSMay msat
  
  satormay-pair : ∀{e1 e2 ξ1 ξ2} →
                  e1 ⊧̇†? ξ1 →
                  e2 ⊧̇†? ξ2 →
                  ⟨ e1 , e2 ⟩ ⊧̇†? ⟨ ξ1 , ξ2 ⟩
  satormay-pair (CSMSSat sat1) (CSMSSat sat2) =
    CSMSSat (CSPair sat1 sat2)
  satormay-pair (CSMSSat sat1) (CSMSMay msat2) =
    CSMSMay (CMSPairR sat1 msat2)
  satormay-pair (CSMSMay msat1) (CSMSSat sat2) =
    CSMSMay (CMSPairL msat1 sat2)
  satormay-pair (CSMSMay msat1) (CSMSMay msat2) =
    CSMSMay (CMSPair msat1 msat2)

  pair-satormay : ∀{e1 e2 ξ1 ξ2} →
                  ⟨ e1 , e2 ⟩ ⊧̇†? ⟨ ξ1 , ξ2 ⟩ →
                  (e1 ⊧̇†? ξ1) × (e2 ⊧̇†? ξ2)
  pair-satormay (CSMSSat (CSPair sat1 sat2)) =
    CSMSSat sat1 , CSMSSat sat2
  pair-satormay (CSMSMay (CMSPairL msat1 sat2)) =
    CSMSMay msat1 , CSMSSat sat2
  pair-satormay (CSMSMay (CMSPairR sat1 msat2)) =
    CSMSSat sat1 , CSMSMay msat2
  pair-satormay (CSMSMay (CMSPair msat1 msat2)) =
    CSMSMay msat1 , CSMSMay msat2
  
  satormay-or-l : ∀{e ξ1 ξ2} →
                  e ⊧̇†? ξ1 →
                  e ⊧̇†? (ξ1 ∨ ξ2)
  satormay-or-l (CSMSSat sat) = CSMSSat (CSOrL sat)
  satormay-or-l {e = e} {ξ2 = ξ2} (CSMSMay msat)
    with satisfy-dec e ξ2
  ... | Inl sat2 = CSMSSat (CSOrR sat2)
  ... | Inr ¬sat2 = CSMSMay (CMSOrL msat ¬sat2)
  
  satormay-or-r : ∀{e ξ1 ξ2} →
                  e ⊧̇†? ξ2 →
                  e ⊧̇†? (ξ1 ∨ ξ2)
  satormay-or-r (CSMSSat sat) = CSMSSat (CSOrR sat)
  satormay-or-r {e = e} {ξ1 = ξ1} (CSMSMay msat)
    with satisfy-dec e ξ1
  ... | Inl sat1 = CSMSSat (CSOrL sat1)
  ... | Inr ¬sat1 = CSMSMay (CMSOrR ¬sat1 msat)

  or-satormay : ∀{e ξ1 ξ2} →
                e ⊧̇†? (ξ1 ∨ ξ2) →
                (e ⊧̇†? ξ1) + (e ⊧̇†? ξ2)
  or-satormay (CSMSSat (CSOrL sat1)) = Inl (CSMSSat sat1)
  or-satormay (CSMSSat (CSOrR sat2)) = Inr (CSMSSat sat2)
  or-satormay (CSMSMay (CMSOrL msat1 ¬sat2)) = Inl (CSMSMay msat1)
  or-satormay (CSMSMay (CMSOrR ¬sat1 msat2)) = Inr (CSMSMay msat2)
  or-satormay (CSMSMay (CMSNotIntro ni (RXOr ref1 ref2)
                       (POrL pos1))) =
    Inl (CSMSMay (CMSNotIntro ni ref1 pos1))
  or-satormay (CSMSMay (CMSNotIntro ni (RXOr ref1 ref2)
                       (POrR pos2))) =
    Inr (CSMSMay (CMSNotIntro ni ref2 pos2))

  -- these two quick lemmas show that if à lambda
  -- satisfies a constraint, then anything at all must
  -- match that constraint
  lam-sat-all-sat : ∀{x e τ ξ e'} →
                    (·λ x ·[ τ ] e) ⊧̇ ξ →
                    e' ⊧̇ ξ
  lam-sat-all-sat CSTruth = CSTruth
  lam-sat-all-sat (CSOrL sat) =
    CSOrL (lam-sat-all-sat sat)
  lam-sat-all-sat (CSOrR sat) =
    CSOrR (lam-sat-all-sat sat)

  all-lam-maysat : ∀{x τ e ξ x' τ' e'} → 
                   (·λ x ·[ τ ] e) ⊧̇? ξ →
                   (·λ x' ·[ τ' ] e') ⊧̇? ξ
  all-lam-maysat CMSUnknown = CMSUnknown
  all-lam-maysat {ξ = ξ1 ∨ ξ2} {e' = e'}
                 (CMSOrL msat1 ¬sat2) =
    CMSOrL (all-lam-maysat msat1)
           (λ{sat2' → ¬sat2 (lam-sat-all-sat sat2')})
  all-lam-maysat (CMSOrR ¬sat1 msat2) =
    CMSOrR (λ{sat1' → ¬sat1 (lam-sat-all-sat sat1')})
           (all-lam-maysat msat2)

  -- the lemmas below show that constraints behave the
  -- same for all notintro expressions w.r.t. satisfication 
  
  -- if some notintro expression satisfies a constraint,
  -- then all notintro expressions satisfy a constraint
  all-notintro-sat : ∀{e ξ e'} →
                     e notintro →
                     e ⊧̇ ξ →
                     e' notintro →
                     e' ⊧̇ ξ
  all-notintro-sat ni CSTruth ni' = CSTruth
  all-notintro-sat ni (CSNotIntroPair x sat1 sat2) ni' =
    CSNotIntroPair ni' (all-notintro-sat NVFst sat1 NVFst)
                   (all-notintro-sat NVSnd sat2 NVSnd)
  all-notintro-sat ni (CSOrL sat) ni' =
    CSOrL (all-notintro-sat ni sat ni')
  all-notintro-sat ni (CSOrR sat) ni' =
    CSOrR (all-notintro-sat ni sat ni')

  -- if some notintro expression does not
  -- satisfy a constraint, then no notintro
  -- expression can satisfy the constraint
  all-notintro-not-sat : ∀{e ξ e'} →
                         e notintro →
                         (e ⊧̇ ξ → ⊥) →
                         e' notintro →
                         e' ⊧̇ ξ →
                         ⊥
  all-notintro-not-sat ni ¬sat ni' CSTruth = ¬sat CSTruth
  all-notintro-not-sat ni ¬sat ni'
                       (CSNotIntroPair _ sat1' sat2') =
    ¬sat (CSNotIntroPair ni
           (all-notintro-sat NVFst sat1' NVFst)
           (all-notintro-sat NVSnd sat2' NVSnd))
  all-notintro-not-sat ni ¬sat ni' (CSOrL sat') =
    ¬sat (CSOrL (all-notintro-sat ni' sat' ni))
  all-notintro-not-sat ni ¬sat ni' (CSOrR sat') =
    ¬sat (CSOrR (all-notintro-sat ni' sat' ni))

  -- if a constraint may be matched by some notintro
  -- expression, then it may be matched by any notintro
  -- expression
  all-notintro-maysat : ∀{e ξ e'} →
                        e notintro →
                        e ⊧̇? ξ →
                        e' notintro →
                        e' ⊧̇? ξ
  all-notintro-maysat ni CMSUnknown ni' = CMSUnknown
  all-notintro-maysat ni (CMSOrL msat1 ¬sat2) ni' =
    CMSOrL (all-notintro-maysat ni msat1 ni')
           (all-notintro-not-sat ni ¬sat2 ni')
  all-notintro-maysat ni (CMSOrR ¬sat1 msat2) ni' =
    CMSOrR (all-notintro-not-sat ni ¬sat1 ni')
           (all-notintro-maysat ni msat2 ni')
  all-notintro-maysat ni (CMSNotIntro _ ref pos) ni' =
    CMSNotIntro ni' ref pos

  entails-trans : ∀{τ ξ1 ξ2 ξ3} →
                  ξ1 ·: τ c⊧̇ ξ2 →
                  ξ3 :c: τ →
                  (∀{Δ Δp e} →
                   ∅ , Δ , Δp ⊢ e :: τ →
                   e val →
                   e ⊧̇ ξ2 →
                   e ⊧̇ ξ3) →
                  ξ1 ·: τ c⊧̇ ξ3
  entails-trans (Entails ct1 ct2 ent12) ct3 ent23 =
    Entails ct1 ct3
            (λ wt val satm1 →
               ent23 wt val (ent12 wt val satm1))
