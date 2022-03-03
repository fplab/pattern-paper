open import Nat
open import Prelude
open import constraints-core
open import contexts
open import core
open import lemmas-satisfy
open import notintro-decidable
open import possible-decidable
open import result-judgements
open import satisfy-decidable
open import statics-core
open import xrefutable-decidable

-- theorem showing that the various satisfaction
-- judgements capture all cases
module satisfy-exclusive where
  -- result of the exclusivity theorem
  data ExSat (e : ihexp) (ξ : constr) : Set where
    Satisfy    : (e ⊧̇ ξ)     → (e ⊧̇? ξ → ⊥) → (e ⊧̇†? ξ)     → ExSat e ξ
    MaySatisfy : (e ⊧̇ ξ → ⊥) → (e ⊧̇? ξ)     → (e ⊧̇†? ξ)     → ExSat e ξ
    NotSatisfy : (e ⊧̇ ξ → ⊥) → (e ⊧̇? ξ → ⊥) → (e ⊧̇†? ξ → ⊥) → ExSat e ξ
  

  -- exclusivity of satisfaction
  --
  -- for a final expression e and a constraint ξ of the same type,
  -- exactly one of e ⊧̇ ξ, e ⊧̇? ξ, and ¬ (e ⊧̇†? ξ) holds
  satisfy-exclusive : ∀{ξ τ Δ Δp e} →
                      ξ :c: τ →
                      ∅ , Δ , Δp ⊢ e :: τ →
                      e final →
                      ExSat e ξ
  satisfy-exclusive CTTruth wt fin =
    Satisfy CSTruth maysat-truth-not (CSMSSat CSTruth)
  satisfy-exclusive CTFalsity wt fin =
    NotSatisfy (λ ()) maysat-falsity-not satormay-falsity-not
  satisfy-exclusive CTUnknown wt fin =
    MaySatisfy (λ ()) CMSUnknown (CSMSMay CMSUnknown)
    
  -- num cases
  satisfy-exclusive {e = N n} (CTNum {n = m})
                    TNum fin with nat-dec n m
  ... | Inl refl = Satisfy CSNum (λ{ (CMSNotIntro () ref pos)})
                           (CSMSSat CSNum)
  ... | Inr n≠m = NotSatisfy (λ{CSNum → n≠m refl})
                             (λ{(CMSNotIntro () ref pos)})
                             λ{(CSMSSat CSNum) → n≠m refl
                             ; (CSMSMay (CMSNotIntro () _ _))}
  satisfy-exclusive CTNum (TAp wt1 wt2) fin =
    MaySatisfy (λ ()) (CMSNotIntro NVAp RXNum PNum)
               (CSMSMay (CMSNotIntro NVAp RXNum PNum))
  satisfy-exclusive CTNum (TMatchZPre wt x) fin =
    MaySatisfy (λ ()) (CMSNotIntro NVMatch RXNum PNum)
               (CSMSMay (CMSNotIntro NVMatch RXNum PNum))
  satisfy-exclusive CTNum (TMatchNZPre wt x x₁ x₂ x₃) fin =
    MaySatisfy (λ ()) (CMSNotIntro NVMatch RXNum PNum)
               (CSMSMay (CMSNotIntro NVMatch RXNum PNum))
  satisfy-exclusive CTNum (TFst wt) fin =
    MaySatisfy (λ ()) (CMSNotIntro NVFst RXNum PNum)
               (CSMSMay (CMSNotIntro NVFst RXNum PNum))
  satisfy-exclusive CTNum (TSnd wt) fin =
    MaySatisfy (λ ()) (CMSNotIntro NVSnd RXNum PNum)
               (CSMSMay (CMSNotIntro NVSnd RXNum PNum))
  satisfy-exclusive CTNum (TEHole u∈Δ st) fin =
    MaySatisfy (λ ()) (CMSNotIntro NVEHole RXNum PNum)
               (CSMSMay (CMSNotIntro NVEHole RXNum PNum))
  satisfy-exclusive CTNum (THole u∈Δ st wt) fin =
    MaySatisfy (λ ()) (CMSNotIntro NVHole RXNum PNum)
               (CSMSMay (CMSNotIntro NVHole RXNum PNum))

  -- inl cases
  satisfy-exclusive {ξ = ξ} {e = e} (CTInl ct) wt fin
    with notintro-dec e
  ... | Inl ni
    with xrefutable-dec ξ | possible-dec ξ
  ... | Inl ref | Inl pos =
    MaySatisfy (λ sat → notintro-sat-ref-not ni sat ref)
               (CMSNotIntro ni ref pos)
               (CSMSMay (CMSNotIntro ni ref pos))
  ... | Inl ref | Inr ¬pos =
    NotSatisfy (λ sat → notintro-sat-ref-not ni sat ref)
               (λ msat → ¬pos (maysat-pos msat))
               (λ satm → ¬pos (satormay-pos satm))
  ... | Inr ¬ref | Inl pos =
    Satisfy (not-ref-sat (CTInl ct) wt fin ¬ref)
            (λ{(CMSNotIntro _ ref _) → ¬ref ref} )
            (CSMSSat (not-ref-sat (CTInl ct) wt fin ¬ref))
  ... | Inr ¬ref | Inr ¬pos = abort (not-ref-not-pos-not ¬ref ¬pos)
  satisfy-exclusive {ξ = ξ} (CTInl ct) wt fin | Inr ¬ni
    with wt
  ... | TAp _ _ = abort (¬ni NVAp)
  ... | TMatchZPre _ _ = abort (¬ni NVMatch)
  ... | TMatchNZPre _ _ _ _ _ = abort (¬ni NVMatch)
  ... | TFst _ = abort (¬ni NVFst)
  ... | TSnd _ = abort (¬ni NVSnd)
  ... | TEHole _ _ = abort (¬ni NVEHole)
  ... | THole _ _ _ = abort (¬ni NVHole)
  ... | TInr _ =
    NotSatisfy (λ ())
               (λ{(CMSNotIntro () _ _)})
               (λ{(CSMSMay (CMSNotIntro () _ _))})
  ... | TInl wt'
    with satisfy-exclusive ct wt' (inl-final fin)
  ... | Satisfy sat ¬msat satm =
    Satisfy (CSInl sat)
            (λ{(CMSInl msat) → ¬msat msat})
            (CSMSSat (CSInl sat))
  ... | MaySatisfy ¬sat msat satm =
    MaySatisfy (λ{(CSInl sat) → ¬sat sat})
               (CMSInl msat)
               (CSMSMay (CMSInl msat))
  ... | NotSatisfy ¬sat ¬msat ¬satm =
    NotSatisfy (λ{(CSInl sat) → ¬sat sat})
               (λ{(CMSInl msat) → ¬msat msat})
               (λ{(CSMSSat (CSInl sat)) → ¬sat sat
                ; (CSMSMay (CMSInl msat)) → ¬msat msat})

  -- inr cases 
  satisfy-exclusive {ξ = ξ} {e = e} (CTInr ct) wt fin
    with notintro-dec e
  ... | Inl ni
    with xrefutable-dec ξ | possible-dec ξ
  ... | Inl ref | Inl pos =
    MaySatisfy (λ sat → notintro-sat-ref-not ni sat ref)
               (CMSNotIntro ni ref pos)
               (CSMSMay (CMSNotIntro ni ref pos))
  ... | Inl ref | Inr ¬pos =
    NotSatisfy (λ sat → notintro-sat-ref-not ni sat ref)
               (λ msat → ¬pos (maysat-pos msat))
               (λ satm → ¬pos (satormay-pos satm))
  ... | Inr ¬ref | Inl pos =
    Satisfy (not-ref-sat (CTInr ct) wt fin ¬ref)
            (λ{(CMSNotIntro _ ref _) → ¬ref ref} )
            (CSMSSat (not-ref-sat (CTInr ct) wt fin ¬ref))
  ... | Inr ¬ref | Inr ¬pos = abort (not-ref-not-pos-not ¬ref ¬pos)
  satisfy-exclusive {ξ = ξ} (CTInr ct) wt fin | Inr ¬ni
    with wt
  ... | TAp _ _ = abort (¬ni NVAp)
  ... | TMatchZPre _ _ = abort (¬ni NVMatch)
  ... | TMatchNZPre _ _ _ _ _ = abort (¬ni NVMatch)
  ... | TFst _ = abort (¬ni NVFst)
  ... | TSnd _ = abort (¬ni NVSnd)
  ... | TEHole _ _ = abort (¬ni NVEHole)
  ... | THole _ _ _ = abort (¬ni NVHole)
  ... | TInl _ =
    NotSatisfy (λ ())
               (λ{(CMSNotIntro () _ _)})
               (λ{(CSMSMay (CMSNotIntro () _ _))})
  ... | TInr wt'
    with satisfy-exclusive ct wt' (inr-final fin)
  ... | Satisfy sat ¬msat satm =
    Satisfy (CSInr sat)
            (λ{(CMSInr msat) → ¬msat msat})
            (CSMSSat (CSInr sat))
  ... | MaySatisfy ¬sat msat satm =
    MaySatisfy (λ{(CSInr sat) → ¬sat sat})
               (CMSInr msat)
               (CSMSMay (CMSInr msat))
  ... | NotSatisfy ¬sat ¬msat ¬satm =
    NotSatisfy (λ{(CSInr sat) → ¬sat sat})
               (λ{(CMSInr msat) → ¬msat msat})
               (λ{(CSMSSat (CSInr sat)) → ¬sat sat
                ; (CSMSMay (CMSInr msat)) → ¬msat msat})

  -- pair cases
  satisfy-exclusive {ξ = ξ} {e = e} (CTPair ct1 ct2) wt fin
    with notintro-dec e
  ... | Inl ni with final-notintro-indet fin ni
  ... | ind
    with satisfy-exclusive
           ct1 (TFst wt)
           (FIndet (IFst (λ{e1 e2 refl → contra ni (λ ())}) ind)) |
         satisfy-exclusive
           ct2 (TSnd wt)
           (FIndet (ISnd (λ{e1 e2 refl → contra ni (λ ())}) ind))
  ... | Satisfy sat1 ¬msat1 satm1 | Satisfy sat2 ¬msat2 satm2 =
    Satisfy (CSNotIntroPair ni sat1 sat2)
            (λ{(CMSNotIntro ni ref pos) →
               notintro-sat-ref-not
                 ni (CSNotIntroPair ni sat1 sat2) ref})
            (CSMSSat (CSNotIntroPair ni sat1 sat2))
  ... | Satisfy sat1 ¬msat1 satm1 | MaySatisfy ¬sat2 msat2 satm2 =
    let msat = CMSNotIntro
                 ni
                 (RXPairR (notintro-maysat-ref NVSnd msat2))
                 (PPair (sat-pos sat1) (maysat-pos msat2))
    in MaySatisfy (λ{(CSNotIntroPair ni sat1 sat2) → ¬sat2 sat2})
                  msat
                  (CSMSMay msat)
  ... | MaySatisfy ¬sat1 msat1 satm1 | Satisfy sat2 ¬msat2 satm2 =
    let msat = CMSNotIntro
                 ni
                 (RXPairL (notintro-maysat-ref NVFst msat1))
                 (PPair (maysat-pos msat1) (sat-pos sat2))
    in MaySatisfy (λ{(CSNotIntroPair ni sat1 sat2) → ¬sat1 sat1})
                  msat
                  (CSMSMay msat)
  ... | MaySatisfy ¬sat1 msat1 satm1 |
        MaySatisfy ¬sat2 msat2 satm2 =
    let msat = CMSNotIntro
                 ni
                 (RXPairL (notintro-maysat-ref NVFst msat1))
                 (PPair (maysat-pos msat1) (maysat-pos msat2))
    in MaySatisfy (λ{(CSNotIntroPair ni sat1 sat2) → ¬sat1 sat1})
                  msat
                  (CSMSMay msat)
  ... | Satisfy sat1 ¬msat1 satm1 |
        NotSatisfy ¬sat2 ¬msat2 ¬satm2 =
    NotSatisfy ¬sat ¬msat ¬satm
    where
      ¬sat : (e ⊧̇ ξ) → ⊥
      ¬sat (CSNotIntroPair ni sat1 sat2) = ¬sat2 sat2
      ¬msat : (e ⊧̇? ξ) → ⊥
      ¬msat (CMSNotIntro ni (RXPairL ref1) pos) =
        notintro-sat-ref-not NVFst sat1 ref1
      ¬msat (CMSNotIntro ni (RXPairR ref2) (PPair pos1 pos2)) =
        ¬msat2 (CMSNotIntro NVSnd ref2 pos2)
      ¬satm : (e ⊧̇†? ξ) → ⊥
      ¬satm (CSMSSat sat) = ¬sat sat
      ¬satm (CSMSMay msat) = ¬msat msat  
  ... | NotSatisfy ¬sat1 ¬msat1 ¬satm1 |
        Satisfy sat2 ¬msat2 satm2 =
    NotSatisfy ¬sat ¬msat ¬satm
    where
      ¬sat : (e ⊧̇ ξ) → ⊥
      ¬sat (CSNotIntroPair ni sat1 sat2) = ¬sat1 sat1
      ¬msat : (e ⊧̇? ξ) → ⊥
      ¬msat (CMSNotIntro ni (RXPairL ref1) (PPair pos1 pos2)) =
        ¬msat1 (CMSNotIntro NVFst ref1 pos1)
      ¬msat (CMSNotIntro ni (RXPairR ref2) pos) =
        notintro-sat-ref-not NVSnd sat2 ref2
      ¬satm : (e ⊧̇†? ξ) → ⊥
      ¬satm (CSMSSat sat) = ¬sat sat
      ¬satm (CSMSMay msat) = ¬msat msat   
  satisfy-exclusive {ξ = ⟨ ξ1 , ξ2 ⟩} {e = e}
                    (CTPair ct1 ct2) wt fin | Inl ni | ind
       | MaySatisfy ¬sat1 msat1 satm1 |
         NotSatisfy ¬sat2 ¬msat2 ¬satm2
    with possible-dec ξ2
  ... | Inl pos2 = MaySatisfy ¬sat msat (CSMSMay msat)
    where
      ¬sat : (e ⊧̇ ⟨ ξ1 , ξ2 ⟩) → ⊥
      ¬sat (CSNotIntroPair ni sat1 sat2) = ¬sat2 sat2
      msat : e ⊧̇? ⟨ ξ1 , ξ2 ⟩
      msat =
        CMSNotIntro
          ni
          (RXPairL (notintro-maysat-ref NVFst msat1))
          (PPair (maysat-pos msat1) pos2)
  ... | Inr ¬pos2 = NotSatisfy ¬sat ¬msat ¬satm
    where
      ¬sat : (e ⊧̇ ⟨ ξ1 , ξ2 ⟩) → ⊥
      ¬sat (CSNotIntroPair ni sat1 sat2) = ¬sat2 sat2
      ¬msat : (e ⊧̇? ⟨ ξ1 , ξ2 ⟩) → ⊥
      ¬msat (CMSNotIntro ni ref (PPair pos1 pos2)) = ¬pos2 pos2
      ¬satm : (e ⊧̇†? ⟨ ξ1 , ξ2 ⟩) → ⊥
      ¬satm (CSMSSat sat) = ¬sat sat
      ¬satm (CSMSMay msat) = ¬msat msat
  satisfy-exclusive {ξ = ⟨ ξ1 , ξ2 ⟩} {e = e}
                    (CTPair ct1 ct2) wt fin | Inl ni | ind
       | NotSatisfy ¬sat1 ¬msat1 ¬satm1 |
         MaySatisfy ¬sat2 msat2 satm2
    with possible-dec ξ1
  ... | Inl pos1 = MaySatisfy ¬sat msat (CSMSMay msat)
    where
      ¬sat : (e ⊧̇ ⟨ ξ1 , ξ2 ⟩) → ⊥
      ¬sat (CSNotIntroPair ni sat1 sat2) = ¬sat1 sat1
      msat : e ⊧̇? ⟨ ξ1 , ξ2 ⟩
      msat =
        CMSNotIntro
          ni
          (RXPairR (notintro-maysat-ref NVSnd msat2))
          (PPair pos1 (maysat-pos msat2))
  ... | Inr ¬pos1 = NotSatisfy ¬sat ¬msat ¬satm
    where
      ¬sat : (e ⊧̇ ⟨ ξ1 , ξ2 ⟩) → ⊥
      ¬sat (CSNotIntroPair ni sat1 sat2) = ¬sat1 sat1
      ¬msat : (e ⊧̇? ⟨ ξ1 , ξ2 ⟩) → ⊥
      ¬msat (CMSNotIntro ni ref (PPair pos1 pos2)) = ¬pos1 pos1
      ¬satm : (e ⊧̇†? ⟨ ξ1 , ξ2 ⟩) → ⊥
      ¬satm (CSMSSat sat) = ¬sat sat
      ¬satm (CSMSMay msat) = ¬msat msat
  satisfy-exclusive {ξ = ξ} {e = e}
                    (CTPair ct1 ct2) wt fin | Inl ni | ind
      | NotSatisfy ¬sat1 ¬msat1 ¬satm1 |
        NotSatisfy ¬sat2 ¬msat2 ¬satm2 =
    NotSatisfy ¬sat ¬msat ¬satm
    where
      ¬sat : (e ⊧̇ ξ) → ⊥
      ¬sat (CSNotIntroPair ni sat1 sat2) = ¬sat1 sat1
      ¬msat : (e ⊧̇? ξ) → ⊥
      ¬msat (CMSNotIntro ni (RXPairL ref1) (PPair pos1 pos2)) =
        ¬msat1 (CMSNotIntro NVFst ref1 pos1)
      ¬msat (CMSNotIntro ni (RXPairR ref2) (PPair pos1 pos2)) =
        ¬msat2 (CMSNotIntro NVSnd ref2 pos2)
      ¬satm : (e ⊧̇†? ξ) → ⊥
      ¬satm (CSMSSat sat) = ¬sat sat
      ¬satm (CSMSMay msat) = ¬msat msat
  satisfy-exclusive {ξ = ξ} {e = e}
                    (CTPair ct1 ct2) wt fin | Inr ¬ni
    with wt
  ... | TAp _ _ = abort (¬ni NVAp)
  ... | TMatchZPre _ _ = abort (¬ni NVMatch)
  ... | TMatchNZPre _ _ _ _ _ = abort (¬ni NVMatch)
  ... | TFst _ = abort (¬ni NVFst)
  ... | TSnd _ = abort (¬ni NVSnd)
  ... | TEHole _ _ = abort (¬ni NVEHole)
  ... | THole _ _ _ = abort (¬ni NVHole)
  ... | TPair wt1 wt2
    with pair-final fin
  ... | fin1 , fin2 
    with satisfy-exclusive ct1 wt1 fin1 |
         satisfy-exclusive ct2 wt2 fin2
  ... | Satisfy sat1 ¬msat1 satm1 |
        Satisfy sat2 ¬msat2 satm2 =
    Satisfy (CSPair sat1 sat2)
            (λ{(CMSPairL msat1 sat2) → ¬msat1 msat1
             ; (CMSPairR sat1 msat2) → ¬msat2 msat2
             ; (CMSPair msat1 msat2) → ¬msat2 msat2})
            (CSMSSat (CSPair sat1 sat2))
  ... | Satisfy sat1 ¬msat1 satm1 |
        MaySatisfy ¬sat2 msat2 satm2 =
    MaySatisfy (λ{(CSPair sat1 sat2) → ¬sat2 sat2})
               (CMSPairR sat1 msat2)
               (CSMSMay (CMSPairR sat1 msat2))
  ... | Satisfy sat1 ¬msat1 satm1 |
        NotSatisfy ¬sat2 ¬msat2 ¬satm2 =
    NotSatisfy ¬sat ¬msat ¬satm
    where
      ¬sat : (e ⊧̇ ξ) → ⊥
      ¬sat (CSPair sat1 sat2) = ¬sat2 sat2
      ¬msat : (e ⊧̇? ξ) → ⊥
      ¬msat (CMSPairL msat1 sat2) = ¬msat1 msat1
      ¬msat (CMSPairR sat1 msat2) = ¬msat2 msat2
      ¬msat (CMSPair msat1 msat2) = ¬msat1 msat1
      ¬satm : (e ⊧̇†? ξ) → ⊥
      ¬satm (CSMSSat sat) = ¬sat sat
      ¬satm (CSMSMay msat) = ¬msat msat
  ... | MaySatisfy ¬sat1 msat1 satm1 |
        Satisfy sat2 ¬msat2 satm2 =
    MaySatisfy (λ{(CSPair sat1 sat2) → ¬sat1 sat1})
               (CMSPairL msat1 sat2)
               (CSMSMay (CMSPairL msat1 sat2))
  ... | MaySatisfy ¬sat1 msat1 satm1 |
        MaySatisfy ¬sat2 msat2 satm2 =
    MaySatisfy (λ{(CSPair sat1 sat2) → ¬sat2 sat2})
               (CMSPair msat1 msat2)
               (CSMSMay (CMSPair msat1 msat2))
  ... | MaySatisfy ¬sat1 msat1 satm1 |
        NotSatisfy ¬sat2 ¬msat2 ¬satm2 =
    NotSatisfy ¬sat ¬msat ¬satm
    where
      ¬sat : (e ⊧̇ ξ) → ⊥
      ¬sat (CSPair sat1 sat2) = ¬sat2 sat2
      ¬msat : (e ⊧̇? ξ) → ⊥
      ¬msat (CMSPairL msat1 sat2) = ¬sat2 sat2
      ¬msat (CMSPairR sat1 msat2) = ¬msat2 msat2
      ¬msat (CMSPair msat1 msat2) = ¬msat2 msat2
      ¬satm : (e ⊧̇†? ξ) → ⊥
      ¬satm (CSMSSat sat) = ¬sat sat
      ¬satm (CSMSMay msat) = ¬msat msat  
  ... | NotSatisfy ¬sat1 ¬msat1 ¬satm1 |
        Satisfy sat2 ¬msat2 satm2 =
    NotSatisfy ¬sat ¬msat ¬satm
    where
      ¬sat : (e ⊧̇ ξ) → ⊥
      ¬sat (CSPair sat1 sat2) = ¬sat1 sat1
      ¬msat : (e ⊧̇? ξ) → ⊥
      ¬msat (CMSPairL msat1 sat2) = ¬msat1 msat1
      ¬msat (CMSPairR sat1 msat2) = ¬msat2 msat2
      ¬msat (CMSPair msat1 msat2) = ¬msat1 msat1
      ¬satm : (e ⊧̇†? ξ) → ⊥
      ¬satm (CSMSSat sat) = ¬sat sat
      ¬satm (CSMSMay msat) = ¬msat msat
  ... | NotSatisfy ¬sat1 ¬msat1 ¬satm1 |
        MaySatisfy ¬sat2 msat2 satm2 =
    NotSatisfy ¬sat ¬msat ¬satm
    where
      ¬sat : (e ⊧̇ ξ) → ⊥
      ¬sat (CSPair sat1 sat2) = ¬sat2 sat2
      ¬msat : (e ⊧̇? ξ) → ⊥
      ¬msat (CMSPairL msat1 sat2) = ¬sat2 sat2
      ¬msat (CMSPairR sat1 msat2) = ¬sat1 sat1
      ¬msat (CMSPair msat1 msat2) = ¬msat1 msat1
      ¬satm : (e ⊧̇†? ξ) → ⊥
      ¬satm (CSMSSat sat) = ¬sat sat
      ¬satm (CSMSMay msat) = ¬msat msat
  ... | NotSatisfy ¬sat1 ¬msat1 ¬satm1 |
        NotSatisfy ¬sat2 ¬msat2 ¬samt2 =
    NotSatisfy ¬sat ¬msat ¬satm
    where
      ¬sat : (e ⊧̇ ξ) → ⊥
      ¬sat (CSPair sat1 sat2) = ¬sat2 sat2
      ¬msat : (e ⊧̇? ξ) → ⊥
      ¬msat (CMSPairL msat1 sat2) = ¬msat1 msat1
      ¬msat (CMSPairR sat1 msat2) = ¬msat2 msat2
      ¬msat (CMSPair msat1 msat2) = ¬msat2 msat2
      ¬satm : (e ⊧̇†? ξ) → ⊥
      ¬satm (CSMSSat sat) = ¬sat sat
      ¬satm (CSMSMay msat) = ¬msat msat
  
  -- or cases
  satisfy-exclusive (CTOr ct1 ct2) wt fin
    with satisfy-exclusive ct1 wt fin |
         satisfy-exclusive ct2 wt fin
  ... | Satisfy sat1 ¬msat1 satm1 |
        Satisfy sat2 ¬msat2 satm2 =
    Satisfy (CSOrR sat2)
            (λ{(CMSOrL _ ¬sat2) → ¬sat2 sat2
             ; (CMSOrR ¬sat1 _) → ¬sat1 sat1
             ; (CMSNotIntro ni (RXOr ref1 ref2) _) →
               notintro-sat-ref-not ni sat1 ref1})
             (CSMSSat (CSOrL sat1))
  ... | Satisfy sat1 ¬msat1 satm1 |
        MaySatisfy ¬sat2 msat2 satm2 =
    Satisfy (CSOrL sat1)
            (λ{(CMSOrL msat1 _) → ¬msat1 msat1
             ; (CMSOrR ¬sat1 _) → ¬sat1 sat1
             ; (CMSNotIntro ni (RXOr ref1 ref2) _) →
               notintro-sat-ref-not ni sat1 ref1})
            (CSMSSat (CSOrL sat1))
  ... | Satisfy sat1 ¬msat1 satm1 |
        NotSatisfy ¬sat2 ¬msat2 ¬satm2 =
    Satisfy (CSOrL sat1)
            (λ{(CMSOrL msat1 _) → ¬msat1 msat1
             ; (CMSOrR ¬sat1 _) → ¬sat1 sat1
             ; (CMSNotIntro ni (RXOr ref1 ref2) _) →
               notintro-sat-ref-not ni sat1 ref1})
            (CSMSSat (CSOrL sat1))
  ... | MaySatisfy ¬sat1 msat1 satm1 |
        Satisfy sat2 ¬msat2 satm2 =
    Satisfy (CSOrR sat2)
            (λ{(CMSOrL _ ¬sat2) → ¬sat2 sat2
             ; (CMSOrR _ msat2) → ¬msat2 msat2
             ; (CMSNotIntro ni (RXOr ref1 ref2) _) →
               notintro-sat-ref-not ni sat2 ref2})
            (CSMSSat (CSOrR sat2))
  ... | MaySatisfy ¬sat1 msat1 satm1 |
        MaySatisfy ¬sat2 msat2 satm2 =
    MaySatisfy (λ{(CSOrL sat1) → ¬sat1 sat1
                ; (CSOrR sat2) → ¬sat2 sat2})
               (CMSOrL msat1 ¬sat2)
               (CSMSMay (CMSOrL msat1 ¬sat2))
  ... | MaySatisfy ¬sat1 msat1 satm1 |
        NotSatisfy ¬sat2 ¬msat2 ¬satm1 =
    MaySatisfy (λ{(CSOrL sat1) → ¬sat1 sat1
                ; (CSOrR sat2) → ¬sat2 sat2})
               (CMSOrL msat1 ¬sat2)
               (CSMSMay (CMSOrL msat1 ¬sat2))
  ... | NotSatisfy ¬sat1 ¬msat1 ¬satm1 |
        Satisfy sat2 ¬msat2 satm2 =
    Satisfy (CSOrR sat2)
            (λ{(CMSOrL _ ¬sat2) → ¬sat2 sat2
             ; (CMSOrR _ msat2) → ¬msat2 msat2
             ; (CMSNotIntro ni (RXOr ref1 ref2) _) →
               notintro-sat-ref-not ni sat2 ref2})
            (CSMSSat (CSOrR sat2))
  ... | NotSatisfy ¬sat1 ¬msat1 ¬satm1 |
        MaySatisfy ¬sat2 msat2 satm2 =
    MaySatisfy (λ{(CSOrL sat1) → ¬sat1 sat1
                ; (CSOrR sat2) → ¬sat2 sat2})
               (CMSOrR ¬sat1 msat2)
               (CSMSMay (CMSOrR ¬sat1 msat2))
  ... | NotSatisfy ¬sat1 ¬msat1 ¬satm1 |
        NotSatisfy ¬sat2 ¬msat2 ¬satm2 =
    NotSatisfy (λ{(CSOrL sat1) → ¬sat1 sat1
                ; (CSOrR sat2) → ¬sat2 sat2})
               (λ{(CMSOrL msat1 ¬sat2) → ¬msat1 msat1
                ; (CMSOrR ¬sat1 msat2) → ¬msat2 msat2
                ; (CMSNotIntro ni (RXOr ref1 ref2) (POrL pos1)) →
                  ¬satm1 (CSMSMay (CMSNotIntro ni ref1 pos1))
                ; (CMSNotIntro ni (RXOr ref1 ref2) (POrR pos2)) →
                  ¬satm2 (CSMSMay (CMSNotIntro ni ref2 pos2))})
               (λ{(CSMSSat (CSOrL sat1)) → ¬sat1 sat1
                ; (CSMSSat (CSOrR sat2)) → ¬sat2 sat2
                ; (CSMSMay (CMSOrL msat1 _)) → ¬msat1 msat1
                ; (CSMSMay (CMSOrR _ msat2)) → ¬msat2 msat2
                ; (CSMSMay (CMSNotIntro ni (RXOr ref1 ref2)
                                        (POrL pos1))) →
                  ¬satm1 (CSMSMay (CMSNotIntro ni ref1 pos1))
                ; (CSMSMay (CMSNotIntro ni (RXOr ref1 ref2)
                                        (POrR pos2))) →
                  ¬satm2 (CSMSMay (CMSNotIntro ni ref2 pos2))})

