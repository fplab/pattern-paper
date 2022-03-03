open import Prelude
open import contexts
open import core
open import complete-constraints-core
open import constraints-core
open import dynamics-core
open import lemmas-satisfy
open import lemmas-values
open import result-judgements
open import satisfy-decidable
open import statics-core
open import value-judgements

-- theorems showing that one can determine
-- entailment and potential entailment of the
-- incomplete constraints emitted by patterns by
-- passing to truify or falsify complete versions
-- of said constraints
module complete-relationship where
  -- substituting ? for ⊤ in ξ does not
  -- change its type
  truify-same-type : ∀{ξ τ} →
                       ξ :c: τ →
                       (ξ ◆⊤) :cc: τ
  truify-same-type CTTruth = CTTruth
  truify-same-type CTFalsity = CTFalsity
  truify-same-type CTUnknown = CTTruth
  truify-same-type CTNum = CTNum
  truify-same-type (CTInl ct) = CTInl (truify-same-type ct)
  truify-same-type (CTInr ct) = CTInr (truify-same-type ct)
  truify-same-type (CTPair ct1 ct2) =
    CTPair (truify-same-type ct1) (truify-same-type ct2)
  truify-same-type (CTOr ct1 ct2) =
    CTOr (truify-same-type ct1) (truify-same-type ct2)

  same-type-truify : ∀{ξ τ} →
                       (ξ ◆⊤) :cc: τ →
                       ξ :c: τ
  same-type-truify {ξ = ·⊤} CTTruth = CTTruth
  same-type-truify {ξ = ·⊥} CTFalsity = CTFalsity
  same-type-truify {ξ = ·?} CTTruth = CTUnknown
  same-type-truify {ξ = N n} CTNum = CTNum
  same-type-truify {ξ = inl ξ} (CTInl ctc) = CTInl (same-type-truify ctc)
  same-type-truify {ξ = inr ξ} (CTInr ctc) = CTInr (same-type-truify ctc)
  same-type-truify {ξ = ⟨ ξ1 , ξ2 ⟩} (CTPair ctc1 ctc2) =
    CTPair (same-type-truify ctc1) (same-type-truify ctc2)
  same-type-truify {ξ = ξ1 ∨ ξ2} (CTOr ctc1 ctc2) =
    CTOr (same-type-truify ctc1) (same-type-truify ctc2)

  -- substituting ? for ⊥ in ξ does not
  -- change its type
  falsify-same-type : ∀{ξ τ} →
                      ξ :c: τ →
                      (ξ ◆⊥) :cc: τ
  falsify-same-type CTTruth = CTTruth
  falsify-same-type CTFalsity = CTFalsity
  falsify-same-type CTUnknown = CTFalsity
  falsify-same-type CTNum = CTNum
  falsify-same-type (CTInl ct) = CTInl (falsify-same-type ct)
  falsify-same-type (CTInr ct) = CTInr (falsify-same-type ct)
  falsify-same-type (CTPair ct1 ct2) =
    CTPair (falsify-same-type ct1) (falsify-same-type ct2)
  falsify-same-type (CTOr ct1 ct2) =
    CTOr (falsify-same-type ct1) (falsify-same-type ct2)
  
  same-type-falsify : ∀{ξ τ} →
                      (ξ ◆⊥) :cc: τ →
                      ξ :c: τ
  same-type-falsify {ξ = ·⊤} CTTruth = CTTruth
  same-type-falsify {ξ = ·⊥} CTFalsity = CTFalsity
  same-type-falsify {ξ = ·?} CTFalsity = CTUnknown
  same-type-falsify {ξ = N n} CTNum = CTNum
  same-type-falsify {ξ = inl ξ} (CTInl ctc) = CTInl (same-type-falsify ctc)
  same-type-falsify {ξ = inr ξ} (CTInr ctc) = CTInr (same-type-falsify ctc)
  same-type-falsify {ξ = ⟨ ξ1 , ξ2 ⟩} (CTPair ctc1 ctc2) =
    CTPair (same-type-falsify ctc1) (same-type-falsify ctc2)
  same-type-falsify {ξ = ξ1 ∨ ξ2} (CTOr ctc1 ctc2) =
    CTOr (same-type-falsify ctc1) (same-type-falsify ctc2)

  -- possibly satisfying a constraint is the same as satisfying its
  -- truthified version
  val-satormay-sat-truify : ∀{e ξ} →
                              e val →
                              e ⊧̇†? ξ →
                              e ⊧ (ξ ◆⊤)
  val-satormay-sat-truify eval (CSMSSat CSTruth) = CSTruth
  val-satormay-sat-truify eval (CSMSSat CSNum) = CSNum
  val-satormay-sat-truify (VInl eval) (CSMSSat (CSInl sat)) =
    CSInl (val-satormay-sat-truify eval (CSMSSat sat))
  val-satormay-sat-truify (VInr eval) (CSMSSat (CSInr sat)) =
    CSInr (val-satormay-sat-truify eval (CSMSSat sat))
  val-satormay-sat-truify (VPair eval1 eval2) (CSMSSat (CSPair sat1 sat2)) =
    CSPair (val-satormay-sat-truify eval1 (CSMSSat sat1))
           (val-satormay-sat-truify eval2 (CSMSSat sat2))
  val-satormay-sat-truify eval (CSMSSat (CSNotIntroPair ni sat1 sat2)) =
    abort (val-notintro-not eval ni)
  val-satormay-sat-truify eval (CSMSSat (CSOrL sat1)) =
    CSOrL (val-satormay-sat-truify eval (CSMSSat sat1))
  val-satormay-sat-truify eval (CSMSSat (CSOrR sat2)) =
    CSOrR (val-satormay-sat-truify eval (CSMSSat sat2))
  val-satormay-sat-truify eval (CSMSMay CMSUnknown) = CSTruth
  val-satormay-sat-truify (VInl eval) (CSMSMay (CMSInl msat)) =
    CSInl (val-satormay-sat-truify eval (CSMSMay msat))
  val-satormay-sat-truify (VInr eval) (CSMSMay (CMSInr msat)) =
    CSInr (val-satormay-sat-truify eval (CSMSMay msat))
  val-satormay-sat-truify (VPair eval1 eval2) (CSMSMay (CMSPairL msat1 sat2)) =
    CSPair (val-satormay-sat-truify eval1 (CSMSMay msat1))
           (val-satormay-sat-truify eval2 (CSMSSat sat2))
  val-satormay-sat-truify (VPair eval1 eval2) (CSMSMay (CMSPairR sat1 msat2)) =
    CSPair (val-satormay-sat-truify eval1 (CSMSSat sat1))
           (val-satormay-sat-truify eval2 (CSMSMay msat2))
  val-satormay-sat-truify (VPair eval1 eval2) (CSMSMay (CMSPair msat1 msat2)) =
    CSPair (val-satormay-sat-truify eval1 (CSMSMay msat1))
           (val-satormay-sat-truify eval2 (CSMSMay msat2))
  val-satormay-sat-truify eval (CSMSMay (CMSOrL msat1 ¬sat2)) =
    CSOrL (val-satormay-sat-truify eval (CSMSMay msat1))
  val-satormay-sat-truify eval (CSMSMay (CMSOrR ¬sat1 msat2)) =
    CSOrR (val-satormay-sat-truify eval (CSMSMay msat2))
  val-satormay-sat-truify eval (CSMSMay (CMSNotIntro ni ref pos)) =
    abort (val-notintro-not eval ni)

  -- converse of the above
  sat-truify-satormay : ∀{e ξ} →
                          e ⊧ (ξ ◆⊤) →
                          e ⊧̇†? ξ
  sat-truify-satormay {ξ = ·⊤} sat = CSMSSat CSTruth
  sat-truify-satormay {ξ = ·?} sat = CSMSMay CMSUnknown
  sat-truify-satormay {ξ = N n} CSNum = CSMSSat CSNum
  sat-truify-satormay {ξ = inl ξ} (CSInl sat) =
    satormay-inl (sat-truify-satormay sat)
  sat-truify-satormay {ξ = inr ξ} (CSInr sat) =
    satormay-inr (sat-truify-satormay sat)
  sat-truify-satormay {ξ = ⟨ ξ1 , ξ2 ⟩} (CSPair sat1 sat2) =
    satormay-pair (sat-truify-satormay sat1) (sat-truify-satormay sat2)
  sat-truify-satormay {ξ = ξ1 ∨ ξ2} (CSOrL sat1) =
    satormay-or-l (sat-truify-satormay sat1)
  sat-truify-satormay {ξ = ξ1 ∨ ξ2} (CSOrR sat2) =
    satormay-or-r (sat-truify-satormay sat2)

  -- satisfying a constraint is the same as satifying its
  -- falsified version
  val-sat-sat-falsify : ∀{e ξ} →
                        e val →
                        e ⊧̇ ξ →
                        e ⊧ (ξ ◆⊥)
  val-sat-sat-falsify eval CSTruth = CSTruth
  val-sat-sat-falsify eval CSNum = CSNum
  val-sat-sat-falsify (VInl eval) (CSInl sat) =
    CSInl (val-sat-sat-falsify eval sat)
  val-sat-sat-falsify (VInr eval) (CSInr sat) =
    CSInr (val-sat-sat-falsify eval sat)
  val-sat-sat-falsify (VPair eval1 eval2) (CSPair sat1 sat2) =
    CSPair (val-sat-sat-falsify eval1 sat1) (val-sat-sat-falsify eval2 sat2)
  val-sat-sat-falsify eval (CSNotIntroPair ni sat1 sat2) =
    abort (val-notintro-not eval ni)
  val-sat-sat-falsify eval (CSOrL sat1) = CSOrL (val-sat-sat-falsify eval sat1)
  val-sat-sat-falsify eval (CSOrR sat2) = CSOrR (val-sat-sat-falsify eval sat2)

  -- converse of the above
  sat-falsify-sat : ∀{e ξ} →
                    e ⊧ (ξ ◆⊥) →
                    e ⊧̇ ξ
  sat-falsify-sat {ξ = ·⊤} sat = CSTruth
  sat-falsify-sat {ξ = N n} CSNum = CSNum
  sat-falsify-sat {ξ = inl ξ} (CSInl sat) = CSInl (sat-falsify-sat sat)
  sat-falsify-sat {ξ = inr ξ} (CSInr sat) = CSInr (sat-falsify-sat sat)
  sat-falsify-sat {ξ = ⟨ ξ1 , ξ2 ⟩} (CSPair sat1 sat2) =
    CSPair (sat-falsify-sat sat1) (sat-falsify-sat sat2)
  sat-falsify-sat {ξ = ξ1 ∨ ξ2} (CSOrL sat1) = CSOrL (sat-falsify-sat sat1)
  sat-falsify-sat {ξ = ξ1 ∨ ξ2} (CSOrR sat2) = CSOrR (sat-falsify-sat sat2)

  -- if anything final satisfies or may satsfy a  a constraint,
  -- then so does anything val
  -- this is trivial since everything which is val is also final
  final-val-satorymay : ∀{ξ τ} →
                        ξ :c: τ →
                        (∀{Δ Δp e} →
                         ∅ , Δ , Δp ⊢ e :: τ →
                         e final →
                         e ⊧̇†? ξ) →
                        (∀{Δ Δp e} →
                        ∅ , Δ , Δp ⊢ e :: τ →
                        e val →
                        e ⊧̇†? ξ)
  final-val-satorymay ct finsat wt eval = finsat wt (FVal eval)                    

  -- converse of the above. if all values satisfy or may satisfy a
  -- constraint, then in fact so does anything final. essentially,
  -- possible exhaustiveness on values implies possible exhaustiveness
  -- in general
  val-final-satormay : ∀{ξ τ} →
                       ξ :c: τ →
                       (∀{Δ Δp e} →
                        ∅ , Δ , Δp ⊢ e :: τ →
                        e val →
                        e ⊧̇†? ξ) →
                       (∀{Δ Δp e} →
                        ∅ , Δ , Δp ⊢ e :: τ →
                        e final →
                        e ⊧̇†? ξ)
  val-final-satormay {ξ = ξ} ct valsat {e = e} wt (FVal eval) = valsat wt eval
  val-final-satormay {ξ = ξ} ct valsat {e = e} wt (FIndet ind)
    with satisfyormay-dec e ξ
  ... | Inl satm = satm
  ... | Inr ¬satm
    with indet-has-values ind wt
  ... | e' , vals' = abort (¬msat' (valsat (values-same-type vals' wt)
                           (values-val vals')))
    where
      ¬msat' : e' ⊧̇†? ξ → ⊥
      ¬msat' satm' =
        indet-values-not-satormay ind vals' wt ct ¬satm satm'

  -- a constraint is possibly exhaustive only if its
  -- truthified version is exhaustve
  truth-potent-ent-truify : ∀{ξ τ} →
                             ·⊤ ·: τ c⊧̇†? ξ →
                             ·⊤ ·: τ cc⊧ (ξ ◆⊤)
  truth-potent-ent-truify (PotEntails trct ct pent) =
    Entails CTTruth (truify-same-type ct)
            λ wt eval _ →
              val-satormay-sat-truify eval (pent wt (FVal eval) (CSMSSat CSTruth))

  -- if the truthified version of a constraint is exhaustive,
  -- then the constraint is possibly exhaustive
  truth-ent-truify-potent : ∀{ξ τ} →
                             ·⊤ ·: τ cc⊧ (ξ ◆⊤) →
                             ·⊤ ·: τ c⊧̇†? ξ
  truth-ent-truify-potent {ξ = ξ} (Entails {τ = τ} trct tct ent) =
    PotEntails CTTruth (same-type-truify tct)
               λ wt fin _ → all-fin-satm wt fin
    where
      all-fin-satm : ∀{Δ Δp e} →
                     ∅ , Δ , Δp ⊢ e :: τ →
                     e final →
                     e ⊧̇†? ξ
      all-fin-satm =
        val-final-satormay (same-type-truify tct)
                           (λ wt' eval' →
                              sat-truify-satormay (ent wt' eval' CSTruth))

  -- an incomplete constraint entails another constraint
  -- only if the truthified version entails the falisfied version
  ent-truify-ent-falsify : ∀{ξ1 ξ2 τ} →
                             ξ1 ·: τ c⊧̇ ξ2 →
                             (ξ1 ◆⊤) ·: τ cc⊧ (ξ2 ◆⊥)
  ent-truify-ent-falsify (Entails ct1 ct2 ent) =
    Entails (truify-same-type ct1) (falsify-same-type ct2)
            λ wt eval satt →
              val-sat-sat-falsify eval
                                  (ent wt eval (sat-truify-satormay satt))

  -- converse of the above
  truify-ent-falsify-ent : ∀{ξ1 ξ2 τ} →
                             (ξ1 ◆⊤) ·: τ cc⊧ (ξ2 ◆⊥) →
                             ξ1 ·: τ c⊧̇ ξ2
  truify-ent-falsify-ent (Entails tct1 fct2 ent) =
    Entails (same-type-truify tct1) (same-type-falsify fct2)
            λ wt eval satm →
              sat-falsify-sat (ent wt eval
                                   (val-satormay-sat-truify eval satm))
