open import Nat
open import Prelude
open import constraints-core
open import core
open import dynamics-core
open import lemmas-satisfy
open import lemmas-subst-value
open import result-judgements
open import satisfy-decidable
open import statics-core

-- a given satisfaction judgement still holds
-- after substituting a variable in the expression
module lemmas-subst-satisfy where
  subst-sat : ∀{x e1 e2 ξ} →
              e1 ⊧̇ ξ →
              ([ e2 / x ] e1) ⊧̇ ξ
  subst-sat CSTruth = CSTruth
  subst-sat CSNum = CSNum
  subst-sat (CSInl sat) = CSInl (subst-sat sat)
  subst-sat (CSInr sat) = CSInr (subst-sat sat)
  subst-sat (CSPair sat1 sat2) =
    CSPair (subst-sat sat1) (subst-sat sat2)
  subst-sat (CSNotIntroPair ni sat1 sat2) =
    CSNotIntroPair (subst-notintro ni)
                   (subst-sat sat1) (subst-sat sat2)
  subst-sat (CSOrL sat) = CSOrL (subst-sat sat)
  subst-sat (CSOrR sat) = CSOrR (subst-sat sat)
  
  final-sat-subst : ∀{x e1 e2 ξ} →
                    e1 final →
                    ([ e2 / x ] e1) ⊧̇ ξ →
                    e1 ⊧̇ ξ
  final-sat-subst (FVal VUnit) sat = sat
  final-sat-subst (FVal VNum) sat = sat
  final-sat-subst {x = x} (FVal (VLam {x = y})) sat
    with nat-dec y x
  ... | Inl refl = sat
  ... | Inr y≠x = lam-sat-all-sat sat
  final-sat-subst (FVal (VInl eval)) CSTruth = CSTruth
  final-sat-subst (FVal (VInl eval)) (CSInl sat) =
    CSInl (final-sat-subst (FVal eval) sat)
  final-sat-subst (FVal (VInl eval)) (CSOrL sat) =
    CSOrL (final-sat-subst (FVal (VInl eval)) sat)
  final-sat-subst (FVal (VInl eval)) (CSOrR sat) =
    CSOrR (final-sat-subst (FVal (VInl eval)) sat)
  final-sat-subst (FVal (VInr eval)) CSTruth = CSTruth
  final-sat-subst (FVal (VInr eval)) (CSInr sat) =
    CSInr (final-sat-subst (FVal eval) sat)
  final-sat-subst (FVal (VInr eval)) (CSOrL sat) =
    CSOrL (final-sat-subst (FVal (VInr eval)) sat)
  final-sat-subst (FVal (VInr eval)) (CSOrR sat) =
    CSOrR (final-sat-subst (FVal (VInr eval)) sat)
  final-sat-subst (FVal (VPair eval1 eval2)) CSTruth = CSTruth
  final-sat-subst (FVal (VPair eval1 eval2)) (CSPair sat1 sat2) =
    CSPair (final-sat-subst (FVal eval1) sat1)
           (final-sat-subst (FVal eval2) sat2)
  final-sat-subst (FVal (VPair eval1 eval2)) (CSOrL sat) =
    CSOrL (final-sat-subst (FVal (VPair eval1 eval2)) sat)
  final-sat-subst (FVal (VPair eval1 eval2)) (CSOrR sat) =
    CSOrR (final-sat-subst (FVal (VPair eval1 eval2)) sat)
  final-sat-subst (FIndet (IAp ind1 fin2)) sat =
    all-notintro-sat NVAp sat NVAp
  final-sat-subst (FIndet (IInl ind)) CSTruth = CSTruth
  final-sat-subst (FIndet (IInl ind)) (CSInl sat) =
    CSInl (final-sat-subst (FIndet ind) sat)
  final-sat-subst (FIndet (IInl ind)) (CSOrL sat) =
    CSOrL (final-sat-subst (FIndet (IInl ind)) sat)
  final-sat-subst (FIndet (IInl ind)) (CSOrR sat) =
    CSOrR (final-sat-subst (FIndet (IInl ind)) sat)
  final-sat-subst (FIndet (IInr ind)) CSTruth = CSTruth
  final-sat-subst (FIndet (IInr ind)) (CSInr sat) =
    CSInr (final-sat-subst (FIndet ind) sat)
  final-sat-subst (FIndet (IInr ind)) (CSOrL sat) =
    CSOrL (final-sat-subst (FIndet (IInr ind)) sat)
  final-sat-subst (FIndet (IInr ind)) (CSOrR sat) =
    CSOrR (final-sat-subst (FIndet (IInr ind)) sat)
  final-sat-subst (FIndet (IMatch fin mmatch)) sat =
    all-notintro-sat NVMatch sat NVMatch
  final-sat-subst (FIndet (IPairL ind1 val2)) CSTruth = CSTruth
  final-sat-subst (FIndet (IPairL ind1 val2)) (CSPair sat1 sat2) =
    CSPair (final-sat-subst (FIndet ind1) sat1)
           (final-sat-subst (FVal val2) sat2)
  final-sat-subst (FIndet (IPairL ind1 val2)) (CSOrL sat) =
    CSOrL (final-sat-subst (FIndet (IPairL ind1 val2)) sat)
  final-sat-subst (FIndet (IPairL ind1 val2)) (CSOrR sat) =
    CSOrR (final-sat-subst (FIndet (IPairL ind1 val2)) sat)
  final-sat-subst (FIndet (IPairR val1 ind2)) CSTruth = CSTruth
  final-sat-subst (FIndet (IPairR val1 ind2)) (CSPair sat1 sat2) =
    CSPair (final-sat-subst (FVal val1) sat1)
           (final-sat-subst (FIndet ind2) sat2)
  final-sat-subst (FIndet (IPairR val1 ind2)) (CSOrL sat) =
    CSOrL (final-sat-subst (FIndet (IPairR val1 ind2)) sat)
  final-sat-subst (FIndet (IPairR val1 ind2)) (CSOrR sat) =
    CSOrR (final-sat-subst (FIndet (IPairR val1 ind2)) sat)
  final-sat-subst (FIndet (IPair ind1 ind2)) CSTruth = CSTruth
  final-sat-subst (FIndet (IPair ind1 ind2)) (CSPair sat1 sat2) =
    CSPair (final-sat-subst (FIndet ind1) sat1)
           (final-sat-subst (FIndet ind2) sat2)
  final-sat-subst (FIndet (IPair ind1 ind2)) (CSOrL sat) =
    CSOrL (final-sat-subst (FIndet (IPair ind1 ind2)) sat)
  final-sat-subst (FIndet (IPair ind1 ind2)) (CSOrR sat) =
    CSOrR (final-sat-subst (FIndet (IPair ind1 ind2)) sat)
  final-sat-subst (FIndet (IFst npr ind)) sat =
    all-notintro-sat NVFst sat NVFst
  final-sat-subst (FIndet (ISnd npr ind)) sat =
    all-notintro-sat NVSnd sat NVSnd
  final-sat-subst (FIndet IEHole) sat =
    all-notintro-sat NVEHole sat NVEHole
  final-sat-subst (FIndet (IHole ind)) sat =
    all-notintro-sat NVHole sat NVHole
              
  final-subst-maysat : ∀{x e1 e2 ξ} →
                       e1 final →
                       e1 ⊧̇? ξ →
                       ([ e2 / x ] e1) ⊧̇? ξ
  final-subst-maysat fin CMSUnknown = CMSUnknown
  final-subst-maysat fin (CMSInl msat) =
    CMSInl (final-subst-maysat (inl-final fin) msat)
  final-subst-maysat fin (CMSInr msat) =
    CMSInr (final-subst-maysat (inr-final fin) msat)
  final-subst-maysat fin (CMSPairL msat1 sat2) =
    CMSPairL (final-subst-maysat (π1 (pair-final fin)) msat1)
             (subst-sat sat2)
  final-subst-maysat fin (CMSPairR sat1 msat2) =
    CMSPairR (subst-sat sat1)
             (final-subst-maysat (π2 (pair-final fin)) msat2)
  final-subst-maysat fin (CMSPair msat1 msat2) =
    CMSPair (final-subst-maysat (π1 (pair-final fin)) msat1)
            (final-subst-maysat (π2 (pair-final fin)) msat2)
  final-subst-maysat fin (CMSOrL msat1 ¬sat2) =
    CMSOrL (final-subst-maysat fin msat1)
           (λ{ssat2 → ¬sat2 (final-sat-subst fin ssat2)})
  final-subst-maysat fin (CMSOrR ¬sat1 msat2) =
    CMSOrR (λ{ssat1 → ¬sat1 (final-sat-subst fin ssat1)})
           (final-subst-maysat fin msat2)
  final-subst-maysat fin (CMSNotIntro ni ref pos) =
    CMSNotIntro (subst-notintro ni) ref pos

  final-maysat-subst : ∀{x e1 e2 ξ} →
                       e1 final →
                       ([ e2 / x ] e1) ⊧̇? ξ →
                       e1 ⊧̇? ξ
  final-maysat-subst (FVal VUnit) msat = msat
  final-maysat-subst (FVal VNum) msat = msat
  final-maysat-subst {x = x} (FVal (VLam {x = y})) msat
    with nat-dec y x
  ... | Inl refl = all-lam-maysat msat
  ... | Inr y≠x = all-lam-maysat msat
  final-maysat-subst (FVal (VInl eval)) CMSUnknown = CMSUnknown
  final-maysat-subst (FVal (VInl eval)) (CMSInl msat) =
    CMSInl (final-maysat-subst (FVal eval) msat)
  final-maysat-subst (FVal (VInl eval)) (CMSOrL msat1 ¬sat2) =
    CMSOrL (final-maysat-subst (FVal (VInl eval)) msat1)
           (λ{sat2 → ¬sat2 (subst-sat sat2)})
  final-maysat-subst (FVal (VInl eval)) (CMSOrR ¬sat1 msat2) =
    CMSOrR (λ{sat1 → ¬sat1 (subst-sat sat1)})
           (final-maysat-subst (FVal (VInl eval)) msat2)
  final-maysat-subst (FVal (VInr eval)) CMSUnknown = CMSUnknown
  final-maysat-subst (FVal (VInr eval)) (CMSInr msat) =
    CMSInr (final-maysat-subst (FVal eval) msat)
  final-maysat-subst (FVal (VInr eval)) (CMSOrL msat1 ¬sat2) =
    CMSOrL (final-maysat-subst (FVal (VInr eval)) msat1)
           (λ{sat2 → ¬sat2 (subst-sat sat2)})
  final-maysat-subst (FVal (VInr eval)) (CMSOrR ¬sat1 msat2) =
    CMSOrR (λ{sat1 → ¬sat1 (subst-sat sat1)})
           (final-maysat-subst (FVal (VInr eval)) msat2)
  final-maysat-subst (FVal (VPair eval1 eval2)) CMSUnknown =
    CMSUnknown
  final-maysat-subst (FVal (VPair eval1 eval2))
                     (CMSPairL msat1 sat2) =
    CMSPairL (final-maysat-subst (FVal eval1) msat1)
             (final-sat-subst (FVal eval2) sat2)
  final-maysat-subst (FVal (VPair eval1 eval2))
                     (CMSPairR sat1 msat2) =
    CMSPairR (final-sat-subst (FVal eval1) sat1)
             (final-maysat-subst (FVal eval2) msat2)
  final-maysat-subst (FVal (VPair eval1 eval2))
                     (CMSPair msat1 msat2) =
    CMSPair (final-maysat-subst (FVal eval1) msat1)
            (final-maysat-subst (FVal eval2) msat2)
  final-maysat-subst (FVal (VPair eval1 eval2))
                     (CMSOrL msat1 ¬sat2) =
    CMSOrL (final-maysat-subst (FVal (VPair eval1 eval2)) msat1)
           (λ{sat2 → ¬sat2 (subst-sat sat2)})
  final-maysat-subst (FVal (VPair eval1 eval2))
                     (CMSOrR ¬sat1 msat2) =
    CMSOrR (λ{sat1 → ¬sat1 (subst-sat sat1)})
           (final-maysat-subst (FVal (VPair eval1 eval2)) msat2)
  final-maysat-subst (FIndet (IAp ind1 fin2)) msat =
    all-notintro-maysat NVAp msat NVAp
  final-maysat-subst (FIndet (IInl ind)) CMSUnknown = CMSUnknown
  final-maysat-subst (FIndet (IInl ind)) (CMSInl msat) =
    CMSInl (final-maysat-subst (FIndet ind) msat)
  final-maysat-subst (FIndet (IInl ind)) (CMSOrL msat1 ¬sat2) =
    CMSOrL (final-maysat-subst (FIndet (IInl ind)) msat1)
           (λ{sat2 → ¬sat2 (subst-sat sat2)})
  final-maysat-subst (FIndet (IInl ind)) (CMSOrR ¬sat1 msat2) =
    CMSOrR (λ{sat1 → ¬sat1 (subst-sat sat1)})
           (final-maysat-subst (FIndet (IInl ind)) msat2)
  final-maysat-subst (FIndet (IInr ind)) CMSUnknown = CMSUnknown
  final-maysat-subst (FIndet (IInr ind)) (CMSInr sat) =
    CMSInr (final-maysat-subst (FIndet ind) sat)
  final-maysat-subst (FIndet (IInr ind)) (CMSOrL msat1 ¬sat2) =
    CMSOrL (final-maysat-subst (FIndet (IInr ind)) msat1)
           (λ{sat2 → ¬sat2 (subst-sat sat2)})
  final-maysat-subst (FIndet (IInr ind)) (CMSOrR ¬sat1 msat2) =
    CMSOrR (λ{sat1 → ¬sat1 (subst-sat sat1)})
           (final-maysat-subst (FIndet (IInr ind)) msat2)
  final-maysat-subst (FIndet (IMatch fin mmatch)) msat =
    all-notintro-maysat NVMatch msat NVMatch
  final-maysat-subst (FIndet (IPairL ind1 val2))
                     CMSUnknown = CMSUnknown
  final-maysat-subst (FIndet (IPairL ind1 val2))
                     (CMSPairL msat1 sat2) =
    CMSPairL (final-maysat-subst (FIndet ind1) msat1)
             (final-sat-subst (FVal val2) sat2)
  final-maysat-subst (FIndet (IPairL ind1 val2))
                     (CMSPairR sat1 msat2) =
    CMSPairR (final-sat-subst (FIndet ind1) sat1)
             (final-maysat-subst (FVal val2) msat2)
  final-maysat-subst (FIndet (IPairL ind1 val2))
                     (CMSPair msat1 msat2) =
    CMSPair (final-maysat-subst (FIndet ind1) msat1)
            (final-maysat-subst (FVal val2) msat2)
  final-maysat-subst (FIndet (IPairL ind1 val2))
                     (CMSOrL msat1 ¬sat2) =
    CMSOrL (final-maysat-subst (FIndet (IPairL ind1 val2)) msat1)
           (λ{sat2 → ¬sat2 (subst-sat sat2)})
  final-maysat-subst (FIndet (IPairL ind1 val2))
                     (CMSOrR ¬sat1 msat2) =
    CMSOrR (λ{sat1 → ¬sat1 (subst-sat sat1)})
           (final-maysat-subst (FIndet (IPairL ind1 val2)) msat2)
  final-maysat-subst (FIndet (IPairR val1 ind2))
                     CMSUnknown = CMSUnknown
  final-maysat-subst (FIndet (IPairR val1 ind2))
                     (CMSPairL msat1 sat2) =
    CMSPairL (final-maysat-subst (FVal val1) msat1)
             (final-sat-subst (FIndet ind2) sat2)
  final-maysat-subst (FIndet (IPairR val1 ind2))
                     (CMSPairR sat1 msat2) =
    CMSPairR (final-sat-subst (FVal val1) sat1)
             (final-maysat-subst (FIndet ind2) msat2)
  final-maysat-subst (FIndet (IPairR val1 ind2))
                     (CMSPair msat1 msat2) =
    CMSPair (final-maysat-subst (FVal val1) msat1)
            (final-maysat-subst (FIndet ind2) msat2)
  final-maysat-subst (FIndet (IPairR val1 ind2))
                     (CMSOrL msat1 ¬sat2) =
    CMSOrL (final-maysat-subst (FIndet (IPairR val1 ind2)) msat1)
           (λ{sat2 → ¬sat2 (subst-sat sat2)})                 
  final-maysat-subst (FIndet (IPairR val1 ind2))
                     (CMSOrR ¬sat1 msat2) =
    CMSOrR (λ{sat1 → ¬sat1 (subst-sat sat1)})
           (final-maysat-subst (FIndet (IPairR val1 ind2)) msat2)
  final-maysat-subst (FIndet (IPair ind1 ind2))
                     CMSUnknown = CMSUnknown
  final-maysat-subst (FIndet (IPair ind1 ind2))
                     (CMSPairL msat1 sat2) =
    CMSPairL (final-maysat-subst (FIndet ind1) msat1)
             (final-sat-subst (FIndet ind2) sat2)
  final-maysat-subst (FIndet (IPair ind1 ind2))
                     (CMSPairR sat1 msat2) =
    CMSPairR (final-sat-subst (FIndet ind1) sat1)
             (final-maysat-subst (FIndet ind2) msat2)
  final-maysat-subst (FIndet (IPair ind1 ind2))
                     (CMSPair msat1 msat2) =
    CMSPair (final-maysat-subst (FIndet ind1) msat1)
            (final-maysat-subst (FIndet ind2) msat2)
  final-maysat-subst (FIndet (IPair ind1 ind2))
                     (CMSOrL msat1 ¬sat2) =
    CMSOrL (final-maysat-subst (FIndet (IPair ind1 ind2)) msat1)
           (λ{sat2 → ¬sat2 (subst-sat sat2)})
  final-maysat-subst (FIndet (IPair ind1 ind2))
                     (CMSOrR ¬sat1 msat2) =
    CMSOrR (λ{sat1 → ¬sat1 (subst-sat sat1)})
           (final-maysat-subst (FIndet (IPair ind1 ind2)) msat2)
  final-maysat-subst (FIndet (IFst npr ind)) msat =
    all-notintro-maysat NVFst msat NVFst
  final-maysat-subst (FIndet (ISnd npr ind)) msat =
    all-notintro-maysat NVSnd msat NVSnd
  final-maysat-subst (FIndet IEHole) msat =
    all-notintro-maysat NVEHole msat NVEHole
  final-maysat-subst (FIndet (IHole fin)) msat =
    all-notintro-maysat NVHole msat NVHole
                       
  -- replacing a variable may allow it to satisfy something
  -- it previously did not
  subst-maysat : ∀{x e1 e2 ξ} →
                 e1 ⊧̇? ξ →
                 ([ e2 / x ] e1) ⊧̇†? ξ
  subst-maysat CMSUnknown = CSMSMay CMSUnknown
  subst-maysat (CMSInl msat)
    with subst-maysat msat
  ... | CSMSSat ssat = CSMSSat (CSInl ssat)
  ... | CSMSMay smsat = CSMSMay (CMSInl smsat)
  subst-maysat (CMSInr msat)
    with subst-maysat msat
  ... | CSMSSat ssat = CSMSSat (CSInr ssat)
  ... | CSMSMay smsat = CSMSMay (CMSInr smsat)
  subst-maysat (CMSPairL msat1 sat2)
    with subst-maysat msat1
  ... | CSMSSat ssat1 =
    CSMSSat (CSPair ssat1 (subst-sat sat2))
  ... | CSMSMay smsat1 =
    CSMSMay (CMSPairL smsat1 (subst-sat sat2))
  subst-maysat (CMSPairR sat1 msat2)
    with subst-maysat msat2
  ... | CSMSSat ssat2 =
    CSMSSat (CSPair (subst-sat sat1) ssat2)
  ... | CSMSMay smsat2 =
    CSMSMay (CMSPairR (subst-sat sat1) smsat2)
  subst-maysat (CMSPair msat1 msat2)
    with subst-maysat msat1 | subst-maysat msat2
  ... | CSMSSat ssat1 | CSMSSat ssat2 =
    CSMSSat (CSPair ssat1 ssat2)
  ... | CSMSSat ssat1 | CSMSMay smsat2 =
    CSMSMay (CMSPairR ssat1 smsat2)
  ... | CSMSMay smsat1 | CSMSSat ssat2 =
    CSMSMay (CMSPairL smsat1 ssat2)
  ... | CSMSMay smsat1 | CSMSMay smsat2 =
    CSMSMay (CMSPair smsat1 smsat2)
  subst-maysat {x = x} {e1 = e1} {e2 = e2} {ξ = ξ1 ∨ ξ2}
               (CMSOrL msat1 ¬sat2)
    with subst-maysat msat1 
  ... | CSMSSat ssat1 = CSMSSat (CSOrL ssat1)
  ... | CSMSMay smsat1
    with satisfy-dec ([ e2 / x ] e1) ξ2
  ... | Inl ssat2 = CSMSSat (CSOrR ssat2)
  ... | Inr ¬ssat2 = CSMSMay (CMSOrL smsat1 ¬ssat2)
  subst-maysat {x = x} {e1 = e1} {e2 = e2} {ξ = ξ1 ∨ ξ2}
               (CMSOrR ¬sat1 msat2)
    with subst-maysat msat2
  ... | CSMSSat ssat2 = CSMSSat (CSOrR ssat2)
  ... | CSMSMay smsat2
    with satisfy-dec ([ e2 / x ] e1) ξ1
  ... | Inl ssat1 = CSMSSat (CSOrL ssat1)
  ... | Inr ¬ssat1 = CSMSMay (CMSOrR ¬ssat1 smsat2)
  subst-maysat (CMSNotIntro ni ref pos) =
    CSMSMay (CMSNotIntro (subst-notintro ni) ref pos)
    
  subst-satormay : ∀{x e1 e2 ξ} →
                   e1 ⊧̇†? ξ →
                   ([ e2 / x ] e1) ⊧̇†? ξ
  subst-satormay (CSMSSat sat) = CSMSSat (subst-sat sat)
  subst-satormay (CSMSMay msat) = subst-maysat msat

  final-satormay-subst : ∀{x e1 e2 ξ} →
                         e1 final →
                         ([ e2 / x ] e1) ⊧̇†? ξ →
                         e1 ⊧̇†? ξ
  final-satormay-subst fin (CSMSSat sat) =
    CSMSSat (final-sat-subst fin sat)
  final-satormay-subst fin (CSMSMay msat) =
    CSMSMay (final-maysat-subst fin msat)
