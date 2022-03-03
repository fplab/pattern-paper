open import Nat
open import Prelude
open import constraints-core
open import contexts
open import core
open import binders-disjointness
open import binders-uniqueness
open import dynamics-core
open import finality
open import lemmas-contexts
open import lemmas-or-append
open import lemmas-patterns
open import lemmas-satisfy
open import lemmas-subst-exhaustive
open import lemmas-subst-list
open import lemmas-subst-nonredundant
open import lemmas-subst-type
open import matching-coherence
open import patterns-core
open import result-judgements
open import statics-core
open import type-assignment-unicity

-- evaluating an expression preserves its type
module preservation where
  preservation : ∀{Δ Δp e1 τ e2} →
                 binders-unique e1 →
                 hole-binders-unique e1 →
                 ∅ , Δ , Δp ⊢ e1 :: τ →
                 e1 ↦ e2 →
                 ∅ , Δ , Δp ⊢ e2 :: τ
  preservation (BUAp bu1 bu2 bd) (HBUAp hbu1 hbu2 hbd)
               (TAp wt1 wt2) (ITpFun stp) = 
    TAp (preservation bu1 hbu1 wt1 stp) wt2
  preservation (BUAp bu1 bu2 bd) (HBUAp hbu1 hbu2 hbd)
               (TAp wt1 wt2) (ITpArg eval stp) =
    TAp wt1 (preservation bu2 hbu2 wt2 stp)
  preservation (BUAp bu1 bu2 (BDLam ub bd))
               (HBUAp hbu1 hbu2 (HBDLam hbd))
               (TAp (TLam x#Γ wt1) wt2) (ITp fin) =
    subst-type bd hbd fin wt1 wt2
  preservation (BUInl bu) (HBUInl hbu) (TInl wt) (ITInl stp) =
    TInl (preservation bu hbu wt stp)
  preservation (BUInr bu) (HBUInr hbu) (TInr wt) (ITInr stp) =
    TInr (preservation bu hbu wt stp)
  preservation (BUMatch bu burs bdrs)
               (HBUMatch hbu hburs hbdrs)
               (TMatchZPre wt rst) (ITExpMatch stp) =
    TMatchZPre (preservation bu hbu wt stp) rst
  preservation {Δ = Δ} {Δp = Δp} {τ = τ}
               (BUMatch bu
                        (BUZRules _ (BURules (BURule bup _ _) _ _) _)
                        (BDZRules _ (BDRules (BDRule pbde _) _)))
               (HBUMatch hbu hburs hbdrs)
               (TMatchZPre wt
                            (RTOneRule (RTRule {e = e} {Γp = Γp}
                                               pt Γ##Γp wt')))
               (ITSuccMatch fin mat) =
    substs-type (mat-substs-simultaneous bu bup pbde mat)
                (mat-substs-type wt pt Γ##Γp mat)
                (tr (λ qq → qq , Δ , Δp ⊢ e :: τ)
                    (! (∪-identityʳ Γp))
                    wt')
  preservation {Δ = Δ} {Δp = Δp} {τ = τ}
               (BUMatch bu
                        (BUZRules _ (BURules (BURule bup _ _) _ _) _)
                        (BDZRules _ (BDRules (BDRule pbde _) _)))
               (HBUMatch hbu hburs hbdrs)
               (TMatchZPre wt
                            (RTRules (RTRule {e = e} {Γp = Γp}
                                             pt Γ##Γp wt')
                                     rst))
               (ITSuccMatch fin mat) =
    substs-type (mat-substs-simultaneous bu bup pbde mat)
                (mat-substs-type wt pt Γ##Γp mat)
                (tr (λ qq → qq , Δ , Δp ⊢ e :: τ)
                    (! (∪-identityʳ Γp))
                    wt')
  preservation (BUMatch bu burs bdrs)
               (HBUMatch hbu hburs hbdrs)
               (TMatchZPre wt
                            (RTRules (RTRule pt Γ##Γp wt')
                                     rst))
               (ITFailMatch fin nmat ERZPre) =
    TMatchNZPre wt fin
                 (RTOneRule (RTRule pt Γ##Γp wt')) rst
                 (notmat-not-satormay fin wt pt nmat)
  preservation (BUMatch bu burs bdrs)
               (HBUMatch hbu hburs hbdrs)
               (TMatchNZPre wt fin pret postt ¬red)
               (ITExpMatch stp) =
    abort (final-step-not fin stp)
  preservation {Δ = Δ} {Δp = Δp} {τ = τ}
               (BUMatch bu
                        (BUZRules _ (BURules (BURule bup _ _) _ _) _)
                        (BDZRules _ (BDRules (BDRule pbde _) _)))
               (HBUMatch hbu hburs hbdrs)
               (TMatchNZPre wt fin pre
                             (RTOneRule (RTRule {e = e} {Γp = Γp}
                                                pt Γ##Γp wt'))
                             ¬red)
               (ITSuccMatch fin₁ mat) =
    substs-type (mat-substs-simultaneous bu bup pbde mat)
                (mat-substs-type wt pt Γ##Γp mat)
                (tr (λ qq → qq , Δ , Δp ⊢ e :: τ)
                    (! (∪-identityʳ Γp))
                    wt')
  preservation {Δ = Δ} {Δp = Δp} {τ = τ}
               (BUMatch bu
                        (BUZRules _ (BURules (BURule bup _ _) _ _) _)
                        (BDZRules _ (BDRules (BDRule pbde _) _)))
               (HBUMatch hbu hburs hbdrs)
               (TMatchNZPre wt fin pre
                             (RTRules (RTRule {e = e} {Γp = Γp}
                                              pt Γ##Γp wt')
                                      rst)
                             ¬red)
               (ITSuccMatch fin₁ mat) =
    substs-type (mat-substs-simultaneous bu bup pbde mat)
                (mat-substs-type wt pt Γ##Γp mat)
                (tr (λ qq → qq , Δ , Δp ⊢ e :: τ)
                    (! (∪-identityʳ Γp))
                    wt')
  preservation (BUMatch bu burs bdrs)
               (HBUMatch hbu hburs hbdrs)
               (TMatchNZPre {e = e} {ξpre = ξpre} wt fin
                             pret
                             (RTRules {ξr = ξr} {ξrs = ξrs}
                                      (RTRule pt Γ##Γp wt')
                                      postt)
                             ¬red)
               (ITFailMatch fin₁ nmat (ERNZPre er)) =
    TMatchNZPre wt fin
                 (rules-erase-constr (ERNZPre er)
                                     pret
                                     (RTOneRule (RTRule pt Γ##Γp wt')))
                 postt ¬red'
    where
      -- need to add ξr to the end of the chain of ∨s in ξpre
      ¬red' : e ⊧̇†? (ξpre ∨+ ξr) → ⊥
      ¬red' satm with or-satormay (satormay-∨+-satormay-∨ satm)
      ... | Inl satmpre = ¬red satmpre
      ... | Inr satmr =
        notmat-not-satormay fin wt pt nmat satmr
  preservation (BUPair bu1 bu2 bd) (HBUPair hbu1 hbu2 hbd)
               (TPair wt1 wt2) (ITPairL stp) =
    TPair (preservation bu1 hbu1 wt1 stp) wt2
  preservation (BUPair bu1 bu2 bd) (HBUPair hbu1 hbu2 hbd)
               (TPair wt1 wt2) (ITPairR val1 stp) =
    TPair wt1 (preservation bu2 hbu2 wt2 stp)
  preservation (BUFst bu) (HBUFst hbu) (TFst wt)
               (ITFst stp) =
    TFst (preservation bu hbu wt stp)
  preservation (BUFst bu) (HBUFst hbu)
               (TFst wt) (ITFstPair fin)
    with wt
  ... | TPair wt1 wt2 = wt1
  preservation (BUSnd bu) (HBUSnd hbu) (TSnd wt)
               (ITSnd stp) = 
    TSnd (preservation bu hbu wt stp)
  preservation (BUSnd bu) (HBUSnd hbu)
               (TSnd wt) (ITSndPair fin)
    with wt
  ... | TPair wt1 wt2 = wt2
  preservation (BUHole buσ bue σbde) (HBUHole hbuσ hbue σhbde)
               (THole u∈Δ wst wt) (ITHole stp) =
    THole u∈Δ wst (preservation bue hbue wt stp)
  
  -- because we separate exhaustiveness checking from type checking,
  -- we need a separate preservation theorem just for exhaustiveness
  exhaustive-targets-erase : ∀{Δp rs-pre r rs-post rss} →
                             erase-r (rs-pre / r / rs-post) rss →
                             Δp ⊢ rs-pre exhaustive-targets →
                             Δp ⊢ (r / rs-post) exhaustive-targets →
                             Δp ⊢ rss exhaustive-targets
  exhaustive-targets-erase ERZPre expret exrestt = exrestt
  exhaustive-targets-erase {rs-pre = (p => e) / rs}
                           (ERNZPre er) (EXRules exe exrs) exrestt =
    EXRules exe (exhaustive-targets-erase er exrs exrestt)
  
  exhaustive-preservation : ∀{Δp e1 e2} →
                            Δp ⊢ e1 exhaustive →
                            e1 ↦ e2 →
                            Δp ⊢ e2 exhaustive
  exhaustive-preservation (EXAp ex1 ex2) (ITpFun stp) =
    EXAp (exhaustive-preservation ex1 stp) ex2
  exhaustive-preservation (EXAp ex1 ex2) (ITpArg fin stp) =
    EXAp ex1 (exhaustive-preservation ex2 stp)
  exhaustive-preservation (EXAp (EXLam ex1) ex2) (ITp fin) =
    subst-exhaustive ex1 ex2
  exhaustive-preservation (EXPair ex1 ex2) (ITPairL stp) =
    EXPair (exhaustive-preservation ex1 stp) ex2
  exhaustive-preservation (EXPair ex1 ex2) (ITPairR fin stp) =
    EXPair ex1 (exhaustive-preservation ex2 stp)
  exhaustive-preservation (EXFst ex1) (ITFst stp) =
    EXFst (exhaustive-preservation ex1 stp)
  exhaustive-preservation (EXFst (EXPair ex1 ex2))
                          (ITFstPair fin) = ex1
  exhaustive-preservation (EXSnd ex1) (ITSnd stp) =
    EXSnd (exhaustive-preservation ex1 stp)
  exhaustive-preservation (EXSnd (EXPair ex1 ex2))
                          (ITSndPair fin) = ex2
  exhaustive-preservation (EXInl ex1) (ITInl stp) =
    EXInl (exhaustive-preservation ex1 stp)
  exhaustive-preservation (EXInr ex1) (ITInr stp) =
    EXInr (exhaustive-preservation ex1 stp)
  exhaustive-preservation (EXMatchZPre ex rst ent exts)
                          (ITExpMatch stp) =
    EXMatchZPre (exhaustive-preservation ex stp)
                rst ent exts
  exhaustive-preservation (EXMatchZPre ex rst ent (EXRules exet exrst))
                          (ITSuccMatch fin mat) =
    substs-exhaustive (mat-substs-exhaustive ex mat)
                      exet
  exhaustive-preservation (EXMatchZPre ex (RTRules pt rst) ent
                                       (EXRules exe exrs))
                          (ITFailMatch fin nmat ERZPre) =
    EXMatchNZPre ex (RTOneRule pt) rst ent
                 (EXRules exe EXNoRules) exrs
  exhaustive-preservation (EXMatchNZPre ex pret restt ent expret exrestt)
                          (ITExpMatch stp) =
    EXMatchNZPre (exhaustive-preservation ex stp)
                 pret restt ent expret exrestt
  exhaustive-preservation (EXMatchNZPre ex pret restt ent exprett
                                        (EXRules exet expostt))
                          (ITSuccMatch fin mat) =
    substs-exhaustive (mat-substs-exhaustive ex mat)
                      exet
  exhaustive-preservation (EXMatchNZPre {ξpre = ξpre} {ξrest = ξr ∨ ξrs}
                                        ex pret
                                        (RTRules pt postt)
                                        (PotEntails {τ = τ}
                                                    CTTruth
                                                    (CTOr ctpre (CTOr ctr ctrs))
                                                    ent)
                                        expret
                                        (EXRules exet expostt))
                          (ITFailMatch fin nmat er) =
    EXMatchNZPre ex
                 (rules-erase-constr-no-target er pret (RTOneRule pt))
                 postt
                 (PotEntails CTTruth (CTOr (∨+-type ctpre ctr) ctrs) ent')
                 (exhaustive-targets-erase er expret (EXRules exet EXNoRules))
                 expostt
    where
      ent' : ∀{Δ Δp e} →
             ∅ , Δ , Δp ⊢ e :: τ →
             e final →
             e ⊧̇†? ·⊤ →
             e ⊧̇†? ((ξpre ∨+ ξr) ∨ ξrs)
      ent' wt fin satt
        with or-satormay (ent wt fin satt)
      ... | Inl satpre =
        satormay-or-l (satormay-∨-satormay-∨+ (satormay-or-l satpre))
      ... | Inr satrest
        with or-satormay satrest
      ... | Inl satr =
        satormay-or-l (satormay-∨-satormay-∨+ (satormay-or-r satr))
      ... | Inr satrs =
        satormay-or-r satrs
  exhaustive-preservation (EXHole exσ ex1) (ITHole stp) =
    EXHole exσ (exhaustive-preservation ex1 stp)

  -- because we separate redundancy checking from type checking,
  -- we need a separate preservation theorem just for nonredundancy
  nonredundant-targets-erase : ∀{Δp rs-pre r rs-post rss} →
                               erase-r (rs-pre / r / rs-post) rss →
                               Δp ⊢ rs-pre nonredundant-targets →
                               Δp ⊢ (r / rs-post) nonredundant-targets →
                               Δp ⊢ rss nonredundant-targets
  nonredundant-targets-erase ERZPre nrpret nrrestt = nrrestt
  nonredundant-targets-erase {rs-pre = (p => e) / rs}
                             (ERNZPre er) (NRRules nre nrrs) nrrestt =
    NRRules nre (nonredundant-targets-erase er nrrs nrrestt)

  nonredundant-preservation : ∀{Δp e1 e2} →
                              Δp ⊢ e1 nonredundant →
                              e1 ↦ e2 →
                              Δp ⊢ e2 nonredundant
  nonredundant-preservation (NRAp nr1 nr2) (ITpFun stp) =
    NRAp (nonredundant-preservation nr1 stp) nr2
  nonredundant-preservation (NRAp nr1 nr2) (ITpArg fin stp) =
    NRAp nr1 (nonredundant-preservation nr2 stp)
  nonredundant-preservation (NRAp (NRLam nr1) nr2) (ITp fin) =
    subst-nonredundant nr1 nr2
  nonredundant-preservation (NRPair nr1 nr2) (ITPairL stp) =
    NRPair (nonredundant-preservation nr1 stp) nr2
  nonredundant-preservation (NRPair nr1 nr2) (ITPairR fin stp) =
    NRPair nr1 (nonredundant-preservation nr2 stp)
  nonredundant-preservation (NRFst nr) (ITFst stp) =
    NRFst (nonredundant-preservation nr stp)
  nonredundant-preservation (NRFst (NRPair nr1 nr2))
                            (ITFstPair fin) =
    nr1
  nonredundant-preservation (NRSnd nr) (ITSnd stp) =
    NRSnd (nonredundant-preservation nr stp)
  nonredundant-preservation (NRSnd (NRPair nr1 nr2))
                            (ITSndPair fin) =
    nr2
  nonredundant-preservation (NRInl nr) (ITInl stp) =
    NRInl (nonredundant-preservation nr stp)
  nonredundant-preservation (NRInr nr) (ITInr stp) =
    NRInr (nonredundant-preservation nr stp)
  nonredundant-preservation (NRMatchZPre nre rst nrt)
                            (ITExpMatch stp) =
    NRMatchZPre (nonredundant-preservation nre stp) rst nrt
  nonredundant-preservation (NRMatchNZPre nre pret restt
                                          nrpret nrrestt)
                            (ITExpMatch stp) =
    NRMatchNZPre (nonredundant-preservation nre stp)
                 pret restt nrpret nrrestt
  nonredundant-preservation (NRMatchZPre nre rst (NRRules nr nrs))
                            (ITSuccMatch fin mat) =
    substs-nonredundant (mat-substs-nonredundant nre mat)
                        nr
  nonredundant-preservation (NRMatchNZPre nre pret restt
                                          nrpret (NRRules nr nrpost))
                            (ITSuccMatch fin mat) =
    substs-nonredundant (mat-substs-nonredundant nre mat)
                        nr
  nonredundant-preservation (NRMatchZPre nr (RTRules pt ¬red rst)
                                         (NRRules nre nrrs))
                            (ITFailMatch fin nmat ERZPre) =
    NRMatchNZPre nr (RTOneRule pt ¬red) rst
                 (NRRules nre NRNoRules) nrrs
  nonredundant-preservation (NRMatchNZPre {τ = τ}
                                          {ξpre = ξpre} {ξrest = ξr ∨ ξrs}
                                          nr pret
                                          (RTRules pt ¬red restt)
                                          nrpret
                                          (NRRules nrt nrpostt))
                            (ITFailMatch fin nmat er) =
    NRMatchNZPre nr
                 (rules-erase-constr-nonredundant
                   CTFalsity er pret (RTOneRule pt ¬red))
                 (weaken-nonredundant
                   (CTOr (CTOr CTFalsity
                               (rules-constr-same-type-nonredundant pret))
                         (pattern-constr-same-type pt))
                   restt
                   ent)
                 (nonredundant-targets-erase
                   er nrpret (NRRules nrt NRNoRules))
                 nrpostt
    where
      ent : ∀{Δ Δp e} →
            ∅ , Δ , Δp ⊢ e :: τ →
            e val →
            e ⊧̇ (·⊥ ∨ (ξpre ∨+ ξr)) →
            e ⊧̇ ((·⊥ ∨ ξpre) ∨ ξr)
      ent wt eval (CSOrR sat)
        with sat-∨+-sat-∨ sat
      ... | CSOrL satpre = CSOrL (CSOrR satpre)
      ... | CSOrR satr = CSOrR satr 
  nonredundant-preservation (NRHole nr) (ITHole stp) =
    NRHole (nonredundant-preservation nr stp)

