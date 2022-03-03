open import List
open import Nat
open import Prelude
open import binders-disjointness
open import binders-disjoint-symmetric
open import binders-uniqueness
open import constraints-core
open import contexts
open import core
open import dynamics-core
open import exchange
open import freshness
open import freshness-decidable
open import hole-binders-disjoint-symmetric
open import lemmas-contexts
open import lemmas-freshness
open import lemmas-subst-disjointness
open import lemmas-subst-list
open import lemmas-subst-result
open import lemmas-subst-satisfy
open import patterns-core
open import result-judgements
open import statics-core
open import type-assignment-unicity
open import weakening

-- substituting a variable for an expression
-- of the same type does not change the type
-- of the resulting term
module lemmas-subst-type where
  -- quick lemma showing that substituing into an erasure
  -- behaves as expected
  subst-erase : ∀{rs-pre r rs-post rs x e2} →
                erase-r (rs-pre / r / rs-post) rs →
                erase-r ([ e2 / x ]zrs (rs-pre / r / rs-post))
                        ([ e2 / x ]rs rs)
  subst-erase ERZPre = ERZPre
  subst-erase (ERNZPre er) = ERNZPre (subst-erase er)

  -- substitutions do no affect the rule typing
  -- judgement which does not track target types.
  -- this resultis basically immediate because this rule typing
  -- judgement only actually looks at patterns, not the type of
  -- any expression
  subst-type-rs-no-target : ∀{Δp rs τ ξ x e2} →
                            Δp ⊢ rs ::s τ [ ξ ] →
                            Δp ⊢ [ e2 / x ]rs rs ::s τ [ ξ ]
  subst-type-rs-no-target {x = x} (RTOneRule {p = p} pt)
    with unbound-in-p-dec x p
  ... | Inl ub = RTOneRule pt
  ... | Inr ¬ub = RTOneRule pt
  subst-type-rs-no-target {x = x} (RTRules {p = p} pt rst)
    with unbound-in-p-dec x p
  ... | Inl ub =
    RTRules pt (subst-type-rs-no-target rst)
  ... | Inr ¬ub =
    RTRules pt (subst-type-rs-no-target rst)


  -- same as the above, but tracking nonredundancy
  subst-type-rs-nonredundant : ∀{Δp rs τ ξpre ξ x e2} →
                               Δp ⊢ rs ::s τ [ ξpre nr/ ξ ] →
                               Δp ⊢ [ e2 / x ]rs rs ::s τ [ ξpre nr/ ξ ]
  subst-type-rs-nonredundant {x = x} (RTOneRule {p = p} pt ¬red)
    with unbound-in-p-dec x p
  ... | Inl ub = RTOneRule pt ¬red
  ... | Inr ¬ub = RTOneRule pt ¬red
  subst-type-rs-nonredundant {x = x} (RTRules {p = p} pt ¬red rst)
    with unbound-in-p-dec x p
  ... | Inl ub =
    RTRules pt ¬red (subst-type-rs-nonredundant rst)
  ... | Inr ¬ub =
    RTRules pt ¬red (subst-type-rs-nonredundant rst)
    
  mutual
    -- substituting a variable for an expression of the same
    -- type does not change the type of the resulting term
    subst-type : ∀{Γ Δ Δp x τ1 e1 τ e2} →
                 binders-disjoint e1 e2 →
                 hole-binders-disjoint e1 e2 →
                 e2 final →
                 (Γ ,, (x , τ1)) , Δ , Δp ⊢ e1 :: τ →
                 Γ , Δ , Δp ⊢ e2 :: τ1 →
                 Γ , Δ , Δp ⊢ [ e2 / x ] e1 :: τ
    subst-type bd hbd fin2 TUnit wt2 = TUnit
    subst-type bd hbd fin2 TNum wt2 = TNum
    subst-type {x = x} bd hbd fin2 (TVar {x = y} y∈) wt2
      with nat-dec y x
    ... | Inl refl
      with nat-dec x x
    ... | Inr x≠x = abort (x≠x refl)
    ... | Inl refl
      with some-inj y∈
    ... | refl = wt2
    subst-type {x = x} bd hbd fin2 (TVar {x = y} y∈) wt2
        | Inr y≠x
      with nat-dec x y
    ... | Inl refl = abort (y≠x refl)
    ... | Inr x≠y = TVar y∈
    subst-type {Γ = Γ} {x = x} bd hbd bu
               (TLam {x = y} y# wts) wt2
      with nat-dec y x
    ... | Inl refl
      with nat-dec x x
    ... | Inr x≠x = abort (x≠x refl)
    ... | Inl refl = abort (some-not-none y#)
    subst-type {Γ = Γ} {x = x} (BDLam ub bd) (HBDLam hbd) fin2
               (TLam {x = y} y# wts) wt2
        | Inr y≠x
      with nat-dec x y
    ... | Inl refl = abort (y≠x refl)
    ... | Inr x≠y =
      TLam y#
            (subst-type
              bd hbd fin2
              (exchange-ta-Γ x≠y wts)
              (weaken-ta-Γ (binders-fresh wt2 ub y#) wt2))
    subst-type (BDAp bd1 bd2) (HBDAp hbd1 hbd2) fin2
               (TAp wts1 wts2) wt2 =
      TAp (subst-type bd1 hbd1 fin2 wts1 wt2)
           (subst-type bd2 hbd2 fin2 wts2 wt2)
    subst-type (BDInl bd) (HBDInl hbd) fin2 (TInl wts) wt2 =
      TInl (subst-type bd hbd fin2 wts wt2)
    subst-type (BDInr bd) (HBDInr hbd) fin2 (TInr wts) wt2 =
      TInr (subst-type bd hbd fin2 wts wt2)
    subst-type (BDMatch 1d2 (BDZRules _ (BDRules rd2 _)))
               (HBDMatch 1hd2 (HBDZRules _ (HBDRules rhd2 _))) fin2
               (TMatchZPre wts (RTOneRule rt)) wt2 = 
      TMatchZPre (subst-type 1d2 1hd2 fin2 wts wt2)
                  (RTOneRule (subst-type-r rd2 rhd2 fin2
                                           rt wt2))
    subst-type (BDMatch 1d2 (BDZRules _ (BDRules rd2 postd2)))
               (HBDMatch 1hd2 (HBDZRules _ (HBDRules rhd2 posthd2))) fin2
               (TMatchZPre wts (RTRules rt rst)) wt2 =
      TMatchZPre (subst-type 1d2 1hd2 fin2 wts wt2)
                  (RTRules (subst-type-r rd2 rhd2 fin2 rt wt2)
                           (subst-type-rs postd2 posthd2 fin2
                                          rst wt2))
    subst-type (BDMatch 1d2
                            (BDZRules pred2 (BDRules rd2 predpost)))
               (HBDMatch 1hd2
                         (HBDZRules prehd2 (HBDRules rhd2 prehdpost))) fin2
               (TMatchNZPre wts fin1 pret
                             (RTOneRule rt) ¬red) wt2 =
      TMatchNZPre (subst-type 1d2 1hd2 fin2 wts wt2)
                   (final-subst-final fin1 fin2)
                   (subst-type-rs pred2 prehd2 fin2 pret wt2)
                   (subst-type-rs (BDRules rd2 BDNoRules)
                                  (HBDRules rhd2 HBDNoRules)
                                  fin2 (RTOneRule rt) wt2)
                   λ{satm → ¬red (final-satormay-subst fin1 satm)}
    subst-type (BDMatch 1d2 (BDZRules pred2 (BDRules rd2 postd2)))
               (HBDMatch 1hd2
                         (HBDZRules prehd2 (HBDRules rhd2 posthd2))) fin2
               (TMatchNZPre wts fin1 pret
                                 (RTRules rt postt) ¬red) wt2 =
      TMatchNZPre (subst-type 1d2 1hd2 fin2 wts wt2)
                   (final-subst-final fin1 fin2)
                   (subst-type-rs pred2 prehd2 fin2 pret wt2)
                   (subst-type-rs (BDRules rd2 postd2)
                                  (HBDRules rhd2 posthd2)
                                  fin2 (RTRules rt postt) wt2)
                   λ{satm → ¬red (final-satormay-subst fin1 satm)}
    subst-type (BDPair bd1 bd2) (HBDPair hbd1 hbd2) fin2
               (TPair wts1 wts2) wt2 =
      TPair (subst-type bd1 hbd1 fin2 wts1 wt2)
             (subst-type bd2 hbd2 fin2 wts2 wt2)
    subst-type (BDFst bd) (HBDFst hbd) fin2 (TFst wts) wt2 =
      TFst (subst-type bd hbd fin2 wts wt2)
    subst-type (BDSnd bd) (HBDSnd hbd) fin2 (TSnd wts) wt2 =
      TSnd (subst-type bd hbd fin2 wts wt2)
    subst-type bd hbd fin2 (TEHole u∈Δ st) wt2 =
      TEHole u∈Δ (STSubst st wt2)
    subst-type (BDHole bdσ bd) (HBDHole hbdσ hbd) fin2
               (THole u∈Δ st wts) wt2 =
      THole u∈Δ (STSubst st wt2)
               (subst-type bd hbd fin2 wts wt2)          
    
    subst-type-rs : ∀{Γ Δ Δp x τ1 rs τ ξ τ' e2} →
                    binders-disjoint-rs rs e2 →
                    hole-binders-disjoint-rs rs e2 →
                    e2 final →
                    (Γ ,, (x , τ1)) , Δ , Δp ⊢ rs ::s τ [ ξ ]=> τ' →
                    Γ , Δ , Δp ⊢ e2 :: τ1 →
                    Γ , Δ , Δp ⊢ [ e2 / x ]rs rs ::s τ [ ξ ]=> τ'
    subst-type-rs (BDRules rd2 rsd2)
                  (HBDRules rhd2 rshd2) fin2 (RTOneRule rt) wt2 =
      RTOneRule (subst-type-r rd2 rhd2 fin2 rt wt2)
    subst-type-rs (BDRules rd2 rsd2)
                  (HBDRules rhd2 rshd2) fin2 (RTRules rt rst) wt2 =
      RTRules (subst-type-r rd2 rhd2 fin2 rt wt2)
              (subst-type-rs rsd2 rshd2 fin2 rst wt2)
              
    subst-type-r : ∀{Γ Δ Δp x τ1 r τ ξ τ' e2} →
                   binders-disjoint-r r e2 →
                   hole-binders-disjoint-r r e2 →
                   e2 final →
                   (Γ ,, (x , τ1)) , Δ , Δp ⊢ r :: τ [ ξ ]=> τ' →
                   Γ , Δ , Δp ⊢ e2 :: τ1 →
                   Γ , Δ , Δp ⊢ [ e2 / x ]r r :: τ [ ξ ]=> τ'
    subst-type-r {Γ = Γ} {Δ = Δ} {x = x} {τ1 = τ1} {e2 = e2}
                 (BDRule {p = p} pd2 1d2)
                 (HBDRule {p = p} phd2 1hd2) fin2
                 (RTRule {Γp = Γp} pt Γ,##Γp wts)
                 wt2
      with unbound-in-p-dec x p
    ... | Inr ¬ub =
      abort (¬ub (apart-Γp-unbound-in-p
                    pt
                    (disjoint-singleton-apart
                      (union-disjoint-l Γ,##Γp))))
    ... | Inl ub rewrite (∪-assoc (■ (x , τ1)) Γ Γp) =
      RTRule pt
             (union-disjoint-r {Γ1 = ■ (x , τ1)} {Γ2 = Γ} Γ,##Γp)
             (subst-type 1d2 1hd2 fin2 wts (weaken-ta-Γ∪ frsh wt2))
      where
        frsh : ∀{z} →
               dom Γp z →
               fresh z e2
        frsh {z = z} z∈Γp = 
          binders-fresh wt2
                        (dom-Γp-unbound-in pt z∈Γp pd2)
                        z#Γ
          where
            z#Γ : z # Γ
            z#Γ with Γ z in Γz
            ... | None = refl
            ... | Some τ =
              abort (some-not-none
                      (! Γz · apart-union-r (■ (x , τ1)) Γ z
                                            (π2 Γ,##Γp z z∈Γp)))

  -- the substituions emitted by a pattern match
  -- make the same typing assumptions as the pattern
  mat-substs-type : ∀{Γ Δ Δp e τ p ξ Γp θ} →
                    Γ , Δ , Δp ⊢ e :: τ →
                    Δp ⊢ p :: τ [ ξ ]⊣ Γp →
                    Γ ## Γp →
                    (e ·: τ ▹ p ⊣ θ) →
                    Γ , Δ , Δp ⊢ θ :sl: Γp
  mat-substs-type wt PTUnit Γ##Γp MUnit = STEmpty
  mat-substs-type wt PTNum Γ##Γp MNum = STEmpty
  mat-substs-type {Γ = Γ} {Δ = Δ} {Δp = Δp}
                  {e = e} {τ = τ}
                  wt PTVar Γ##Γp (MVar {x = x}) =
    tr (λ qq → Γ , Δ , Δp ⊢ (e , τ , x) :: [] :sl: qq)
       (∪-identityʳ (■ (x , τ)))
       (STExtend (disjoint-singleton-apart (##-sym Γ##Γp)) STEmpty wt)
  mat-substs-type (TInl wt) (PTInl pt) Γ##Γp (MInl mat) =
    mat-substs-type wt pt Γ##Γp mat
  mat-substs-type (TInr wt) (PTInr pt) Γ##Γp (MInr mat) =
    mat-substs-type wt pt Γ##Γp mat
  mat-substs-type {Γ = Γ} wt
                  (PTPair {Γ1 = Γ1} {Γ2 = Γ2} Γ1##Γ2 pt1 pt2)
                  Γ##Γp
                  (MPair mat1 mat2)
    with wt
  ... | TPair wt1 wt2 =
    substs-concat-type
      (mat-substs-type wt1 pt1
                       (##-sym (union-disjoint-l {Γ1 = Γ1} {Γ2 = Γ2}
                                                 (##-sym Γ##Γp)))
                       mat1)
      (mat-substs-type wt2 pt2
                       (##-sym (union-disjoint-r {Γ1 = Γ1} {Γ2 = Γ2}
                                                 (##-sym Γ##Γp)))
                       mat2)
  mat-substs-type {Γ = Γ} wt 
                  (PTPair {Γ1 = Γ1} {Γ2 = Γ2} Γ1##Γ2 pt1 pt2)
                  Γ##Γp
                  (MNotIntroPair ni mat1 mat2) =
    substs-concat-type
      (mat-substs-type (TFst wt) pt1
                       (##-sym (union-disjoint-l {Γ1 = Γ1} {Γ2 = Γ2}
                                                 (##-sym Γ##Γp)))
                       mat1)
      (mat-substs-type (TSnd wt) pt2
                       (##-sym (union-disjoint-r {Γ1 = Γ1} {Γ2 = Γ2}
                                                 (##-sym Γ##Γp)))
                       mat2)
  mat-substs-type wt PTWild Γ##Γp MWild = STEmpty

  -- appling a series of substitution for variables to expressions
  -- of the same type does not change the type of the resulting term
  substs-type : ∀{Γ Δ Δp θ Γθ e τ} →
                θ simultaneous →
                Γ , Δ , Δp ⊢ θ :sl: Γθ →
                (Γθ ∪ Γ) , Δ , Δp ⊢ e :: τ →
                Γ , Δ , Δp ⊢ apply-substs θ e :: τ
  substs-type SθEmpty STEmpty wt = wt
  substs-type {Γ = Γ} {Δ = Δ} {Δp = Δp} 
              {θ = (d , τ' , y) :: θ} {e = e} {τ = τ}
              (SθExtend yubθ sim)
              (STExtend {Γθ = Γθ} {τ = τ'} {y = y} y#Γ wst wtd)
              wt =
    TAp (TLam y#Γ
                (substs-type {Γθ = Γθ}
                             sim
                             (weaken-θ-∪Γ {Γ' = ■ (y , τ')} frsh wst)
                             (tr (λ qq → qq , Δ , Δp ⊢ e :: τ) eq wt)))
         wtd
    where
      eq : ((Γθ ,, (y , τ')) ∪ Γ) == (Γθ ∪ (Γ ,, (y , τ')))
      eq = ap1 (λ qq → qq ∪ Γ)
               (∪-comm (■ (y , τ')) Γθ
                       (apart-singleton-disjoint
                         (unbound-in-θ-apart-Γθ wst
                                                yubθ))) ·
             ∪-assoc Γθ (■ (y , τ')) Γ
      frsh : ∀{x} →
             dom (■ (y , τ')) x →
             fresh-θ x θ
      frsh x∈■ with dom-singleton-eq x∈■
      ... | refl = binders-fresh-θ wst yubθ y#Γ
