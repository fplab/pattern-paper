open import List
open import Nat
open import Prelude
open import binders-disjointness
open import contexts
open import core
open import freshness
open import lemmas-contexts
open import patterns-core
open import result-judgements
open import statics-core

module lemmas-freshness where
  -- the emitted context Γp contains only variables
  -- occuring in the pattern
  unbound-in-p-apart-Γp : ∀{p τ ξ Γp Δp x} →
                          Δp ⊢ p :: τ [ ξ ]⊣ Γp →
                          unbound-in-p x p →
                          x # Γp
  unbound-in-p-apart-Γp PTUnit UBPUnit = refl
  unbound-in-p-apart-Γp PTNum UBPNum = refl
  unbound-in-p-apart-Γp PTVar (UBPVar x≠y) =
    neq-apart-singleton x≠y
  unbound-in-p-apart-Γp (PTInl pt) (UBPInl ub) =
    unbound-in-p-apart-Γp pt ub
  unbound-in-p-apart-Γp (PTInr pt) (UBPInr ub) =
    unbound-in-p-apart-Γp pt ub
  unbound-in-p-apart-Γp {x = x}
                        (PTPair {Γ1 = Γ1} {Γ2 = Γ2}
                                disj pt1 pt2)
                        (UBPPair ub1 ub2) =
    apart-parts Γ1 Γ2 x
                (unbound-in-p-apart-Γp pt1 ub1)
                (unbound-in-p-apart-Γp pt2 ub2)
  unbound-in-p-apart-Γp (PTEHole w∈Δp) UBPEHole = refl
  unbound-in-p-apart-Γp (PTHole w∈Δp pt) (UBPHole ub) =
    unbound-in-p-apart-Γp pt ub
  unbound-in-p-apart-Γp PTWild UBPWild = refl

  -- if a pattern is binders disjoint from a term,
  -- then anything in the emitted context Γp is
  -- unbound in said term. that is, every binder in
  -- the pattern occurs in Γp
  dom-Γp-unbound-in : ∀{p τ ξ Γp Δp x T t} →
                      {{_ : UnboundIn T}} →
                      Δp ⊢ p :: τ [ ξ ]⊣ Γp →
                      dom Γp x →
                      binders-disjoint-p {T = T} p t →
                      unbound-in x t
  dom-Γp-unbound-in PTVar x∈Γp (BDPVar {x = y} ub)
    with dom-singleton-eq x∈Γp
  ... | refl = ub
  dom-Γp-unbound-in (PTInl pt) x∈Γp (BDPInl bd) =
    dom-Γp-unbound-in pt x∈Γp bd
  dom-Γp-unbound-in (PTInr pt) x∈Γp (BDPInr bd) =
    dom-Γp-unbound-in pt x∈Γp bd
  dom-Γp-unbound-in {x = x} (PTPair {Γ1 = Γ1} {Γ2 = Γ2}
                                    Γ1##Γ2 pt1 pt2)
                    (τ , x∈Γp)
                    (BDPPair bd1 bd2)
    with dom-union-part Γ1 Γ2 x τ x∈Γp
  ... | Inl x∈Γ1 = dom-Γp-unbound-in pt1 (τ , x∈Γ1) bd1
  ... | Inr x∈Γ2 = dom-Γp-unbound-in pt2 (τ , x∈Γ2) bd2
  dom-Γp-unbound-in (PTEHole w∈Δp) () BDPEHole
  dom-Γp-unbound-in (PTHole w∈Δp pt) x∈Γp (BDPHole bd) =
    dom-Γp-unbound-in pt x∈Γp bd

  -- anything apart from the emitted context is not in the pattern
  apart-Γp-unbound-in-p : ∀{p τ ξ Γp Δp x} →
                          Δp ⊢ p :: τ [ ξ ]⊣ Γp →
                          x # Γp →
                          unbound-in-p x p
  apart-Γp-unbound-in-p PTUnit x#Γp = UBPUnit
  apart-Γp-unbound-in-p PTNum x#Γp = UBPNum
  apart-Γp-unbound-in-p {τ = τ} {x = x} (PTVar {x = y}) x#Γp =
    UBPVar (apart-singleton-neq x#Γp)
  apart-Γp-unbound-in-p (PTInl pt) x#Γp =
    UBPInl (apart-Γp-unbound-in-p pt x#Γp)
  apart-Γp-unbound-in-p (PTInr pt) x#Γp =
    UBPInr (apart-Γp-unbound-in-p pt x#Γp)
  apart-Γp-unbound-in-p {x = x}
                        (PTPair {Γ1 = Γ1} {Γ2 = Γ2}
                                Γ1##Γ2 pt1 pt2)
                        x#Γp =
    UBPPair (apart-Γp-unbound-in-p pt1
                                   (apart-union-l Γ1 Γ2 x x#Γp))
            (apart-Γp-unbound-in-p pt2
                                   (apart-union-r Γ1 Γ2 x x#Γp))
  apart-Γp-unbound-in-p (PTEHole w∈Δp) x#Γp = UBPEHole
  apart-Γp-unbound-in-p (PTHole w∈Δp pt) x#Γp =
    UBPHole (apart-Γp-unbound-in-p pt x#Γp)
  apart-Γp-unbound-in-p PTWild x#Γp = UBPWild

  -- a variable is unbound in a combined list of
  -- substitutions if its unbound in each part
  substs-concat-unbound-in : ∀{x θ1 θ2} →
                             unbound-in-θ x θ1 →
                             unbound-in-θ x θ2 →
                             unbound-in-θ x (θ1 ++ θ2)
  substs-concat-unbound-in UBθEmpty ub2 = ub2
  substs-concat-unbound-in (UBθExtend xubd x≠y ub1) ub2 =
    UBθExtend xubd x≠y (substs-concat-unbound-in ub1 ub2)

  -- for a well-typed list of substitutions, anything
  -- unbound in the list is unbound in the type Γθ
  -- recording all substitutions
  unbound-in-θ-apart-Γθ : ∀{Γ Δ Δp θ Γθ x} →
                          Γ , Δ , Δp ⊢ θ :sl: Γθ →
                          unbound-in-θ x θ →
                          x # Γθ
  unbound-in-θ-apart-Γθ STEmpty UBθEmpty = refl
  unbound-in-θ-apart-Γθ {x = x}
                        (STExtend {Γθ = Γθ} y#Γ wst wt)
                        (UBθExtend xubd x≠y xubθ) =
    neq-apart-extend Γθ x≠y
                     (unbound-in-θ-apart-Γθ wst xubθ)
                     
  -- a match expression only emits substitutions involing
  -- variables bound in the pattern
  unbound-in-mat-substs : ∀{x e τ p θ} →
                          unbound-in-e x e →
                          unbound-in-p x p →
                          e ·: τ ▹ p ⊣ θ →
                          unbound-in-θ x θ
  unbound-in-mat-substs ube UBPUnit MUnit = UBθEmpty
  unbound-in-mat-substs ube UBPNum MNum = UBθEmpty
  unbound-in-mat-substs ube (UBPVar x≠y) MVar =
    UBθExtend ube x≠y UBθEmpty
  unbound-in-mat-substs (UBInl ube) (UBPInl ubp) (MInl mat) =
    unbound-in-mat-substs ube ubp mat
  unbound-in-mat-substs (UBInr ube) (UBPInr ubp) (MInr mat) =
    unbound-in-mat-substs ube ubp mat
  unbound-in-mat-substs ube (UBPPair ubp1 ubp2) (MPair mat1 mat2)
    with ube
  ... | UBPair ube1 ube2 =
    substs-concat-unbound-in
      (unbound-in-mat-substs ube1 ubp1 mat1)
      (unbound-in-mat-substs ube2 ubp2 mat2)
  unbound-in-mat-substs ube (UBPPair ubp1 ubp2)
                        (MNotIntroPair ni mat1 mat2) =
    substs-concat-unbound-in
      (unbound-in-mat-substs (UBFst ube) ubp1 mat1)
      (unbound-in-mat-substs (UBSnd ube) ubp2 mat2)
  unbound-in-mat-substs ube UBPWild MWild = UBθEmpty

  -- analogues of the above results, but for pattern holes
  apart-Δp-hole-unbound-in-p : ∀{u p τ ξ Γp Δp} →
                               Δp ⊢ p :: τ [ ξ ]⊣ Γp →
                               u # Δp →
                               hole-unbound-in-p u p
  apart-Δp-hole-unbound-in-p PTUnit u#Δp = HUBPUnit
  apart-Δp-hole-unbound-in-p PTNum u#Δp = HUBPNum
  apart-Δp-hole-unbound-in-p PTVar u#Δp = HUBPVar
  apart-Δp-hole-unbound-in-p (PTInl pt) u#Δp =
    HUBPInl (apart-Δp-hole-unbound-in-p pt u#Δp)
  apart-Δp-hole-unbound-in-p (PTInr pt) u#Δp =
    HUBPInr (apart-Δp-hole-unbound-in-p pt u#Δp)
  apart-Δp-hole-unbound-in-p {u = u}
                             (PTPair Γ1##Γ2 pt1 pt2)
                             u#Δp =
    HUBPPair (apart-Δp-hole-unbound-in-p pt1 u#Δp)
             (apart-Δp-hole-unbound-in-p pt2 u#Δp)
  apart-Δp-hole-unbound-in-p {u = u}
                             (PTEHole {w = w} {τ = τ} w∈Δp)
                             u#Δp =
    HUBPEHole λ{refl → abort (some-not-none (! w∈Δp · u#Δp))}
  apart-Δp-hole-unbound-in-p {u = u}
                             (PTHole {w = w} {τ = τ} 
                                       w∈Δp pt)
                             u#Δp =
   HUBPHole (λ{refl → abort (some-not-none (! w∈Δp · u#Δp))})
              (apart-Δp-hole-unbound-in-p pt u#Δp)
  apart-Δp-hole-unbound-in-p PTWild u#Δp = HUBPWild

  -- if a term is well-typed, then any free variable must
  -- appear in the context. thus, if something is both
  -- apart from the typing context and unbound in the expression,
  -- it must be fresh in the expression
  mutual
    binders-fresh-r : ∀{Γ Δ Δp r τ1 ξ τ2 x} →
                      Γ , Δ , Δp ⊢ r :: τ1 [ ξ ]=> τ2 →
                      unbound-in-r x r →
                      x # Γ →
                      fresh-r x r
    binders-fresh-r {Γ = Γ} {x = x}
                    (RTRule {Γp = Γp} pt Γ##Γp wt)
                    (UBRule xubp xube) x#Γ =        
      FRule xubp
            (binders-fresh wt xube
              (apart-parts Γ Γp x x#Γ
                (unbound-in-p-apart-Γp pt xubp)))

    binders-fresh-rs : ∀{Γ Δ Δp rs τ1 ξ τ2 x} →
                       Γ , Δ , Δp ⊢ rs ::s τ1 [ ξ ]=> τ2 →
                       unbound-in-rs x rs →
                       x # Γ →
                       fresh-rs x rs
    binders-fresh-rs (RTOneRule rt) (UBRules xubr _) x#Γ = 
      FRules (binders-fresh-r rt xubr x#Γ) FNoRules
    binders-fresh-rs (RTRules rt rst)
                     (UBRules xubr xubrs) x#Γ =
      FRules (binders-fresh-r rt xubr x#Γ)
             (binders-fresh-rs rst xubrs x#Γ)

    binders-fresh-σ : ∀{Γ Δ Δp σ Γ' x} →
                      Γ , Δ , Δp ⊢ σ :se: Γ' →
                      unbound-in-σ x σ →
                      x # Γ →
                      fresh-σ x σ
    binders-fresh-σ {Γ' = Γ'} {x = x} (STId Γ'⊆Γ) UBσId x#Γ =
      FσId x#Γ'
      where
        x#Γ' : x # Γ'
        x#Γ' with Γ' x in Γ'x
        ... | Some τ =
          abort (some-not-none (! (Γ'⊆Γ x τ Γ'x) · x#Γ))
        ... | None = refl
    binders-fresh-σ {Γ = Γ} (STSubst st wt) (UBσSubst ub x≠y ubσ) x#Γ =
      FσSubst (binders-fresh wt ub x#Γ)
              x≠y
              (binders-fresh-σ st ubσ (neq-apart-extend Γ x≠y x#Γ))

    binders-fresh-θ : ∀{Γ Δ Δp θ Γ' x} →
                      Γ , Δ , Δp ⊢ θ :sl: Γ' →
                      unbound-in-θ x θ →
                      x # Γ →
                      fresh-θ x θ
    binders-fresh-θ STEmpty ub x#Γ = FθEmpty
    binders-fresh-θ (STExtend y#Γ wst wt)
                    (UBθExtend ubd x≠y ubθ) x#Γ =
      FθExtend (binders-fresh wt ubd x#Γ)
               x≠y
               (binders-fresh-θ wst ubθ x#Γ)
                      
    binders-fresh : ∀{Γ Δ Δp e τ x} →
                    Γ , Δ , Δp ⊢ e :: τ →
                    unbound-in x e →
                    x # Γ →
                    fresh x e
    binders-fresh TUnit UBUnit x#Γ = FUnit
    binders-fresh TNum UBNum x#Γ = FNum
    binders-fresh (TVar {x = y} y∈Γ) UBVar x#Γ =
      FVar (λ{ refl → some-not-none ((! y∈Γ) · x#Γ) })
    binders-fresh {Γ = Γ} (TLam {x = y} y#Γ wt)
                  (UBLam x≠y xub) x#Γ =
      FLam x≠y (binders-fresh wt xub (neq-apart-extend Γ x≠y x#Γ))
    binders-fresh (TAp wt1 wt2) (UBAp ub1 ub2) x#Γ =
      FAp (binders-fresh wt1 ub1 x#Γ) (binders-fresh wt2 ub2 x#Γ)
    binders-fresh (TInl wt) (UBInl ub) x#Γ =
      FInl (binders-fresh wt ub x#Γ)
    binders-fresh (TInr wt) (UBInr ub) x#Γ =
      FInr (binders-fresh wt ub x#Γ)
    binders-fresh (TMatchZPre {r = p => d} wt (RTOneRule rt))
                  (UBMatch xube (UBZRules UBNoRules
                                          (UBRules ubr _))) x#Γ =
      FMatch (binders-fresh wt xube x#Γ)
             (FZRules FNoRules
                      (FRules (binders-fresh-r rt ubr x#Γ)
                              FNoRules))
    binders-fresh (TMatchZPre {r = p => d} wt (RTRules rt rst))
                  (UBMatch xube (UBZRules _ (UBRules ubr xubrs))) x#Γ =
      FMatch (binders-fresh wt xube x#Γ)
             (FZRules FNoRules
                      (FRules (binders-fresh-r rt ubr x#Γ)
                              (binders-fresh-rs rst xubrs x#Γ)))
    binders-fresh (TMatchNZPre wt fin pret (RTOneRule rt) ¬red)
                  (UBMatch xube
                           (UBZRules xubpre
                                     (UBRules xubr xubpost))) x#Γ =
      FMatch (binders-fresh wt xube x#Γ)
             (FZRules (binders-fresh-rs pret xubpre x#Γ)
                      (FRules (binders-fresh-r rt xubr x#Γ)
                              FNoRules))
    binders-fresh (TMatchNZPre wt fin pret
                                (RTRules rt postt) ¬red)
                  (UBMatch xube
                           (UBZRules xubpre
                                     (UBRules xubr xubpost))) x#Γ =
      FMatch (binders-fresh wt xube x#Γ)
             (FZRules (binders-fresh-rs pret xubpre x#Γ)
                      (FRules (binders-fresh-r rt xubr x#Γ)
                              (binders-fresh-rs postt xubpost x#Γ)))
    binders-fresh (TPair wt1 wt2) (UBPair ub1 ub2) x#Γ =
      FPair (binders-fresh wt1 ub1 x#Γ)
            (binders-fresh wt2 ub2 x#Γ)
    binders-fresh (TFst wt) (UBFst ub) x#Γ =
      FFst (binders-fresh wt ub x#Γ)
    binders-fresh (TSnd wt) (UBSnd ub) x#Γ =
      FSnd (binders-fresh wt ub x#Γ)
    binders-fresh (TEHole u∈Δ st) (UBEHole ubσ) x#Γ =
      FEHole (binders-fresh-σ st ubσ x#Γ)
    binders-fresh (THole u∈Δ st wt) (UBHole ubσ ub) x#Γ =
      FHole (binders-fresh-σ st ubσ x#Γ) (binders-fresh wt ub x#Γ)

  mutual
    hole-binders-fresh-r : ∀{Γ Δ Δp r τ1 ξ τ2 u} →
                           Γ , Δ , Δp ⊢ r :: τ1 [ ξ ]=> τ2 →
                           hole-unbound-in-r u r →
                           u # Δ →
                           hole-fresh-r u r
    hole-binders-fresh-r {Δ = Δ} {u = u}
                         (RTRule {Δp = Δp} pt Γ##Γp wt)
                         (HUBRule ubp ube) u#Δ =
      HFRule ubp
             (hole-binders-fresh wt ube u#Δ)

    hole-binders-fresh-rs : ∀{Γ Δ Δp rs τ1 ξ τ2 u} →
                            Γ , Δ , Δp ⊢ rs ::s τ1 [ ξ ]=> τ2 →
                            hole-unbound-in-rs u rs →
                            u # Δ →
                            hole-fresh-rs u rs
    hole-binders-fresh-rs (RTOneRule rt) (HUBRules ubr _) u#Δ = 
      HFRules (hole-binders-fresh-r rt ubr u#Δ) HFNoRules
    hole-binders-fresh-rs (RTRules rt rst)
                     (HUBRules ubr ubrs) u#Δ =
      HFRules (hole-binders-fresh-r rt ubr u#Δ)
              (hole-binders-fresh-rs rst ubrs u#Δ)

    hole-binders-fresh-σ : ∀{Γ Δ Δp σ Γ' u} →
                           Γ , Δ , Δp ⊢ σ :se: Γ' →
                           hole-unbound-in-σ u σ →
                           u # Δ →
                           hole-fresh-σ u σ
    hole-binders-fresh-σ (STId Γ⊆Γ') HUBσId u#Δ = HFσId
    hole-binders-fresh-σ (STSubst st wt) (HUBσSubst ub ubσ) u#Δ =
      HFσSubst (hole-binders-fresh wt ub u#Δ)
               (hole-binders-fresh-σ st ubσ u#Δ)
              
    hole-binders-fresh : ∀{Γ Δ Δp e τ u} →
                         Γ , Δ , Δp ⊢ e :: τ →
                         hole-unbound-in u e →
                         u # Δ →
                         hole-fresh u e
    hole-binders-fresh TUnit HUBUnit u#Δ = HFUnit
    hole-binders-fresh TNum HUBNum u#Δ = HFNum
    hole-binders-fresh (TVar x∈Γ) HUBVar u#Δ = HFVar
    hole-binders-fresh (TLam x#Γ wt) (HUBLam ub) u#Δ =
      HFLam (hole-binders-fresh wt ub u#Δ)
    hole-binders-fresh (TAp wt1 wt2) (HUBAp ub1 ub2) u#Δ =
      HFAp (hole-binders-fresh wt1 ub1 u#Δ)
           (hole-binders-fresh wt2 ub2 u#Δ)
    hole-binders-fresh (TInl wt) (HUBInl ub) u#Δ =
      HFInl (hole-binders-fresh wt ub u#Δ)
    hole-binders-fresh (TInr wt) (HUBInr ub) u#Δ =
      HFInr (hole-binders-fresh wt ub u#Δ)
    hole-binders-fresh (TMatchZPre {r = p => d} wt (RTOneRule rt))
                       (HUBMatch ube
                                 (HUBZRules HUBNoRules (HUBRules ubr _)))
                       u#Δ =
      HFMatch (hole-binders-fresh wt ube u#Δ)
              (HFZRules HFNoRules
                        (HFRules (hole-binders-fresh-r rt ubr u#Δ)
                                 HFNoRules))
    hole-binders-fresh (TMatchZPre {r = p => d} wt
                                    (RTRules rt rst))
                       (HUBMatch ube (HUBZRules _ (HUBRules ubr ubrs))) u#Δ =
      HFMatch (hole-binders-fresh wt ube u#Δ)
              (HFZRules HFNoRules
                        (HFRules (hole-binders-fresh-r rt ubr u#Δ)
                                 (hole-binders-fresh-rs rst ubrs u#Δ)))
    hole-binders-fresh (TMatchNZPre wt fin pret
                                     (RTOneRule rt) ¬red)
                       (HUBMatch ube (HUBZRules ubpre (HUBRules ubr ubpost)))
                       u#Δ =
      HFMatch (hole-binders-fresh wt ube u#Δ)
              (HFZRules (hole-binders-fresh-rs pret ubpre u#Δ)
                        (HFRules (hole-binders-fresh-r rt ubr u#Δ)
                                 HFNoRules))
    hole-binders-fresh (TMatchNZPre wt fin pret
                                     (RTRules rt postt) ¬red)
                       (HUBMatch ube (HUBZRules ubpre (HUBRules ubr ubpost)))
                       u#Δ =
      HFMatch (hole-binders-fresh wt ube u#Δ)
              (HFZRules (hole-binders-fresh-rs pret ubpre u#Δ)
                        (HFRules (hole-binders-fresh-r rt ubr u#Δ)
                                 (hole-binders-fresh-rs postt ubpost u#Δ)))
    hole-binders-fresh (TPair wt1 wt2) (HUBPair ub1 ub2) u#Δ =
       HFPair (hole-binders-fresh wt1 ub1 u#Δ)
              (hole-binders-fresh wt2 ub2 u#Δ)
    hole-binders-fresh (TFst wt) (HUBFst ub) u#Δ =
       HFFst (hole-binders-fresh wt ub u#Δ)
    hole-binders-fresh (TSnd wt) (HUBSnd ub) u#Δ =
       HFSnd (hole-binders-fresh wt ub u#Δ)
    hole-binders-fresh (TEHole {u = u'} u'∈Δ st) (HUBEHole ubσ) u#Δ =
      HFEHole (λ{refl → some-not-none (! u'∈Δ · u#Δ)})
              (hole-binders-fresh-σ st ubσ u#Δ)
    hole-binders-fresh (THole {u = u'} u'∈Δ st wt)
                       (HUBHole ubσ ub) u#Δ =
      HFHole (λ{refl → some-not-none (! u'∈Δ · u#Δ)})
               (hole-binders-fresh-σ st ubσ u#Δ)
               (hole-binders-fresh wt ub u#Δ)
                
