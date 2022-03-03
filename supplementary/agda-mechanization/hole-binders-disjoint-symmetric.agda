open import List
open import Nat
open import Prelude
open import binders-disjointness
open import contexts
open import core
open import freshness
open import lemmas-contexts
open import patterns-core

module hole-binders-disjoint-symmetric where
  -- these lemmas build up to proving that the various
  -- hole disjointness judgements are symmetric.
  --
  -- more specifically, the definitions of the disjointness
  -- judgements deconstruct on the first argument, while
  -- leaving the second argument generic. these lemmas
  -- show that you can instead deconstruct on the second
  -- arugment. all of these results are entirely mechanical,
  -- but horribly tedious.
  mutual
    lem-hbd-lam : {e : ihexp} {x : Nat} {τ1 : htyp} {e1 : ihexp} →
                  hole-binders-disjoint e (·λ x ·[ τ1 ] e1) →
                  hole-binders-disjoint e e1
    lem-hbd-lam HBDUnit = HBDUnit
    lem-hbd-lam HBDNum = HBDNum
    lem-hbd-lam HBDVar = HBDVar
    lem-hbd-lam (HBDLam bd) = HBDLam (lem-hbd-lam bd)
    lem-hbd-lam (HBDAp bd1 bd2) =
      HBDAp (lem-hbd-lam bd1) (lem-hbd-lam bd2)
    lem-hbd-lam (HBDInl bd) = HBDInl (lem-hbd-lam bd)
    lem-hbd-lam (HBDInr bd) = HBDInr (lem-hbd-lam bd)
    lem-hbd-lam (HBDMatch bd (HBDZRules bdpre bdpost)) =
      HBDMatch (lem-hbd-lam bd)
               (HBDZRules (lem-hbd-rs-lam bdpre)
                          (lem-hbd-rs-lam bdpost))
    lem-hbd-lam (HBDPair bd1 bd2) =
      HBDPair (lem-hbd-lam bd1) (lem-hbd-lam bd2)
    lem-hbd-lam (HBDFst bd) = HBDFst (lem-hbd-lam bd)
    lem-hbd-lam (HBDSnd bd) = HBDSnd (lem-hbd-lam bd)
    lem-hbd-lam (HBDEHole bdσ) = HBDEHole (lem-hbd-σ-lam bdσ)
    lem-hbd-lam (HBDHole bdσ bd) =
      HBDHole (lem-hbd-σ-lam bdσ) (lem-hbd-lam bd)

    lem-hbd-σ-lam : {σ : subst-env} {x : Nat} {τ1 : htyp} {e1 : ihexp} →
                    hole-binders-disjoint-σ σ (·λ x ·[ τ1 ] e1) →
                    hole-binders-disjoint-σ σ e1
    lem-hbd-σ-lam HBDσId = HBDσId
    lem-hbd-σ-lam (HBDσSubst bd bdσ) =
      HBDσSubst (lem-hbd-lam bd) (lem-hbd-σ-lam bdσ)
      
    lem-hbd-rs-lam : {rs : rules} {x : Nat} {τ1 : htyp} {e1 : ihexp} →
                     hole-binders-disjoint-rs rs (·λ x ·[ τ1 ] e1) →
                     hole-binders-disjoint-rs rs e1  
    lem-hbd-rs-lam HBDNoRules = HBDNoRules
    lem-hbd-rs-lam (HBDRules bdr bdrs) =
      HBDRules (lem-hbd-r-lam bdr) (lem-hbd-rs-lam bdrs)

    lem-hbd-r-lam : {r : rule} {x : Nat} {τ1 : htyp} {e1 : ihexp} →
                    hole-binders-disjoint-r r (·λ x ·[ τ1 ] e1) →
                    hole-binders-disjoint-r r e1
    lem-hbd-r-lam (HBDRule bdp bd) =
      HBDRule (lem-hbd-p-lam bdp) (lem-hbd-lam bd)

    lem-hbd-p-lam : {p : pattrn} {x : Nat} {τ1 : htyp} {e1 : ihexp} →
                    hole-binders-disjoint-p p (·λ x ·[ τ1 ] e1) →
                    hole-binders-disjoint-p p e1
    lem-hbd-p-lam HBDPUnit = HBDPUnit
    lem-hbd-p-lam HBDPNum = HBDPNum
    lem-hbd-p-lam HBDPVar = HBDPVar
    lem-hbd-p-lam (HBDPInl bd) = HBDPInl (lem-hbd-p-lam bd)
    lem-hbd-p-lam (HBDPInr bd) = HBDPInr (lem-hbd-p-lam bd)
    lem-hbd-p-lam (HBDPPair bd1 bd2) =
      HBDPPair (lem-hbd-p-lam bd1) (lem-hbd-p-lam bd2)
    lem-hbd-p-lam HBDPWild = HBDPWild
    lem-hbd-p-lam (HBDPEHole (HUBLam ub)) = HBDPEHole ub
    lem-hbd-p-lam (HBDPHole (HUBLam ub) bd) =
      HBDPHole ub (lem-hbd-p-lam bd)
    
  mutual
    lem-hbd-ap : {e : ihexp} {e1 e2 : ihexp} →
                 hole-binders-disjoint e (e1 ∘ e2) →
                 hole-binders-disjoint e e1 ×
                   hole-binders-disjoint e e2
    lem-hbd-ap HBDUnit = HBDUnit , HBDUnit
    lem-hbd-ap HBDNum = HBDNum , HBDNum
    lem-hbd-ap HBDVar = HBDVar , HBDVar
    lem-hbd-ap (HBDLam bd)
      with lem-hbd-ap bd
    ... | bd1 , bd2 = HBDLam bd1 , HBDLam bd2
    lem-hbd-ap (HBDAp bd1 bd2)
      with lem-hbd-ap bd1 | lem-hbd-ap bd2
    ... | bd1₁ , bd1₂ | bd2₁ , bd2₂ =
      HBDAp bd1₁ bd2₁ , HBDAp bd1₂ bd2₂
    lem-hbd-ap (HBDInl bd)
      with lem-hbd-ap bd
    ... | bd1 , bd2 = HBDInl bd1 , HBDInl bd2
    lem-hbd-ap (HBDInr bd)
      with lem-hbd-ap bd
    ... | bd1 , bd2 = HBDInr bd1 , HBDInr bd2
    lem-hbd-ap (HBDMatch bd (HBDZRules pret postt))
      with lem-hbd-ap bd |
           lem-hbd-rs-ap pret |
           lem-hbd-rs-ap postt
    ... | bd1 , bd2 
        |  bdpre1 , bdpre2
        | bdpost1 , bdpost2 =
      HBDMatch bd1 (HBDZRules bdpre1 bdpost1) ,
      HBDMatch bd2 (HBDZRules bdpre2 bdpost2)
    lem-hbd-ap (HBDPair bd1 bd2)
      with lem-hbd-ap bd1 | lem-hbd-ap bd2
    ... | bd1₁ , bd1₂ | bd2₁ , bd2₂ =
      HBDPair bd1₁ bd2₁ , HBDPair bd1₂ bd2₂
    lem-hbd-ap (HBDFst bd)
      with lem-hbd-ap bd
    ... | bd1 , bd2 = HBDFst bd1 , HBDFst bd2
    lem-hbd-ap (HBDSnd bd)
      with lem-hbd-ap bd
    ... | bd1 , bd2 = HBDSnd bd1 , HBDSnd bd2
    lem-hbd-ap (HBDEHole bdσ)
      with lem-hbd-σ-ap bdσ
    ... | bdσ1 , bdσ2 = HBDEHole bdσ1 , HBDEHole bdσ2
    lem-hbd-ap (HBDHole bdσ bd)
      with lem-hbd-σ-ap bdσ | lem-hbd-ap bd
    ... | bdσ1 , bdσ2 | bd1 , bd2 =
      HBDHole bdσ1 bd1 , HBDHole bdσ2 bd2

    lem-hbd-σ-ap : {σ : subst-env} {e1 e2 : ihexp} →
                  hole-binders-disjoint-σ σ (e1 ∘ e2) →
                  hole-binders-disjoint-σ σ e1 ×
                    hole-binders-disjoint-σ σ e2
    lem-hbd-σ-ap HBDσId = HBDσId , HBDσId
    lem-hbd-σ-ap (HBDσSubst bd bdσ)
      with lem-hbd-ap bd | lem-hbd-σ-ap bdσ
    ... | bd1 , bd2 | bdσ1 , bdσ2 =
      HBDσSubst bd1 bdσ1 , HBDσSubst bd2 bdσ2 
      
    lem-hbd-rs-ap : {rs : rules} {e1 e2 : ihexp} →
                    hole-binders-disjoint-rs rs (e1 ∘ e2) →
                    hole-binders-disjoint-rs rs e1 ×
                      hole-binders-disjoint-rs rs e2
    lem-hbd-rs-ap HBDNoRules = HBDNoRules , HBDNoRules
    lem-hbd-rs-ap (HBDRules bdr bdrs)
      with lem-hbd-r-ap bdr | lem-hbd-rs-ap bdrs
    ... | bdr1 , bdr2 | bd1 , bd2 =
      HBDRules bdr1 bd1 , HBDRules bdr2 bd2
      
    lem-hbd-r-ap : {r : rule} {e1 e2 : ihexp} →
                   hole-binders-disjoint-r r (e1 ∘ e2) →
                   hole-binders-disjoint-r r e1 ×
                     hole-binders-disjoint-r r e2
    lem-hbd-r-ap (HBDRule pt bd)
      with lem-hbd-p-ap pt | lem-hbd-ap bd
    ... | pt1 , pt2 | bd1 , bd2 =
      HBDRule pt1 bd1 , HBDRule pt2 bd2

    lem-hbd-p-ap : {p : pattrn} {e1 e2 : ihexp} →
                   hole-binders-disjoint-p p (e1 ∘ e2) →
                   hole-binders-disjoint-p p e1 ×
                     hole-binders-disjoint-p p e2
    lem-hbd-p-ap HBDPUnit = HBDPUnit , HBDPUnit
    lem-hbd-p-ap HBDPNum = HBDPNum , HBDPNum
    lem-hbd-p-ap HBDPVar = HBDPVar , HBDPVar
    lem-hbd-p-ap (HBDPInl bd)
      with lem-hbd-p-ap bd
    ... | bd1 , bd2 = HBDPInl bd1 , HBDPInl bd2
    lem-hbd-p-ap (HBDPInr bd)
      with lem-hbd-p-ap bd
    ... | bd1 , bd2 = HBDPInr bd1 , HBDPInr bd2
    lem-hbd-p-ap (HBDPPair bd1 bd2)
      with lem-hbd-p-ap bd1 | lem-hbd-p-ap bd2
    ... | bd1₁ , bd1₂ | bd2₁ , bd2₂ =
      HBDPPair bd1₁ bd2₁ , HBDPPair bd1₂ bd2₂
    lem-hbd-p-ap HBDPWild = HBDPWild , HBDPWild
    lem-hbd-p-ap (HBDPEHole (HUBAp ub1 ub2)) =
      HBDPEHole ub1 , HBDPEHole ub2
    lem-hbd-p-ap (HBDPHole (HUBAp ub1 ub2) bd)
      with lem-hbd-p-ap bd
    ... | bd1 , bd2 =
      HBDPHole ub1 bd1 , HBDPHole ub2 bd2

  mutual
    lem-hbd-inl : {e : ihexp} {τ : htyp} {e1 : ihexp} →
                  hole-binders-disjoint e (inl τ e1) →
                  hole-binders-disjoint e e1
    lem-hbd-inl HBDUnit = HBDUnit
    lem-hbd-inl HBDNum = HBDNum
    lem-hbd-inl HBDVar = HBDVar
    lem-hbd-inl (HBDLam bd) = HBDLam (lem-hbd-inl bd)
    lem-hbd-inl (HBDAp bd1 bd2) =
      HBDAp (lem-hbd-inl bd1) (lem-hbd-inl bd2)
    lem-hbd-inl (HBDInl bd) = HBDInl (lem-hbd-inl bd)
    lem-hbd-inl (HBDInr bd) = HBDInr (lem-hbd-inl bd)
    lem-hbd-inl (HBDMatch bd (HBDZRules bdpre bdpost)) =
      HBDMatch (lem-hbd-inl bd)
              (HBDZRules (lem-hbd-rs-inl bdpre)
                        (lem-hbd-rs-inl bdpost))
    lem-hbd-inl (HBDPair bd1 bd2) =
      HBDPair (lem-hbd-inl bd1) (lem-hbd-inl bd2)
    lem-hbd-inl (HBDFst bd) = HBDFst (lem-hbd-inl bd)
    lem-hbd-inl (HBDSnd bd) = HBDSnd (lem-hbd-inl bd)
    lem-hbd-inl (HBDEHole bdσ) =
      HBDEHole (lem-hbd-σ-inl bdσ)
    lem-hbd-inl (HBDHole bdσ bd) =
      HBDHole (lem-hbd-σ-inl bdσ) (lem-hbd-inl bd)

    lem-hbd-σ-inl : {σ : subst-env} {τ : htyp} {e1 : ihexp} →
                   hole-binders-disjoint-σ σ (inl τ e1) →
                   hole-binders-disjoint-σ σ e1
    lem-hbd-σ-inl HBDσId = HBDσId
    lem-hbd-σ-inl (HBDσSubst bd bdσ) =
      HBDσSubst (lem-hbd-inl bd) (lem-hbd-σ-inl bdσ)
      
    lem-hbd-rs-inl : {rs : rules} {τ : htyp} {e1 : ihexp} →
                     hole-binders-disjoint-rs rs (inl τ e1) →
                     hole-binders-disjoint-rs rs e1
    lem-hbd-rs-inl HBDNoRules = HBDNoRules
    lem-hbd-rs-inl (HBDRules bdr bdrs) =
      HBDRules (lem-hbd-r-inl bdr) (lem-hbd-rs-inl bdrs)

    lem-hbd-r-inl : {r : rule} {τ : htyp} {e1 : ihexp} →
                    hole-binders-disjoint-r r (inl τ e1) →
                    hole-binders-disjoint-r r e1
    lem-hbd-r-inl (HBDRule bdp bd) =
      HBDRule (lem-hbd-p-inl bdp) (lem-hbd-inl bd)

    lem-hbd-p-inl : {p : pattrn} {τ : htyp} {e1 : ihexp} →
                    hole-binders-disjoint-p p (inl τ e1) →
                    hole-binders-disjoint-p p e1
    lem-hbd-p-inl HBDPUnit = HBDPUnit
    lem-hbd-p-inl HBDPNum = HBDPNum
    lem-hbd-p-inl HBDPVar = HBDPVar
    lem-hbd-p-inl (HBDPInl bd) = HBDPInl (lem-hbd-p-inl bd)
    lem-hbd-p-inl (HBDPInr bd) = HBDPInr (lem-hbd-p-inl bd)
    lem-hbd-p-inl (HBDPPair bd1 bd2) =
      HBDPPair (lem-hbd-p-inl bd1) (lem-hbd-p-inl bd2)
    lem-hbd-p-inl HBDPWild = HBDPWild
    lem-hbd-p-inl (HBDPEHole (HUBInl ub)) = HBDPEHole ub
    lem-hbd-p-inl (HBDPHole (HUBInl ub) bd) =
      HBDPHole ub (lem-hbd-p-inl bd)
    
  mutual
    lem-hbd-inr : {e : ihexp} {τ : htyp} {e1 : ihexp} →
                  hole-binders-disjoint e (inr τ e1) →
                  hole-binders-disjoint e e1
    lem-hbd-inr HBDUnit = HBDUnit
    lem-hbd-inr HBDNum = HBDNum
    lem-hbd-inr HBDVar = HBDVar
    lem-hbd-inr (HBDLam bd) = HBDLam (lem-hbd-inr bd)
    lem-hbd-inr (HBDAp bd1 bd2) =
      HBDAp (lem-hbd-inr bd1) (lem-hbd-inr bd2)
    lem-hbd-inr (HBDInl bd) = HBDInl (lem-hbd-inr bd)
    lem-hbd-inr (HBDInr bd) = HBDInr (lem-hbd-inr bd)
    lem-hbd-inr (HBDMatch bd (HBDZRules bdpre bdpost)) =
      HBDMatch (lem-hbd-inr bd)
               (HBDZRules (lem-hbd-rs-inr bdpre)
                          (lem-hbd-rs-inr bdpost))
    lem-hbd-inr (HBDPair bd1 bd2) =
      HBDPair (lem-hbd-inr bd1) (lem-hbd-inr bd2)
    lem-hbd-inr (HBDFst bd) = HBDFst (lem-hbd-inr bd)
    lem-hbd-inr (HBDSnd bd) = HBDSnd (lem-hbd-inr bd)
    lem-hbd-inr (HBDEHole bdσ) =
      HBDEHole (lem-hbd-σ-inr bdσ)
    lem-hbd-inr (HBDHole bdσ bd) =
      HBDHole (lem-hbd-σ-inr bdσ) (lem-hbd-inr bd)

    lem-hbd-σ-inr : {σ : subst-env} {τ : htyp} {e1 : ihexp} →
                    hole-binders-disjoint-σ σ (inr τ e1) →
                    hole-binders-disjoint-σ σ e1
    lem-hbd-σ-inr HBDσId = HBDσId
    lem-hbd-σ-inr (HBDσSubst bd bdσ) =
      HBDσSubst (lem-hbd-inr bd) (lem-hbd-σ-inr bdσ)
      
    lem-hbd-rs-inr : {rs : rules} {τ : htyp} {e1 : ihexp} →
                     hole-binders-disjoint-rs rs (inr τ e1) →
                     hole-binders-disjoint-rs rs e1
    lem-hbd-rs-inr HBDNoRules = HBDNoRules
    lem-hbd-rs-inr (HBDRules bdr bdrs) =
      HBDRules (lem-hbd-r-inr bdr) (lem-hbd-rs-inr bdrs)

    lem-hbd-r-inr : {r : rule} {τ : htyp} {e1 : ihexp}  →
                    hole-binders-disjoint-r r (inr τ e1) →
                    hole-binders-disjoint-r r e1
    lem-hbd-r-inr (HBDRule bdp bd) =
      HBDRule (lem-hbd-p-inr bdp) (lem-hbd-inr bd)

    lem-hbd-p-inr : {p : pattrn} {τ : htyp} {e1 : ihexp} →
                    hole-binders-disjoint-p p (inr τ e1) →
                    hole-binders-disjoint-p p e1
    lem-hbd-p-inr HBDPUnit = HBDPUnit
    lem-hbd-p-inr HBDPNum = HBDPNum
    lem-hbd-p-inr HBDPVar = HBDPVar
    lem-hbd-p-inr (HBDPInl bd) = HBDPInl (lem-hbd-p-inr bd)
    lem-hbd-p-inr (HBDPInr bd) = HBDPInr (lem-hbd-p-inr bd)
    lem-hbd-p-inr (HBDPPair bd1 bd2) =
      HBDPPair (lem-hbd-p-inr bd1) (lem-hbd-p-inr bd2)
    lem-hbd-p-inr HBDPWild = HBDPWild
    lem-hbd-p-inr (HBDPEHole (HUBInr ub)) = HBDPEHole ub
    lem-hbd-p-inr (HBDPHole (HUBInr ub) bd) =
      HBDPHole ub (lem-hbd-p-inr bd)
    
  mutual
    lem-hbd-match : {e : ihexp} {e1 : ihexp} {τ : htyp}
                    {rs-pre : rules} {r : rule} {rs-post : rules} →
                    hole-binders-disjoint e
                      (match e1 ·: τ of (rs-pre / r / rs-post)) →
                    hole-binders-disjoint e e1 ×
                      hole-binders-disjoint e rs-pre ×
                        hole-binders-disjoint e r ×
                          hole-binders-disjoint e rs-post
    lem-hbd-match HBDUnit = HBDUnit , HBDUnit , HBDUnit , HBDUnit
    lem-hbd-match HBDNum = HBDNum , HBDNum , HBDNum , HBDNum
    lem-hbd-match HBDVar = HBDVar , HBDVar , HBDVar , HBDVar
    lem-hbd-match (HBDLam bd)
      with lem-hbd-match bd
    ... | bd' , bdpre , bdr , bdpost =
      HBDLam bd' , HBDLam bdpre , HBDLam bdr , HBDLam bdpost
    lem-hbd-match (HBDAp bd1 bd2)
      with lem-hbd-match bd1 | lem-hbd-match bd2
    ... | bd1' , bdpre1 , bdr1 , bdpost1 |
          bd2' , bdpre2 , bdr2 , bdpost2 =
      HBDAp bd1' bd2' ,
      HBDAp bdpre1 bdpre2 ,
      HBDAp bdr1 bdr2 ,
      HBDAp bdpost1 bdpost2 
    lem-hbd-match (HBDInl bd)
      with lem-hbd-match bd
    ... | bd' , bdpre , bdr , bdpost =
      HBDInl bd' , HBDInl bdpre , HBDInl bdr , HBDInl bdpost
    lem-hbd-match (HBDInr bd)
      with lem-hbd-match bd
    ... | bd' , bdpre , bdr , bdpost =
      HBDInr bd' , HBDInr bdpre , HBDInr bdr , HBDInr bdpost
    lem-hbd-match (HBDMatch bd (HBDZRules bdpre bdpost))
      with lem-hbd-match bd |
           lem-hbd-rs-match bdpre |
           lem-hbd-rs-match bdpost
    ... | bd' , bdpre , bdr , bdpost
        | bdpre' , bdprepre , bdprer , bdprepost
        | bdpost' , bdpostpre , bdpostr , bdpostpost =
      HBDMatch bd' (HBDZRules bdpre' bdpost') ,
      HBDMatch bdpre (HBDZRules bdprepre bdpostpre) ,
      HBDMatch bdr (HBDZRules bdprer bdpostr) ,
      HBDMatch bdpost (HBDZRules bdprepost bdpostpost)
    lem-hbd-match (HBDPair bd1 bd2)
      with lem-hbd-match bd1 | lem-hbd-match bd2
    ... | bd1' , bdpre1 , bdr1 , bdpost1 |
          bd2' , bdpre2 , bdr2 , bdpost2 =
      HBDPair bd1' bd2' ,
      HBDPair bdpre1 bdpre2 ,
      HBDPair bdr1 bdr2 ,
      HBDPair bdpost1 bdpost2 
    lem-hbd-match (HBDFst bd)
      with lem-hbd-match bd
    ... | bd' , bdpre , bdr , bdpost =
      HBDFst bd' , HBDFst bdpre , HBDFst bdr , HBDFst bdpost
    lem-hbd-match (HBDSnd bd)
      with lem-hbd-match bd
    ... | bd' , bdpre , bdr , bdpost =
      HBDSnd bd' , HBDSnd bdpre , HBDSnd bdr , HBDSnd bdpost
    lem-hbd-match (HBDEHole bdσ)
      with lem-hbd-σ-match bdσ
    ... | bdσ' , bdσpre , bdσr , bdσpost =
      HBDEHole bdσ' ,
      HBDEHole bdσpre ,
      HBDEHole bdσr ,
      HBDEHole bdσpost
    lem-hbd-match (HBDHole bdσ bd)
      with lem-hbd-σ-match bdσ | lem-hbd-match bd
    ... | bdσ' , bdσpre , bdσr , bdσpost
        | bd' , bdpre , bdr , bdpost =
      HBDHole bdσ' bd' ,
      HBDHole bdσpre bdpre ,
      HBDHole bdσr bdr ,
      HBDHole bdσpost bdpost

    lem-hbd-σ-match : {σ : subst-env} {e1 : ihexp} {τ : htyp}
                      {rs-pre : rules} {r : rule} {rs-post : rules} →
                      hole-binders-disjoint-σ σ
                        (match e1 ·: τ of (rs-pre / r / rs-post)) →
                      hole-binders-disjoint-σ σ e1 ×
                        hole-binders-disjoint-σ σ rs-pre ×
                          hole-binders-disjoint-σ σ r ×
                            hole-binders-disjoint-σ σ rs-post
    lem-hbd-σ-match HBDσId = HBDσId , HBDσId , HBDσId , HBDσId
    lem-hbd-σ-match (HBDσSubst bd bdσ)
      with lem-hbd-match bd | lem-hbd-σ-match bdσ
    ... | bd' , bdpre , bdr , bdpost
        | bdσ' , bdσpre , bdσr , bdσpost =
      HBDσSubst bd' bdσ' ,
      HBDσSubst bdpre bdσpre ,
      HBDσSubst bdr bdσr ,
      HBDσSubst bdpost bdσpost

    lem-hbd-rs-match : {rs : rules} {e1 : ihexp} {τ : htyp}
                       {rs-pre : rules} {r : rule} {rs-post : rules} →
                       hole-binders-disjoint-rs rs
                         (match e1 ·: τ of (rs-pre / r / rs-post)) →
                       hole-binders-disjoint-rs rs e1 ×
                         hole-binders-disjoint-rs rs rs-pre ×
                           hole-binders-disjoint-rs rs r ×
                             hole-binders-disjoint-rs rs rs-post
    lem-hbd-rs-match HBDNoRules =
      HBDNoRules , HBDNoRules , HBDNoRules , HBDNoRules 
    lem-hbd-rs-match (HBDRules bdr bdrs)
      with lem-hbd-r-match bdr | lem-hbd-rs-match bdrs
    ... | bdr' , bdrpre , bdrr , bdrpost
        | bdrs' , bdrspre , bdrsr , bdrspost =
      HBDRules bdr' bdrs' ,
      HBDRules bdrpre bdrspre ,
      HBDRules bdrr bdrsr ,
      HBDRules bdrpost bdrspost

    lem-hbd-r-match : {r : rule} {e1 : ihexp} {τ : htyp}
                      {rs-pre : rules} {r1 : rule} {rs-post : rules} →
                      hole-binders-disjoint-r r
                        (match e1 ·: τ of (rs-pre / r1 / rs-post)) →
                      hole-binders-disjoint-r r e1 ×
                        hole-binders-disjoint-r r rs-pre ×
                          hole-binders-disjoint-r r r1 ×
                            hole-binders-disjoint-r r rs-post
    lem-hbd-r-match (HBDRule bdp bd)
      with lem-hbd-p-match bdp | lem-hbd-match bd
    ... | bdp' , bdppre , bdpr , bdppost
        | bd' , bdpre , bdr , bdpost =
      HBDRule bdp' bd' ,
      HBDRule bdppre bdpre ,
      HBDRule bdpr bdr ,
      HBDRule bdppost bdpost
  
    lem-hbd-p-match : {p : pattrn} {e1 : ihexp} {τ : htyp}
                      {rs-pre : rules} {r1 : rule} {rs-post : rules} →
                      hole-binders-disjoint-p p
                        (match e1 ·: τ of (rs-pre / r1 / rs-post)) →
                      hole-binders-disjoint-p p e1 ×
                        hole-binders-disjoint-p p rs-pre ×
                          hole-binders-disjoint-p p r1 ×
                            hole-binders-disjoint-p p rs-post
    lem-hbd-p-match HBDPUnit = HBDPUnit , HBDPUnit , HBDPUnit , HBDPUnit
    lem-hbd-p-match HBDPNum = HBDPNum , HBDPNum , HBDPNum , HBDPNum
    lem-hbd-p-match HBDPVar =
      HBDPVar , HBDPVar , HBDPVar , HBDPVar
    lem-hbd-p-match (HBDPInl bd)
      with lem-hbd-p-match bd
    ... | bd' , bdpre , bdr , bdpost =
      HBDPInl bd' , HBDPInl bdpre , HBDPInl bdr , HBDPInl bdpost
    lem-hbd-p-match (HBDPInr bd)
      with lem-hbd-p-match bd
    ... | bd' , bdpre , bdr , bdpost =
      HBDPInr bd' , HBDPInr bdpre , HBDPInr bdr , HBDPInr bdpost
    lem-hbd-p-match (HBDPPair bd1 bd2)
      with lem-hbd-p-match bd1 | lem-hbd-p-match bd2
    ... | bd1' , bdpre1 , bdr1 , bdpost1
        | bd2' , bdpre2 , bdr2 , bdpost2 =
      HBDPPair bd1' bd2' ,
      HBDPPair bdpre1 bdpre2 ,
      HBDPPair bdr1 bdr2 ,
      HBDPPair bdpost1 bdpost2
    lem-hbd-p-match HBDPWild =
      HBDPWild , HBDPWild , HBDPWild , HBDPWild
    lem-hbd-p-match (HBDPEHole
                      (HUBMatch ub
                        (HUBZRules ubpre (HUBRules ubr ubpost)))) =
      HBDPEHole ub , HBDPEHole ubpre , HBDPEHole ubr , HBDPEHole ubpost
    lem-hbd-p-match (HBDPHole
                      (HUBMatch ub
                        (HUBZRules ubpre (HUBRules ubr ubpost))) bd)
      with lem-hbd-p-match bd
    ... | bd' , bdpre , bdr , bdpost =
      HBDPHole ub bd' , HBDPHole ubpre bdpre ,
      HBDPHole ubr bdr , HBDPHole ubpost bdpost
    
  mutual
    lem-hbd-pair : {e : ihexp} {e1 e2 : ihexp} →
                   hole-binders-disjoint e ⟨ e1 , e2 ⟩ →
                   (hole-binders-disjoint e e1) ×
                     (hole-binders-disjoint e e2)
    lem-hbd-pair HBDUnit = HBDUnit , HBDUnit
    lem-hbd-pair HBDNum = HBDNum , HBDNum
    lem-hbd-pair HBDVar = HBDVar , HBDVar
    lem-hbd-pair (HBDLam bd)
      with lem-hbd-pair bd
    ... | bd1 , bd2 = HBDLam bd1 , HBDLam bd2
    lem-hbd-pair (HBDAp bd1 bd2)
      with lem-hbd-pair bd1 | lem-hbd-pair bd2
    ... | bd1₁ , bd1₂ | bd2₁ , bd2₂ =
      HBDAp bd1₁ bd2₁ , HBDAp bd1₂ bd2₂
    lem-hbd-pair (HBDInl bd)
      with lem-hbd-pair bd
    ... | bd1 , bd2 = HBDInl bd1 , HBDInl bd2
    lem-hbd-pair (HBDInr bd)
      with lem-hbd-pair bd
    ... | bd1 , bd2 = HBDInr bd1 , HBDInr bd2
    lem-hbd-pair (HBDMatch bd (HBDZRules bdpre bdpost))
      with lem-hbd-pair bd |
           lem-hbd-rs-pair bdpre |
           lem-hbd-rs-pair bdpost
    ... | bd1 , bd2
        | bdpre1 , bdpre2
        | bdpost1 , bdpost2 =
      HBDMatch bd1 (HBDZRules bdpre1 bdpost1) ,
      HBDMatch bd2 (HBDZRules bdpre2 bdpost2)
    lem-hbd-pair (HBDPair bd1 bd2)
      with lem-hbd-pair bd1 | lem-hbd-pair bd2
    ... | bd1₁ , bd1₂ | bd2₁ , bd2₂ =
      HBDPair bd1₁ bd2₁ , HBDPair bd1₂ bd2₂
    lem-hbd-pair (HBDFst bd)
      with lem-hbd-pair bd
    ... | bd1 , bd2 = HBDFst bd1 , HBDFst bd2
    lem-hbd-pair (HBDSnd bd)
      with lem-hbd-pair bd
    ... | bd1 , bd2 = HBDSnd bd1 , HBDSnd bd2
    lem-hbd-pair (HBDEHole bdσ)
      with lem-hbd-σ-pair bdσ
    ... | bdσ1 , bdσ2 =
      HBDEHole bdσ1 , HBDEHole bdσ2
    lem-hbd-pair (HBDHole bdσ bd)
      with lem-hbd-σ-pair bdσ | lem-hbd-pair bd
    ... | bdσ1 , bdσ2 | bd1 , bd2 =
      HBDHole bdσ1 bd1 , HBDHole bdσ2 bd2

    lem-hbd-σ-pair : {σ : subst-env} {e1 e2 : ihexp} →
                     hole-binders-disjoint-σ σ ⟨ e1 , e2 ⟩ →
                     hole-binders-disjoint-σ σ e1 ×
                       hole-binders-disjoint-σ σ e2
    lem-hbd-σ-pair HBDσId =
      HBDσId , HBDσId
    lem-hbd-σ-pair (HBDσSubst bd bdσ)
      with lem-hbd-σ-pair bdσ | lem-hbd-pair bd
    ... | bdσ1 , bdσ2 | bd1 , bd2 =
      HBDσSubst bd1 bdσ1 , HBDσSubst bd2 bdσ2
      
    lem-hbd-rs-pair : {rs : rules} {e1 e2 : ihexp} →
                      hole-binders-disjoint-rs rs ⟨ e1 , e2 ⟩ →
                      (hole-binders-disjoint-rs rs e1) ×
                        (hole-binders-disjoint-rs rs e2)
    lem-hbd-rs-pair HBDNoRules = HBDNoRules , HBDNoRules
    lem-hbd-rs-pair (HBDRules bdr bdrs)
      with lem-hbd-r-pair bdr | lem-hbd-rs-pair bdrs
    ... | bdr1 , bdr2 | bdrs1 , bdrs2 =
      HBDRules bdr1 bdrs1 , HBDRules bdr2 bdrs2

    lem-hbd-r-pair : {r : rule} {e1 e2 : ihexp} →
                     hole-binders-disjoint-r r ⟨ e1 , e2 ⟩ →
                     (hole-binders-disjoint-r r e1) ×
                       (hole-binders-disjoint-r r e2)
    lem-hbd-r-pair (HBDRule bdp bd)
      with lem-hbd-p-pair bdp | lem-hbd-pair bd
    ... | bdp' , ubp | bd' , ub =
      HBDRule bdp' bd' , HBDRule ubp ub

    lem-hbd-p-pair : {p : pattrn} {e1 e2 : ihexp} →
                     hole-binders-disjoint-p p ⟨ e1 , e2 ⟩ →
                     (hole-binders-disjoint-p p e1) ×
                       (hole-binders-disjoint-p p e2)
    lem-hbd-p-pair HBDPUnit = HBDPUnit , HBDPUnit
    lem-hbd-p-pair HBDPNum = HBDPNum , HBDPNum
    lem-hbd-p-pair HBDPVar = HBDPVar , HBDPVar
    lem-hbd-p-pair (HBDPInl bd)
      with lem-hbd-p-pair bd
    ... | bd1 , bd2 = HBDPInl bd1 , HBDPInl bd2
    lem-hbd-p-pair (HBDPInr bd)
      with lem-hbd-p-pair bd
    ... | bd1 , bd2 = HBDPInr bd1 , HBDPInr bd2
    lem-hbd-p-pair (HBDPPair bd1 bd2)
      with lem-hbd-p-pair bd1 | lem-hbd-p-pair bd2
    ... | bd1₁ , bd1₂ | bd2₁ , bd2₂ =
      HBDPPair bd1₁ bd2₁ , HBDPPair bd1₂ bd2₂
    lem-hbd-p-pair HBDPWild = HBDPWild , HBDPWild
    lem-hbd-p-pair (HBDPEHole (HUBPair ub1 ub2))=
      HBDPEHole ub1 , HBDPEHole ub2
    lem-hbd-p-pair (HBDPHole (HUBPair ub1 ub2) bd)
      with lem-hbd-p-pair bd
    ... | bd1 , bd2 = HBDPHole ub1 bd1 , HBDPHole ub2 bd2
    
  mutual
    lem-hbd-fst : {e : ihexp} {e1 : ihexp} →
                  hole-binders-disjoint e (fst e1) →
                  hole-binders-disjoint e e1
    lem-hbd-fst HBDUnit = HBDUnit
    lem-hbd-fst HBDNum = HBDNum
    lem-hbd-fst HBDVar = HBDVar
    lem-hbd-fst (HBDLam bd) = HBDLam (lem-hbd-fst bd)
    lem-hbd-fst (HBDAp bd1 bd2) =
      HBDAp (lem-hbd-fst bd1) (lem-hbd-fst bd2)
    lem-hbd-fst (HBDInl bd) = HBDInl (lem-hbd-fst bd)
    lem-hbd-fst (HBDInr bd) = HBDInr (lem-hbd-fst bd)
    lem-hbd-fst (HBDMatch bd (HBDZRules bdpre bdpost)) =
      HBDMatch (lem-hbd-fst bd)
               (HBDZRules (lem-hbd-rs-fst bdpre)
                          (lem-hbd-rs-fst bdpost))
    lem-hbd-fst (HBDPair bd1 bd2) =
      HBDPair (lem-hbd-fst bd1) (lem-hbd-fst bd2)
    lem-hbd-fst (HBDFst bd) = HBDFst (lem-hbd-fst bd)
    lem-hbd-fst (HBDSnd bd) = HBDSnd (lem-hbd-fst bd)
    lem-hbd-fst (HBDEHole bdσ) = HBDEHole (lem-hbd-σ-fst bdσ)
    lem-hbd-fst (HBDHole bdσ bd) =
      HBDHole (lem-hbd-σ-fst bdσ) (lem-hbd-fst bd)

    lem-hbd-σ-fst : {σ : subst-env} {e1 : ihexp} →
                   hole-binders-disjoint-σ σ (fst e1) →
                   hole-binders-disjoint-σ σ e1
    lem-hbd-σ-fst HBDσId = HBDσId
    lem-hbd-σ-fst (HBDσSubst bd bdσ) =
      HBDσSubst (lem-hbd-fst bd) (lem-hbd-σ-fst bdσ)
      
    lem-hbd-rs-fst : {rs : rules} {e1 : ihexp} →
                     hole-binders-disjoint-rs rs (fst e1) →
                     hole-binders-disjoint-rs rs e1
    lem-hbd-rs-fst HBDNoRules = HBDNoRules
    lem-hbd-rs-fst (HBDRules bdr bdrs) =
      HBDRules (lem-hbd-r-fst bdr) (lem-hbd-rs-fst bdrs)

    lem-hbd-r-fst : {r : rule} {e1 : ihexp} →
                    hole-binders-disjoint-r r (fst e1) →
                    hole-binders-disjoint-r r e1
    lem-hbd-r-fst (HBDRule bdp bd) =
      HBDRule (lem-hbd-p-fst bdp) (lem-hbd-fst bd)

    lem-hbd-p-fst : {p : pattrn} {e1 : ihexp} →
                    hole-binders-disjoint-p p (fst e1) →
                    hole-binders-disjoint-p p e1
    lem-hbd-p-fst HBDPUnit = HBDPUnit
    lem-hbd-p-fst HBDPNum = HBDPNum
    lem-hbd-p-fst HBDPVar = HBDPVar
    lem-hbd-p-fst (HBDPInl bd) = HBDPInl (lem-hbd-p-fst bd)
    lem-hbd-p-fst (HBDPInr bd) = HBDPInr (lem-hbd-p-fst bd)
    lem-hbd-p-fst (HBDPPair bd1 bd2) =
      HBDPPair (lem-hbd-p-fst bd1) (lem-hbd-p-fst bd2)
    lem-hbd-p-fst HBDPWild = HBDPWild
    lem-hbd-p-fst (HBDPEHole (HUBFst ub)) = HBDPEHole ub
    lem-hbd-p-fst (HBDPHole (HUBFst ub) bd) =
      HBDPHole ub (lem-hbd-p-fst bd)
    
  mutual
    lem-hbd-snd : {e : ihexp} {e1 : ihexp} →
                  hole-binders-disjoint e (snd e1) →
                  hole-binders-disjoint e e1
    lem-hbd-snd HBDUnit = HBDUnit
    lem-hbd-snd HBDNum = HBDNum
    lem-hbd-snd HBDVar = HBDVar
    lem-hbd-snd (HBDLam bd) = HBDLam (lem-hbd-snd bd)
    lem-hbd-snd (HBDAp bd1 bd2) =
      HBDAp (lem-hbd-snd bd1) (lem-hbd-snd bd2)
    lem-hbd-snd (HBDInl bd) = HBDInl (lem-hbd-snd bd)
    lem-hbd-snd (HBDInr bd) = HBDInr (lem-hbd-snd bd)
    lem-hbd-snd (HBDMatch bd (HBDZRules bdpre bdpost)) =
      HBDMatch (lem-hbd-snd bd)
              (HBDZRules (lem-hbd-rs-snd bdpre)
                        (lem-hbd-rs-snd bdpost))
    lem-hbd-snd (HBDPair bd1 bd2) =
      HBDPair (lem-hbd-snd bd1) (lem-hbd-snd bd2)
    lem-hbd-snd (HBDFst bd) = HBDFst (lem-hbd-snd bd)
    lem-hbd-snd (HBDSnd bd) = HBDSnd (lem-hbd-snd bd)
    lem-hbd-snd (HBDEHole bdσ) = HBDEHole (lem-hbd-σ-snd bdσ)
    lem-hbd-snd (HBDHole bdσ bd) =
      HBDHole (lem-hbd-σ-snd bdσ) (lem-hbd-snd bd)

    lem-hbd-σ-snd : {σ : subst-env} {e1 : ihexp} →
                    hole-binders-disjoint-σ σ (snd e1) →
                    hole-binders-disjoint-σ σ e1
    lem-hbd-σ-snd HBDσId = HBDσId
    lem-hbd-σ-snd (HBDσSubst bd bdσ) =
      HBDσSubst (lem-hbd-snd bd) (lem-hbd-σ-snd bdσ)
      
    lem-hbd-rs-snd : {rs : rules} {e1 : ihexp} →
                     hole-binders-disjoint-rs rs (snd e1) →
                     hole-binders-disjoint-rs rs e1
    lem-hbd-rs-snd HBDNoRules = HBDNoRules
    lem-hbd-rs-snd (HBDRules bdr bdrs) =
      HBDRules (lem-hbd-r-snd bdr) (lem-hbd-rs-snd bdrs)

    lem-hbd-r-snd : {r : rule} {e1 : ihexp} →
                    hole-binders-disjoint-r r (snd e1) →
                    hole-binders-disjoint-r r e1
    lem-hbd-r-snd (HBDRule bdp bd) =
      HBDRule (lem-hbd-p-snd bdp) (lem-hbd-snd bd)

    lem-hbd-p-snd : {p : pattrn} {e1 : ihexp} →
                    hole-binders-disjoint-p p (snd e1) →
                    hole-binders-disjoint-p p e1
    lem-hbd-p-snd HBDPUnit = HBDPUnit
    lem-hbd-p-snd HBDPNum = HBDPNum
    lem-hbd-p-snd HBDPVar = HBDPVar
    lem-hbd-p-snd (HBDPInl bd) = HBDPInl (lem-hbd-p-snd bd)
    lem-hbd-p-snd (HBDPInr bd) = HBDPInr (lem-hbd-p-snd bd)
    lem-hbd-p-snd (HBDPPair bd1 bd2) =
      HBDPPair (lem-hbd-p-snd bd1) (lem-hbd-p-snd bd2)
    lem-hbd-p-snd HBDPWild = HBDPWild
    lem-hbd-p-snd (HBDPEHole (HUBSnd ub)) = HBDPEHole ub
    lem-hbd-p-snd (HBDPHole (HUBSnd ub) bd) =
      HBDPHole ub (lem-hbd-p-snd bd)

  mutual
    lem-hbd-ehole : {e : ihexp} {u : Nat} {σ : subst-env} →
                    hole-binders-disjoint e ⦇-⦈⟨ u , σ ⟩ →
                    hole-binders-disjoint e σ
    lem-hbd-ehole HBDUnit = HBDUnit
    lem-hbd-ehole HBDNum = HBDNum
    lem-hbd-ehole HBDVar = HBDVar
    lem-hbd-ehole (HBDLam bd) =
      HBDLam (lem-hbd-ehole bd)
    lem-hbd-ehole (HBDAp bd1 bd2) =
      HBDAp (lem-hbd-ehole bd1) (lem-hbd-ehole bd2)
    lem-hbd-ehole (HBDInl bd) = HBDInl (lem-hbd-ehole bd)
    lem-hbd-ehole (HBDInr bd) = HBDInr (lem-hbd-ehole bd)
    lem-hbd-ehole (HBDMatch bd (HBDZRules bdpre bdpost)) =
      HBDMatch (lem-hbd-ehole bd)
              (HBDZRules (lem-hbd-rs-ehole bdpre)
                        (lem-hbd-rs-ehole bdpost))
    lem-hbd-ehole (HBDPair bd1 bd2) =
      HBDPair (lem-hbd-ehole bd1)
             (lem-hbd-ehole bd2)
    lem-hbd-ehole (HBDFst bd) = HBDFst (lem-hbd-ehole bd)
    lem-hbd-ehole (HBDSnd bd) = HBDSnd (lem-hbd-ehole bd)
    lem-hbd-ehole (HBDEHole bdσ) = HBDEHole (lem-hbd-σ-ehole bdσ)
    lem-hbd-ehole (HBDHole bdσ bd) =
      HBDHole (lem-hbd-σ-ehole bdσ)
               (lem-hbd-ehole bd)

    lem-hbd-σ-ehole : {σ : subst-env} {u : Nat} {σ1 : subst-env} →
                      hole-binders-disjoint-σ σ ⦇-⦈⟨ u , σ1 ⟩ →
                      hole-binders-disjoint-σ σ σ1
    lem-hbd-σ-ehole HBDσId = HBDσId
    lem-hbd-σ-ehole (HBDσSubst bd bdσ) =
      HBDσSubst (lem-hbd-ehole bd) (lem-hbd-σ-ehole bdσ)

    lem-hbd-rs-ehole : {rs : rules} {u : Nat} {σ : subst-env} →
                       hole-binders-disjoint-rs rs ⦇-⦈⟨ u , σ ⟩ →
                       hole-binders-disjoint-rs rs σ
    lem-hbd-rs-ehole HBDNoRules = HBDNoRules
    lem-hbd-rs-ehole (HBDRules bdr bdrs) =
      HBDRules (lem-hbd-r-ehole bdr) (lem-hbd-rs-ehole bdrs)

    lem-hbd-r-ehole : {r : rule} {u : Nat} {σ : subst-env} →
                      hole-binders-disjoint-r r ⦇-⦈⟨ u , σ ⟩ →
                      hole-binders-disjoint-r r σ
    lem-hbd-r-ehole (HBDRule bdp bde) =
      HBDRule (lem-hbd-p-ehole bdp) (lem-hbd-ehole bde)
    
    lem-hbd-p-ehole : {p : pattrn} {u : Nat} {σ : subst-env} →
                      hole-binders-disjoint-p p ⦇-⦈⟨ u , σ ⟩ →
                      hole-binders-disjoint-p p σ
    lem-hbd-p-ehole HBDPUnit = HBDPUnit
    lem-hbd-p-ehole HBDPNum = HBDPNum
    lem-hbd-p-ehole HBDPVar = HBDPVar
    lem-hbd-p-ehole (HBDPInl bd) = HBDPInl (lem-hbd-p-ehole bd)
    lem-hbd-p-ehole (HBDPInr bd) = HBDPInr (lem-hbd-p-ehole bd)
    lem-hbd-p-ehole (HBDPPair bd1 bd2) =
      HBDPPair (lem-hbd-p-ehole bd1) (lem-hbd-p-ehole bd2)
    lem-hbd-p-ehole HBDPWild = HBDPWild
    lem-hbd-p-ehole (HBDPEHole (HUBEHole ubσ)) =
      HBDPEHole ubσ
    lem-hbd-p-ehole (HBDPHole (HUBEHole ubσ) bd) =
      HBDPHole ubσ (lem-hbd-p-ehole bd)
      
  mutual
    lem-hbd-hole : {e : ihexp} {e1 : ihexp} {u : Nat} {σ : subst-env} →
                     hole-binders-disjoint e ⦇⌜ e1 ⌟⦈⟨ u , σ ⟩ →
                     hole-binders-disjoint e σ ×
                       hole-binders-disjoint e e1
    lem-hbd-hole HBDUnit = HBDUnit , HBDUnit
    lem-hbd-hole HBDNum = HBDNum , HBDNum
    lem-hbd-hole HBDVar = HBDVar , HBDVar
    lem-hbd-hole (HBDLam bd)
      with lem-hbd-hole bd
    ... | bdσ ,  bd' =
      HBDLam bdσ , HBDLam bd' 
    lem-hbd-hole (HBDAp bd1 bd2)
      with lem-hbd-hole bd1 | lem-hbd-hole bd2
    ... | bd1σ  , bd1' | bd2σ , bd2' =
      HBDAp bd1σ bd2σ , HBDAp bd1' bd2'
    lem-hbd-hole (HBDInl bd)
      with lem-hbd-hole bd
    ... |  bdσ , bd' =
      HBDInl bdσ , HBDInl bd'
    lem-hbd-hole (HBDInr bd)
      with lem-hbd-hole bd
    ... | bdσ , bd'  =
       HBDInr bdσ , HBDInr bd'
    lem-hbd-hole (HBDMatch bd (HBDZRules bdpre bdpost))
      with lem-hbd-hole bd |
           lem-hbd-rs-hole bdpre |
           lem-hbd-rs-hole bdpost
    ... | bdσ , bd'
        | bdpreσ , bdpre'
        | bdpostσ , bdpost' =
      HBDMatch bdσ (HBDZRules bdpreσ bdpostσ) ,
      HBDMatch bd' (HBDZRules bdpre' bdpost')
    lem-hbd-hole (HBDPair bd1 bd2)
      with lem-hbd-hole bd1 | lem-hbd-hole bd2
    ... | bdσ1 , bd1' | bdσ2 , bd2' =
      HBDPair bdσ1 bdσ2 , HBDPair bd1' bd2' 
    lem-hbd-hole (HBDFst bd)
      with lem-hbd-hole bd
    ... | bdσ , bd' = HBDFst bdσ , HBDFst bd'
    lem-hbd-hole (HBDSnd bd)
      with lem-hbd-hole bd
    ... | bdσ , bd' = HBDSnd bdσ , HBDSnd bd' 
    lem-hbd-hole (HBDEHole bdσ)
      with lem-hbd-σ-hole bdσ
    ... | bdσσ , bdσ' =
       HBDEHole bdσσ , HBDEHole bdσ'
    lem-hbd-hole (HBDHole bdσ bde)
      with lem-hbd-σ-hole bdσ | lem-hbd-hole bde
    ... | bdσσ , bdσ' | bdeσ , bde' =
      HBDHole bdσσ bdeσ , HBDHole bdσ' bde'

    lem-hbd-σ-hole : {σ : subst-env} {e1 : ihexp} {u : Nat} {σ1 : subst-env} →
                       hole-binders-disjoint-σ σ ⦇⌜ e1 ⌟⦈⟨ u , σ1 ⟩ →
                       hole-binders-disjoint-σ σ σ1 ×
                         hole-binders-disjoint-σ σ e1 
    lem-hbd-σ-hole HBDσId = HBDσId , HBDσId
    lem-hbd-σ-hole (HBDσSubst bdd bdσ)
      with lem-hbd-hole bdd | lem-hbd-σ-hole bdσ
    ... | bddσ , bdd' | bdσσ , bdσ' =
      HBDσSubst bddσ bdσσ , HBDσSubst bdd' bdσ'

    lem-hbd-rs-hole : {rs : rules} {e1 : ihexp} {u : Nat} {σ : subst-env} →
                        hole-binders-disjoint-rs rs ⦇⌜ e1 ⌟⦈⟨ u , σ ⟩ →
                        hole-binders-disjoint-rs rs σ ×
                          hole-binders-disjoint-rs rs e1
    lem-hbd-rs-hole HBDNoRules = HBDNoRules , HBDNoRules
    lem-hbd-rs-hole (HBDRules bdr bdrs)
      with lem-hbd-r-hole bdr | lem-hbd-rs-hole bdrs
    ... | bdrσ , bdr' | bdrsσ , bdrs' =
      HBDRules bdrσ bdrsσ , HBDRules bdr' bdrs'

    lem-hbd-r-hole : {r : rule} {e1 : ihexp} {u : Nat} {σ : subst-env} →
                       hole-binders-disjoint-r r ⦇⌜ e1 ⌟⦈⟨ u , σ ⟩ →
                       hole-binders-disjoint-r r σ ×
                         hole-binders-disjoint-r r e1
    lem-hbd-r-hole (HBDRule bdp bde)
      with lem-hbd-p-hole bdp | lem-hbd-hole bde
    ... | bdpσ , bdp' | bdeσ , bde' =
      HBDRule bdpσ bdeσ , HBDRule bdp' bde'
    
    lem-hbd-p-hole : {p : pattrn} {e1 : ihexp} {u : Nat} {σ : subst-env} →
                       hole-binders-disjoint-p p ⦇⌜ e1 ⌟⦈⟨ u , σ ⟩ →
                       hole-binders-disjoint-p p σ ×
                         hole-binders-disjoint-p p e1
    lem-hbd-p-hole HBDPUnit = HBDPUnit , HBDPUnit
    lem-hbd-p-hole HBDPNum = HBDPNum , HBDPNum
    lem-hbd-p-hole HBDPVar = HBDPVar , HBDPVar
    lem-hbd-p-hole (HBDPInl bd)
      with lem-hbd-p-hole bd
    ... | bdσ , bd' =
      HBDPInl bdσ , HBDPInl bd'
    lem-hbd-p-hole (HBDPInr bd)
      with lem-hbd-p-hole bd
    ... | bdσ , bd' =
      HBDPInr bdσ , HBDPInr bd'
    lem-hbd-p-hole (HBDPPair bd1 bd2)
      with lem-hbd-p-hole bd1 |
           lem-hbd-p-hole bd2
    ... | bdσ1 , bd1' | bdσ2 , bd2' =
      HBDPPair bdσ1 bdσ2 , HBDPPair bd1' bd2'
    lem-hbd-p-hole HBDPWild = HBDPWild , HBDPWild
    lem-hbd-p-hole (HBDPEHole (HUBHole ubσ ub)) =
      HBDPEHole ubσ , HBDPEHole ub
    lem-hbd-p-hole (HBDPHole (HUBHole ubσ ub) bd)
      with lem-hbd-p-hole bd
    ... | bdσ ,  bd' =
      HBDPHole ubσ bdσ , HBDPHole ub bd'

  mutual
    lem-σ-hbd-subst : {e : ihexp} {d : ihexp} {y : Nat} {σ : subst-env} →
                      hole-binders-disjoint e (Subst d y σ) →
                      hole-binders-disjoint e d ×
                        hole-binders-disjoint e σ
    lem-σ-hbd-subst HBDUnit = HBDUnit , HBDUnit
    lem-σ-hbd-subst HBDNum = HBDNum , HBDNum
    lem-σ-hbd-subst HBDVar = HBDVar , HBDVar
    lem-σ-hbd-subst (HBDLam bd)
      with lem-σ-hbd-subst bd
    ... | bd' , bdσ =
      HBDLam bd' , HBDLam bdσ
    lem-σ-hbd-subst (HBDAp bd1 bd2)
      with lem-σ-hbd-subst bd1 | lem-σ-hbd-subst bd2
    ... | bd1' , bdσ1 | bd2' , bdσ2 =
      HBDAp bd1' bd2' ,  HBDAp bdσ1 bdσ2
    lem-σ-hbd-subst (HBDInl bd)
      with lem-σ-hbd-subst bd
    ... | bd' , bdσ =
      HBDInl bd' , HBDInl bdσ
    lem-σ-hbd-subst (HBDInr bd)
      with lem-σ-hbd-subst bd
    ... | bd' , bdσ =
      HBDInr bd' , HBDInr bdσ
    lem-σ-hbd-subst (HBDMatch bd (HBDZRules bdpre bdpost))
      with lem-σ-hbd-subst bd |
           lem-σ-hbd-rs-subst bdpre |
           lem-σ-hbd-rs-subst bdpost
    ... | bd' , bdσ
        | bdpre' , bdpreσ
        | bdpost' , bdpostσ =
      HBDMatch bd' (HBDZRules bdpre' bdpost') ,
      HBDMatch bdσ (HBDZRules bdpreσ bdpostσ)
    lem-σ-hbd-subst (HBDPair bd1 bd2)
      with lem-σ-hbd-subst bd1 | lem-σ-hbd-subst bd2
    ... | bd1' , bdσ1 | bd2' , bdσ2 =
      HBDPair bd1' bd2' , HBDPair bdσ1 bdσ2
    lem-σ-hbd-subst (HBDFst bd)
      with lem-σ-hbd-subst bd
    ... | bd' , bdσ =
      HBDFst bd' , HBDFst bdσ
    lem-σ-hbd-subst (HBDSnd bd)
      with lem-σ-hbd-subst bd
    ... | bd' , bdσ =
      HBDSnd bd' , HBDSnd bdσ
    lem-σ-hbd-subst (HBDEHole bdσ)
      with lem-σ-hbd-σ-subst bdσ
    ... | bdσ' , bdσσ =
      HBDEHole bdσ' , HBDEHole bdσσ
    lem-σ-hbd-subst (HBDHole bdσ bde)
      with lem-σ-hbd-σ-subst bdσ | lem-σ-hbd-subst bde
    ... | bdσ' , bdσσ | bde' , bdeσ =
      HBDHole bdσ' bde' , HBDHole bdσσ bdeσ

    lem-σ-hbd-σ-subst : {σ : subst-env} {d : ihexp} {y : Nat} {σ1 : subst-env} →
                        hole-binders-disjoint-σ σ (Subst d y σ1) →
                        hole-binders-disjoint-σ σ d ×
                          hole-binders-disjoint-σ σ σ1
    lem-σ-hbd-σ-subst HBDσId = HBDσId , HBDσId
    lem-σ-hbd-σ-subst (HBDσSubst bdd bdσ)
      with lem-σ-hbd-subst bdd | lem-σ-hbd-σ-subst bdσ
    ... | bdd' , bddσ | bdσ' , bdσσ =
      HBDσSubst bdd' bdσ' , HBDσSubst bddσ bdσσ

    lem-σ-hbd-rs-subst : {rs : rules} {d : ihexp} {y : Nat} {σ : subst-env} →
                         hole-binders-disjoint-rs rs (Subst d y σ) →
                         hole-binders-disjoint-rs rs d ×
                           hole-binders-disjoint-rs rs σ
    lem-σ-hbd-rs-subst HBDNoRules = HBDNoRules , HBDNoRules
    lem-σ-hbd-rs-subst (HBDRules bdr bdrs)
      with lem-σ-hbd-r-subst bdr | lem-σ-hbd-rs-subst bdrs
    ... | bdr' , bdrσ | bdrs' , bdrsσ =
      HBDRules bdr' bdrs' , HBDRules bdrσ bdrsσ

    lem-σ-hbd-r-subst : {r : rule} {d : ihexp} {y : Nat} {σ : subst-env} →
                        hole-binders-disjoint-r r (Subst d y σ) →
                        hole-binders-disjoint-r r d ×
                          hole-binders-disjoint-r r σ
    lem-σ-hbd-r-subst (HBDRule bdp bd)
      with lem-σ-hbd-p-subst bdp | lem-σ-hbd-subst bd
    ... | bdp' , bdpσ | bd' , bdσ =
      HBDRule bdp' bd' , HBDRule bdpσ bdσ

    lem-σ-hbd-p-subst : {p : pattrn} {d : ihexp} {y : Nat} {σ : subst-env} →
                        hole-binders-disjoint-p p (Subst d y σ) →
                        hole-binders-disjoint-p p d ×
                          hole-binders-disjoint-p p σ
    lem-σ-hbd-p-subst HBDPUnit = HBDPUnit , HBDPUnit
    lem-σ-hbd-p-subst HBDPNum = HBDPNum , HBDPNum
    lem-σ-hbd-p-subst HBDPVar = HBDPVar , HBDPVar 
    lem-σ-hbd-p-subst (HBDPInl bd)
      with lem-σ-hbd-p-subst bd
    ... | bd' , bdσ =
      HBDPInl bd' , HBDPInl bdσ
    lem-σ-hbd-p-subst (HBDPInr bd)
      with lem-σ-hbd-p-subst bd
    ... | bd' , bdσ =
      HBDPInr bd' , HBDPInr bdσ
    lem-σ-hbd-p-subst (HBDPPair bd1 bd2)
      with lem-σ-hbd-p-subst bd1 | lem-σ-hbd-p-subst bd2
    ... | bd1' , bdσ1 | bd2' , bdσ2 =
      HBDPPair bd1' bd2' , HBDPPair bdσ1 bdσ2
    lem-σ-hbd-p-subst HBDPWild = HBDPWild , HBDPWild
    lem-σ-hbd-p-subst (HBDPEHole (HUBσSubst ubσ ub)) =
      HBDPEHole ubσ , HBDPEHole ub
    lem-σ-hbd-p-subst (HBDPHole (HUBσSubst ubσ ub) bd)
      with lem-σ-hbd-p-subst bd
    ... | bd' , bdσ =
      HBDPHole ubσ bd' , HBDPHole ub bdσ

  mutual
    lem-rs-hbd : {e : ihexp} {r : rule} {rs : rules} →
                 hole-binders-disjoint e (r / rs) →
                 hole-binders-disjoint e r ×
                   hole-binders-disjoint e rs
    lem-rs-hbd HBDUnit = HBDUnit , HBDUnit
    lem-rs-hbd HBDNum = HBDNum , HBDNum
    lem-rs-hbd HBDVar = HBDVar , HBDVar
    lem-rs-hbd (HBDLam bd)
      with lem-rs-hbd bd
    ... | bdr , bdrs = HBDLam bdr , HBDLam bdrs
    lem-rs-hbd (HBDAp bd1 bd2)
      with lem-rs-hbd bd1 | lem-rs-hbd bd2
    ... | bdr1 , bdrs1 | bdr2 , bdrs2 =
      HBDAp bdr1 bdr2 , HBDAp bdrs1 bdrs2
    lem-rs-hbd (HBDInl bd)
      with lem-rs-hbd bd
    ... | bdr , bdrs = HBDInl bdr , HBDInl bdrs
    lem-rs-hbd (HBDInr bd)
      with lem-rs-hbd bd
    ... | bdr , bdrs = HBDInr bdr , HBDInr bdrs
    lem-rs-hbd (HBDMatch bd (HBDZRules bdpre bdpost))
      with lem-rs-hbd bd |
           lem-rs-hbd-rs bdpre |
           lem-rs-hbd-rs bdpost
    ... | bdr , bdrs
        | bdprer , bdprers
        | bdpostr , bdpostrs =
      HBDMatch bdr (HBDZRules bdprer bdpostr) ,
      HBDMatch bdrs (HBDZRules bdprers bdpostrs)
    lem-rs-hbd (HBDPair bd1 bd2)
      with lem-rs-hbd bd1 | lem-rs-hbd bd2
    ... | bdr1 , bdrs1 | bdr2 , bdrs2 =
      HBDPair bdr1 bdr2 , HBDPair bdrs1 bdrs2
    lem-rs-hbd (HBDFst bd)
      with lem-rs-hbd bd
    ... | bdr , bdrs = HBDFst bdr , HBDFst bdrs
    lem-rs-hbd (HBDSnd bd)
      with lem-rs-hbd bd
    ... | bdr , bdrs = HBDSnd bdr , HBDSnd bdrs
    lem-rs-hbd (HBDEHole bdσ)
      with lem-rs-hbd-σ bdσ
    ... | bdσr , bdσrs = HBDEHole bdσr , HBDEHole bdσrs
    lem-rs-hbd (HBDHole bdσ bd)
      with lem-rs-hbd-σ bdσ | lem-rs-hbd bd
    ... | bdσr , bdσrs | bdr , bdrs =
      HBDHole bdσr bdr , HBDHole bdσrs bdrs

    lem-rs-hbd-σ : {σ : subst-env} {r : rule} {rs : rules} →
                   hole-binders-disjoint-σ σ (r / rs) →
                   hole-binders-disjoint-σ σ r ×
                     hole-binders-disjoint-σ σ rs
    lem-rs-hbd-σ HBDσId = HBDσId , HBDσId
    lem-rs-hbd-σ (HBDσSubst bd bdσ)
      with lem-rs-hbd bd | lem-rs-hbd-σ bdσ
    ... | bdr , bdrs | bdσr , bdσrs =
      HBDσSubst bdr bdσr , HBDσSubst bdrs bdσrs

    lem-rs-hbd-rs : {rs1 : rules} {r : rule} {rs2 : rules} →
                    hole-binders-disjoint-rs rs1 (r / rs2) →
                    hole-binders-disjoint-rs rs1 r ×
                      hole-binders-disjoint-rs rs1 rs2
    lem-rs-hbd-rs HBDNoRules = HBDNoRules , HBDNoRules
    lem-rs-hbd-rs (HBDRules bdr bdrs)
      with lem-rs-hbd-r bdr | lem-rs-hbd-rs bdrs
    ... | bdrr , bdrrs | bdrsr , bdrsrs =
      HBDRules bdrr bdrsr , HBDRules bdrrs bdrsrs
   
    lem-rs-hbd-r : {r1 : rule} {r2 : rule} {rs : rules} →
                   hole-binders-disjoint-r r1 (r2 / rs) →
                   hole-binders-disjoint-r r1 r2 ×
                     hole-binders-disjoint-r r1 rs
    lem-rs-hbd-r (HBDRule bdp bd)
      with lem-rs-hbd-p bdp | lem-rs-hbd bd
    ... | bdpr , bdprs | bdr , bdrs =
      HBDRule bdpr bdr , HBDRule bdprs bdrs

    lem-rs-hbd-p : {p : pattrn} {r : rule} {rs : rules} →
                   hole-binders-disjoint-p p (r / rs) →
                   hole-binders-disjoint-p p r ×
                     hole-binders-disjoint-p p rs
    lem-rs-hbd-p HBDPUnit = HBDPUnit , HBDPUnit
    lem-rs-hbd-p HBDPNum = HBDPNum , HBDPNum
    lem-rs-hbd-p HBDPVar = HBDPVar , HBDPVar
    lem-rs-hbd-p (HBDPInl bd)
      with lem-rs-hbd-p bd
    ... | bdr , bdrs = HBDPInl bdr , HBDPInl bdrs
    lem-rs-hbd-p (HBDPInr bd)
      with lem-rs-hbd-p bd
    ... | bdr , bdrs = HBDPInr bdr , HBDPInr bdrs
    lem-rs-hbd-p (HBDPPair bd1 bd2)
      with lem-rs-hbd-p bd1 | lem-rs-hbd-p bd2
    ... | bdr1 , bdrs1 | bdr2 , bdrs2  =
      HBDPPair bdr1 bdr2 , HBDPPair bdrs1 bdrs2
    lem-rs-hbd-p HBDPWild = HBDPWild , HBDPWild
    lem-rs-hbd-p (HBDPEHole (HUBRules ubr ubrs)) =
      HBDPEHole ubr , HBDPEHole ubrs
    lem-rs-hbd-p (HBDPHole (HUBRules ubr ubrs) bd)
      with lem-rs-hbd-p bd
    ... | bdr , bdrs = HBDPHole ubr bdr , HBDPHole ubrs bdrs
    
  mutual
    lem-r-hbd : {e : ihexp} {pr : pattrn} {er : ihexp} →
                hole-binders-disjoint e (pr => er) →
                hole-binders-disjoint e pr ×
                  hole-binders-disjoint e er
    lem-r-hbd HBDUnit = HBDUnit , HBDUnit
    lem-r-hbd HBDNum = HBDNum , HBDNum
    lem-r-hbd HBDVar = HBDVar , HBDVar
    lem-r-hbd (HBDLam bd)
      with lem-r-hbd bd
    ... | bdp , bdr = HBDLam bdp , HBDLam bdr
    lem-r-hbd (HBDAp bd1 bd2)
      with lem-r-hbd bd1 | lem-r-hbd bd2
    ... | bdp1 , bdr1 | bdp2 , bdr2 =
      HBDAp bdp1 bdp2 , HBDAp bdr1 bdr2
    lem-r-hbd (HBDInl bd)
      with lem-r-hbd bd
    ... | bdp , bdr = HBDInl bdp , HBDInl bdr
    lem-r-hbd (HBDInr bd)
      with lem-r-hbd bd
    ... | bdp , bdr = HBDInr bdp , HBDInr bdr
    lem-r-hbd (HBDMatch bd (HBDZRules bdpre bdpost))
      with lem-r-hbd bd |
           lem-r-hbd-rs bdpre |
           lem-r-hbd-rs bdpost 
    ... | bdp , bdr
        | bdprep , bdprer
        | bdpostp , bdpostr =
      HBDMatch bdp (HBDZRules bdprep bdpostp) ,
      HBDMatch bdr (HBDZRules bdprer bdpostr)
    lem-r-hbd (HBDPair bd1 bd2)
      with lem-r-hbd bd1 | lem-r-hbd bd2
    ... | bdp1 , bdr1 | bdp2 , bdr2 =
      HBDPair bdp1 bdp2 , HBDPair bdr1 bdr2
    lem-r-hbd (HBDFst bd)
      with lem-r-hbd bd
    ... | bdp , bdr = HBDFst bdp , HBDFst bdr
    lem-r-hbd (HBDSnd bd)
      with lem-r-hbd bd
    ... | bdp , bdr = HBDSnd bdp , HBDSnd bdr
    lem-r-hbd (HBDEHole bdσ)
      with lem-r-hbd-σ bdσ
    ... | bdσp , bdσe = HBDEHole bdσp , HBDEHole bdσe
    lem-r-hbd (HBDHole bdσ bd)
      with lem-r-hbd-σ bdσ | lem-r-hbd bd
    ... | bdσp , bdσe | bdp , bde =
      HBDHole bdσp bdp , HBDHole bdσe bde

    lem-r-hbd-σ : {σ : subst-env} {pr : pattrn} {er : ihexp} →
                  hole-binders-disjoint-σ σ (pr => er) →
                  hole-binders-disjoint-σ σ pr ×
                    hole-binders-disjoint-σ σ er
    lem-r-hbd-σ HBDσId = HBDσId , HBDσId
    lem-r-hbd-σ (HBDσSubst bd bdσ)
      with lem-r-hbd bd | lem-r-hbd-σ bdσ
    ... | bdσp , bdσe | bdp , bde =
      HBDσSubst bdσp bdp , HBDσSubst bdσe bde

    lem-r-hbd-rs : {rs : rules} {pr : pattrn} {er : ihexp} →
                   hole-binders-disjoint-rs rs (pr => er) →
                   hole-binders-disjoint-rs rs pr ×
                     hole-binders-disjoint-rs rs er
    lem-r-hbd-rs HBDNoRules = HBDNoRules , HBDNoRules
    lem-r-hbd-rs (HBDRules bdr bdrs)
      with lem-r-hbd-r bdr | lem-r-hbd-rs bdrs
    ... | bdrp , bdre | bdrsp , bdrse =
      HBDRules bdrp bdrsp , HBDRules bdre bdrse

    lem-r-hbd-r : {r : rule} {pr : pattrn} {er : ihexp} →
                  hole-binders-disjoint-r r (pr => er) →
                  hole-binders-disjoint-r r pr ×
                    hole-binders-disjoint-r r er
    lem-r-hbd-r (HBDRule bdp bd)
      with lem-r-hbd-p bdp | lem-r-hbd bd
    ... | bdpp , bdpe | ebdp , ebde =
      HBDRule bdpp ebdp , HBDRule bdpe ebde

    lem-r-hbd-p : {p : pattrn} {pr : pattrn} {er : ihexp} →
                  hole-binders-disjoint-p p (pr => er) →
                  hole-binders-disjoint-p p pr ×
                    hole-binders-disjoint-p p er
    lem-r-hbd-p HBDPUnit = HBDPUnit , HBDPUnit
    lem-r-hbd-p HBDPNum = HBDPNum , HBDPNum
    lem-r-hbd-p HBDPVar = HBDPVar , HBDPVar
    lem-r-hbd-p (HBDPInl bd)
      with lem-r-hbd-p bd
    ... | bdp , bde = HBDPInl bdp , HBDPInl bde
    lem-r-hbd-p (HBDPInr bd)
      with lem-r-hbd-p bd
    ... | bdp , bde = HBDPInr bdp , HBDPInr bde
    lem-r-hbd-p (HBDPPair bd1 bd2)
      with lem-r-hbd-p bd1 | lem-r-hbd-p bd2
    ... | bdp1 , bde1 | bdp2 , bde2 =
      HBDPPair bdp1 bdp2 , HBDPPair bde1 bde2
    lem-r-hbd-p HBDPWild = HBDPWild , HBDPWild
    lem-r-hbd-p (HBDPEHole (HUBRule ubp ube)) =
      HBDPEHole ubp , HBDPEHole ube
    lem-r-hbd-p (HBDPHole (HUBRule ubp ube) bd)
      with lem-r-hbd-p bd
    ... | bdp , bde =
      HBDPHole ubp bdp , HBDPHole ube bde

  mutual
    lem-p-hbd-inl : {e : ihexp} {p1 : pattrn} →
                    hole-binders-disjoint e (inl p1) →
                    hole-binders-disjoint e p1
    lem-p-hbd-inl HBDUnit = HBDUnit
    lem-p-hbd-inl HBDNum = HBDNum
    lem-p-hbd-inl HBDVar = HBDVar
    lem-p-hbd-inl (HBDLam bd) = HBDLam (lem-p-hbd-inl bd)
    lem-p-hbd-inl (HBDAp bd1 bd2) =
      HBDAp (lem-p-hbd-inl bd1) (lem-p-hbd-inl bd2)
    lem-p-hbd-inl (HBDInl bd) = HBDInl (lem-p-hbd-inl bd)
    lem-p-hbd-inl (HBDInr bd) = HBDInr (lem-p-hbd-inl bd)
    lem-p-hbd-inl (HBDMatch bd (HBDZRules bdpre bdpost)) =
      HBDMatch (lem-p-hbd-inl bd)
               (HBDZRules (lem-p-hbd-rs-inl bdpre)
                          (lem-p-hbd-rs-inl bdpost))
    lem-p-hbd-inl (HBDPair bd1 bd2) =
      HBDPair (lem-p-hbd-inl bd1) (lem-p-hbd-inl bd2)
    lem-p-hbd-inl (HBDFst bd) =  HBDFst (lem-p-hbd-inl bd)
    lem-p-hbd-inl (HBDSnd bd) = HBDSnd (lem-p-hbd-inl bd)
    lem-p-hbd-inl (HBDEHole bdσ) =
      HBDEHole (lem-p-hbd-σ-inl bdσ)
    lem-p-hbd-inl (HBDHole bdσ bd) =
      HBDHole (lem-p-hbd-σ-inl bdσ) (lem-p-hbd-inl bd)

    lem-p-hbd-σ-inl : {σ : subst-env} {p1 : pattrn} →
                      hole-binders-disjoint-σ σ (inl p1) →
                      hole-binders-disjoint-σ σ p1
    lem-p-hbd-σ-inl HBDσId = HBDσId
    lem-p-hbd-σ-inl (HBDσSubst bd bdσ) =
      HBDσSubst (lem-p-hbd-inl bd) (lem-p-hbd-σ-inl bdσ)

    lem-p-hbd-rs-inl : {rs : rules} {p1 : pattrn} →
                       hole-binders-disjoint-rs rs (inl p1) →
                       hole-binders-disjoint-rs rs p1
    lem-p-hbd-rs-inl HBDNoRules = HBDNoRules
    lem-p-hbd-rs-inl (HBDRules bdr bdrs) =
      HBDRules (lem-p-hbd-r-inl bdr) (lem-p-hbd-rs-inl bdrs)

    lem-p-hbd-r-inl : {r : rule} {p1 : pattrn} →
                      hole-binders-disjoint-r r (inl p1) →
                      hole-binders-disjoint-r r p1
    lem-p-hbd-r-inl (HBDRule bdp bd) =
      HBDRule (lem-p-hbd-p-inl bdp) (lem-p-hbd-inl bd)

    lem-p-hbd-p-inl : {p : pattrn} {p1 : pattrn} →
                      hole-binders-disjoint-p p (inl p1) →
                      hole-binders-disjoint-p p p1
    lem-p-hbd-p-inl HBDPUnit = HBDPUnit
    lem-p-hbd-p-inl HBDPNum = HBDPNum
    lem-p-hbd-p-inl HBDPVar = HBDPVar
    lem-p-hbd-p-inl (HBDPInl bd) =
      HBDPInl (lem-p-hbd-p-inl bd)
    lem-p-hbd-p-inl (HBDPInr bd) =
      HBDPInr (lem-p-hbd-p-inl bd)
    lem-p-hbd-p-inl (HBDPPair bd1 bd2) =
      HBDPPair (lem-p-hbd-p-inl bd1)
        (lem-p-hbd-p-inl bd2)
    lem-p-hbd-p-inl HBDPWild = HBDPWild
    lem-p-hbd-p-inl (HBDPEHole (HUBPInl ub)) =
      HBDPEHole ub
    lem-p-hbd-p-inl (HBDPHole (HUBPInl ub) bd) =
      HBDPHole ub (lem-p-hbd-p-inl bd)

  mutual
    lem-p-hbd-inr : {e : ihexp} {p1 : pattrn} →
                    hole-binders-disjoint e (inr p1) →
                    hole-binders-disjoint e p1
    lem-p-hbd-inr HBDUnit = HBDUnit
    lem-p-hbd-inr HBDNum = HBDNum
    lem-p-hbd-inr HBDVar = HBDVar
    lem-p-hbd-inr (HBDLam bd) =
      HBDLam (lem-p-hbd-inr bd)
    lem-p-hbd-inr (HBDAp bd1 bd2) =
      HBDAp (lem-p-hbd-inr bd1) (lem-p-hbd-inr bd2)
    lem-p-hbd-inr (HBDInl bd) = HBDInl (lem-p-hbd-inr bd)
    lem-p-hbd-inr (HBDInr bd) = HBDInr (lem-p-hbd-inr bd)
    lem-p-hbd-inr (HBDMatch bd (HBDZRules bdpre bdpost)) =
      HBDMatch (lem-p-hbd-inr bd)
              (HBDZRules (lem-p-hbd-rs-inr bdpre)
                        (lem-p-hbd-rs-inr bdpost))
    lem-p-hbd-inr (HBDPair bd1 bd2) =
      HBDPair (lem-p-hbd-inr bd1) (lem-p-hbd-inr bd2)
    lem-p-hbd-inr (HBDFst bd) = HBDFst (lem-p-hbd-inr bd)
    lem-p-hbd-inr (HBDSnd bd) = HBDSnd (lem-p-hbd-inr bd)
    lem-p-hbd-inr (HBDEHole bdσ) =
      HBDEHole (lem-p-hbd-σ-inr bdσ)
    lem-p-hbd-inr (HBDHole bdσ bd) =
      HBDHole (lem-p-hbd-σ-inr bdσ) (lem-p-hbd-inr bd)

    lem-p-hbd-σ-inr : {σ : subst-env} {p1 : pattrn} →
                      hole-binders-disjoint-σ σ (inr p1) →
                      hole-binders-disjoint-σ σ p1
    lem-p-hbd-σ-inr HBDσId = HBDσId
    lem-p-hbd-σ-inr (HBDσSubst bd bdσ) =
      HBDσSubst (lem-p-hbd-inr bd) (lem-p-hbd-σ-inr bdσ)

    lem-p-hbd-rs-inr : {rs : rules} {p1 : pattrn} →
                       hole-binders-disjoint-rs rs (inr p1) →
                       hole-binders-disjoint-rs rs p1
    lem-p-hbd-rs-inr HBDNoRules = HBDNoRules
    lem-p-hbd-rs-inr (HBDRules bdr bdrs) =
      HBDRules (lem-p-hbd-r-inr bdr) (lem-p-hbd-rs-inr bdrs)

    lem-p-hbd-r-inr : {r : rule} {p1 : pattrn} →
                      hole-binders-disjoint-r r (inr p1) →
                      hole-binders-disjoint-r r p1
    lem-p-hbd-r-inr (HBDRule bdp bd) =
      HBDRule (lem-p-hbd-p-inr bdp) (lem-p-hbd-inr bd)

    lem-p-hbd-p-inr : {p : pattrn} {p1 : pattrn} →
                      hole-binders-disjoint-p p (inr p1) →
                      hole-binders-disjoint-p p p1
    lem-p-hbd-p-inr HBDPUnit = HBDPUnit
    lem-p-hbd-p-inr HBDPNum = HBDPNum
    lem-p-hbd-p-inr HBDPVar = HBDPVar
    lem-p-hbd-p-inr (HBDPInl bd) =
      HBDPInl (lem-p-hbd-p-inr bd)
    lem-p-hbd-p-inr (HBDPInr bd) =
      HBDPInr (lem-p-hbd-p-inr bd)
    lem-p-hbd-p-inr (HBDPPair bd1 bd2) =
      HBDPPair (lem-p-hbd-p-inr bd1)
              (lem-p-hbd-p-inr bd2)
    lem-p-hbd-p-inr HBDPWild = HBDPWild
    lem-p-hbd-p-inr (HBDPEHole (HUBPInr ub)) =
      HBDPEHole ub
    lem-p-hbd-p-inr (HBDPHole (HUBPInr ub) bd) =
      HBDPHole ub (lem-p-hbd-p-inr bd)

  mutual
    lem-p-hbd-pair : {e : ihexp} {p1 p2 : pattrn} →
                     hole-binders-disjoint e ⟨ p1 , p2 ⟩ →
                     hole-binders-disjoint e p1 ×
                       hole-binders-disjoint e p2
    lem-p-hbd-pair HBDUnit = HBDUnit , HBDUnit
    lem-p-hbd-pair HBDNum = HBDNum , HBDNum
    lem-p-hbd-pair HBDVar = HBDVar , HBDVar
    lem-p-hbd-pair (HBDLam bd)
      with lem-p-hbd-pair bd
    ... | bd1 , bd2 = HBDLam bd1 , HBDLam bd2
    lem-p-hbd-pair (HBDAp bd1 bd2)
      with lem-p-hbd-pair bd1 | lem-p-hbd-pair bd2
    ... | bd1₁ , bd1₂ | bd2₁ , bd2₂ =
      HBDAp bd1₁ bd2₁ , HBDAp bd1₂ bd2₂
    lem-p-hbd-pair (HBDInl bd)
      with lem-p-hbd-pair bd
    ... | bd1 , bd2 = HBDInl bd1 , HBDInl bd2
    lem-p-hbd-pair (HBDInr bd)
      with lem-p-hbd-pair bd
    ... | bd1 , bd2 = HBDInr bd1 , HBDInr bd2
    lem-p-hbd-pair (HBDMatch bd (HBDZRules bdpre bdpost))
      with lem-p-hbd-pair bd |
           lem-p-hbd-rs-pair bdpre |
           lem-p-hbd-rs-pair bdpost
    ... | bd1 , bd2
        | bdpre1 , bdpre2
        | bdpost1 , bdpost2 =
      HBDMatch bd1 (HBDZRules bdpre1 bdpost1) ,
      HBDMatch bd2 (HBDZRules bdpre2 bdpost2)
    lem-p-hbd-pair (HBDPair bd1 bd2)
      with lem-p-hbd-pair bd1 | lem-p-hbd-pair bd2
    ... | bd1₁ , bd1₂ | bd2₁ , bd2₂ =
      HBDPair bd1₁ bd2₁ , HBDPair bd1₂ bd2₂
    lem-p-hbd-pair (HBDFst bd)
      with lem-p-hbd-pair bd
    ... | bd1 , bd2 = HBDFst bd1 , HBDFst bd2
    lem-p-hbd-pair (HBDSnd bd)
      with lem-p-hbd-pair bd
    ... | bd1 , bd2 = HBDSnd bd1 , HBDSnd bd2
    lem-p-hbd-pair (HBDEHole bdσ)
      with lem-p-hbd-σ-pair bdσ
    ... | bdσ1 , bdσ2 = HBDEHole bdσ1 , HBDEHole bdσ2
    lem-p-hbd-pair (HBDHole bdσ bd)
      with lem-p-hbd-σ-pair bdσ | lem-p-hbd-pair bd
    ... | bdσ1 , bdσ2 | bd1 , bd2 =
      HBDHole bdσ1 bd1 , HBDHole bdσ2 bd2

    lem-p-hbd-σ-pair : {σ : subst-env} {p1 p2 : pattrn} →
                       hole-binders-disjoint-σ σ ⟨ p1 , p2 ⟩ →
                       hole-binders-disjoint-σ σ p1 ×
                         hole-binders-disjoint-σ σ p2
    lem-p-hbd-σ-pair HBDσId = HBDσId , HBDσId
    lem-p-hbd-σ-pair (HBDσSubst bd bdσ)
      with lem-p-hbd-pair bd | lem-p-hbd-σ-pair bdσ
    ... | bd1 , bd2 | bdσ1 , bdσ2 =
      HBDσSubst bd1 bdσ1 , HBDσSubst bd2 bdσ2

    lem-p-hbd-rs-pair : {rs : rules} {p1 p2 : pattrn} →
                        hole-binders-disjoint-rs rs ⟨ p1 , p2 ⟩ →
                        hole-binders-disjoint-rs rs p1 ×
                          hole-binders-disjoint-rs rs p2
    lem-p-hbd-rs-pair HBDNoRules = HBDNoRules , HBDNoRules
    lem-p-hbd-rs-pair (HBDRules bdr bdrs)
      with lem-p-hbd-r-pair bdr |
           lem-p-hbd-rs-pair bdrs
    ... | bdr1 , bdr2 | bdrs1 , bdrs2 =
      HBDRules bdr1 bdrs1 , HBDRules bdr2 bdrs2

    lem-p-hbd-r-pair : {r : rule} {p1 p2 : pattrn} →
                       hole-binders-disjoint-r r ⟨ p1 , p2 ⟩ →
                       hole-binders-disjoint-r r p1 ×
                         hole-binders-disjoint-r r p2
    lem-p-hbd-r-pair (HBDRule bdp bd)
      with lem-p-hbd-p-pair bdp |
           lem-p-hbd-pair bd
    ... | bdp1 , bdp2 | bd1 , bd2 =
      HBDRule bdp1 bd1 , HBDRule bdp2 bd2

    lem-p-hbd-p-pair : {p : pattrn} {p1 p2 : pattrn} →
                       hole-binders-disjoint-p p ⟨ p1 , p2 ⟩ →
                       hole-binders-disjoint-p p p1 ×
                         hole-binders-disjoint-p p p2
    lem-p-hbd-p-pair HBDPUnit = HBDPUnit , HBDPUnit
    lem-p-hbd-p-pair HBDPNum = HBDPNum , HBDPNum
    lem-p-hbd-p-pair HBDPVar = HBDPVar , HBDPVar
    lem-p-hbd-p-pair (HBDPInl bd)
      with lem-p-hbd-p-pair bd
    ... | bd1 , bd2 = HBDPInl bd1 , HBDPInl bd2
    lem-p-hbd-p-pair (HBDPInr bd)
      with lem-p-hbd-p-pair bd
    ... | bd1 , bd2 = HBDPInr bd1 , HBDPInr bd2
    lem-p-hbd-p-pair (HBDPPair bd1 bd2)
      with lem-p-hbd-p-pair bd1 |
           lem-p-hbd-p-pair bd2
    ... | bd1₁ , bd1₂ | bd2₁ , bd2₂ =
      HBDPPair bd1₁ bd2₁ , HBDPPair bd1₂ bd2₂
    lem-p-hbd-p-pair HBDPWild = HBDPWild , HBDPWild
    lem-p-hbd-p-pair (HBDPEHole (HUBPPair ub1 ub2)) =
      HBDPEHole ub1 , HBDPEHole ub2
    lem-p-hbd-p-pair (HBDPHole (HUBPPair ub1 ub2) bd)
      with lem-p-hbd-p-pair bd
    ... | bd1 , bd2 =
      HBDPHole ub1 bd1 , HBDPHole ub2 bd2

  mutual
    lem-p-hbd-ehole : {e : ihexp} {u : Nat} →
                      hole-binders-disjoint {T = pattrn} e ⦇-⦈[ u ] →
                      hole-unbound-in-e u e
    lem-p-hbd-ehole HBDUnit = HUBUnit
    lem-p-hbd-ehole HBDNum = HUBNum
    lem-p-hbd-ehole HBDVar = HUBVar
    lem-p-hbd-ehole (HBDLam bd) =
      HUBLam (lem-p-hbd-ehole bd)
    lem-p-hbd-ehole (HBDAp bd1 bd2) =
      HUBAp (lem-p-hbd-ehole bd1) (lem-p-hbd-ehole bd2)
    lem-p-hbd-ehole (HBDInl bd) =
      HUBInl (lem-p-hbd-ehole bd)
    lem-p-hbd-ehole (HBDInr bd) =
      HUBInr (lem-p-hbd-ehole bd)
    lem-p-hbd-ehole (HBDMatch bd (HBDZRules bdpre bdpost)) =
      HUBMatch (lem-p-hbd-ehole bd)
               (HUBZRules (lem-p-hbd-rs-ehole bdpre)
                          (lem-p-hbd-rs-ehole bdpost))
    lem-p-hbd-ehole (HBDPair bd1 bd2) =
      HUBPair (lem-p-hbd-ehole bd1) (lem-p-hbd-ehole bd2)
    lem-p-hbd-ehole (HBDFst bd) = HUBFst (lem-p-hbd-ehole bd)
    lem-p-hbd-ehole (HBDSnd bd) = HUBSnd (lem-p-hbd-ehole bd)
    lem-p-hbd-ehole (HBDEHole bdσ) =
      HUBEHole (lem-p-hbd-σ-ehole bdσ)
    lem-p-hbd-ehole (HBDHole bdσ bd) =
      HUBHole (lem-p-hbd-σ-ehole bdσ) (lem-p-hbd-ehole bd)
  
    lem-p-hbd-σ-ehole : {σ : subst-env} {w : Nat} →
                        hole-binders-disjoint-σ {T = pattrn} σ ⦇-⦈[ w ] →
                        hole-unbound-in-σ w σ
    lem-p-hbd-σ-ehole HBDσId = HUBσId
    lem-p-hbd-σ-ehole (HBDσSubst bd bdσ) =
      HUBσSubst (lem-p-hbd-ehole bd) (lem-p-hbd-σ-ehole bdσ)
 
    lem-p-hbd-rs-ehole : {rs : rules} {w : Nat} →
                         hole-binders-disjoint-rs {T = pattrn} rs ⦇-⦈[ w ] →
                         hole-unbound-in-rs w rs
    lem-p-hbd-rs-ehole HBDNoRules = HUBNoRules
    lem-p-hbd-rs-ehole (HBDRules bdr bdrs) =
      HUBRules (lem-p-hbd-r-ehole bdr) (lem-p-hbd-rs-ehole bdrs)

    lem-p-hbd-r-ehole : {r : rule} {w : Nat} →
                        hole-binders-disjoint-r {T = pattrn} r ⦇-⦈[ w ] →
                        hole-unbound-in-r w r
    lem-p-hbd-r-ehole (HBDRule bdp bd) =
      HUBRule (lem-p-hbd-p-ehole bdp) (lem-p-hbd-ehole bd)

    lem-p-hbd-p-ehole : {p : pattrn} {w : Nat} →
                        hole-binders-disjoint-p {T = pattrn} p ⦇-⦈[ w ] →
                        hole-unbound-in-p w p
    lem-p-hbd-p-ehole HBDPUnit = HUBPUnit
    lem-p-hbd-p-ehole HBDPNum = HUBPNum
    lem-p-hbd-p-ehole HBDPVar = HUBPVar
    lem-p-hbd-p-ehole (HBDPInl bd) =
      HUBPInl (lem-p-hbd-p-ehole bd)
    lem-p-hbd-p-ehole (HBDPInr bd) =
      HUBPInr (lem-p-hbd-p-ehole bd)
    lem-p-hbd-p-ehole (HBDPPair bd1 bd2) =
      HUBPPair (lem-p-hbd-p-ehole bd1)
              (lem-p-hbd-p-ehole bd2)
    lem-p-hbd-p-ehole HBDPWild = HUBPWild
    lem-p-hbd-p-ehole (HBDPEHole (HUBPEHole u≠w)) =
      HUBPEHole (flip u≠w)
    lem-p-hbd-p-ehole (HBDPHole (HUBPEHole u≠w) bd) =
      HUBPHole (flip u≠w) (lem-p-hbd-p-ehole bd)

  mutual
    lem-p-hbd-hole : {e : ihexp} {p1 : pattrn} {w : Nat} {τ : htyp} →
                       hole-binders-disjoint e ⦇⌜ p1 ⌟⦈[ w , τ ] →
                       hole-unbound-in-e w e ×
                         hole-binders-disjoint e p1
    lem-p-hbd-hole HBDUnit = HUBUnit , HBDUnit
    lem-p-hbd-hole HBDNum = HUBNum , HBDNum
    lem-p-hbd-hole HBDVar = HUBVar , HBDVar
    lem-p-hbd-hole (HBDLam bd)
      with lem-p-hbd-hole bd
    ... | ub , bd' = HUBLam ub , HBDLam bd'
    lem-p-hbd-hole (HBDAp bd1 bd2)
      with lem-p-hbd-hole bd1 | lem-p-hbd-hole bd2
    ... | ub1 , bd1' | ub2 , bd2' =
      HUBAp ub1 ub2 , HBDAp bd1' bd2'
    lem-p-hbd-hole (HBDInl bd)
      with lem-p-hbd-hole bd
    ... | ub , bd' = HUBInl ub , HBDInl bd'
    lem-p-hbd-hole (HBDInr bd)
      with lem-p-hbd-hole bd
    ... | ub , bd' = HUBInr ub , HBDInr bd'
    lem-p-hbd-hole (HBDMatch bd (HBDZRules bdpre bdpost))
      with lem-p-hbd-hole bd |
           lem-p-hbd-rs-hole bdpre |
           lem-p-hbd-rs-hole bdpost
    ... | ub , bd'
        | ubpre , bdpre'
        | ubdpost , bdpost' =
      HUBMatch ub (HUBZRules ubpre ubdpost) ,
      HBDMatch bd' (HBDZRules bdpre' bdpost')
    lem-p-hbd-hole (HBDPair bd1 bd2)
      with lem-p-hbd-hole bd1 | lem-p-hbd-hole bd2
    ... | ub1 , bd1' | ub2 , bd2' =
      HUBPair ub1 ub2 , HBDPair bd1' bd2'
    lem-p-hbd-hole (HBDFst bd)
      with lem-p-hbd-hole bd
    ... | ub , bd' = HUBFst ub , HBDFst bd'
    lem-p-hbd-hole (HBDSnd bd)
      with lem-p-hbd-hole bd
    ... | ub , bd' = HUBSnd ub , HBDSnd bd'
    lem-p-hbd-hole (HBDEHole bdσ)
      with lem-p-hbd-σ-hole bdσ
    ... | ubσ , bdσ' = HUBEHole ubσ , HBDEHole bdσ'
    lem-p-hbd-hole (HBDHole bdσ bd)
      with lem-p-hbd-σ-hole bdσ | lem-p-hbd-hole bd
    ... | ubσ , bdσ' | ub , bd' =
      HUBHole ubσ ub , HBDHole bdσ' bd'

    lem-p-hbd-σ-hole : {σ : subst-env} {p1 : pattrn} {w : Nat} {τ : htyp} →
                         hole-binders-disjoint-σ σ ⦇⌜ p1 ⌟⦈[ w , τ ] →
                         hole-unbound-in-σ w σ ×
                           hole-binders-disjoint-σ σ p1
    lem-p-hbd-σ-hole HBDσId = HUBσId , HBDσId
    lem-p-hbd-σ-hole (HBDσSubst bd bdσ)
      with lem-p-hbd-hole bd | lem-p-hbd-σ-hole bdσ
    ... | ub , bd' | ubσ , bdσ' =
      HUBσSubst ub ubσ , HBDσSubst bd' bdσ'
    
    lem-p-hbd-rs-hole : {rs : rules} {p1 : pattrn} {w : Nat} {τ : htyp} →
                          hole-binders-disjoint-rs rs ⦇⌜ p1 ⌟⦈[ w , τ ] →
                          hole-unbound-in-rs w rs ×
                            hole-binders-disjoint-rs rs p1
    lem-p-hbd-rs-hole HBDNoRules = HUBNoRules , HBDNoRules
    lem-p-hbd-rs-hole (HBDRules bdr bdrs)
      with lem-p-hbd-r-hole bdr | lem-p-hbd-rs-hole bdrs
    ... | ubr , bdr' | ubrs , bdrs' =
      HUBRules ubr ubrs , HBDRules bdr' bdrs'

    lem-p-hbd-r-hole : {r : rule} {p1 : pattrn} {w : Nat} {τ : htyp} →
                         hole-binders-disjoint-r r ⦇⌜ p1 ⌟⦈[ w , τ ] →
                         hole-unbound-in-r w r ×
                           hole-binders-disjoint-r r p1
    lem-p-hbd-r-hole (HBDRule bdp bde)
      with lem-p-hbd-p-hole bdp | lem-p-hbd-hole bde
    ... | ubp , bdp' | ube , bde' =
      HUBRule ubp ube , HBDRule bdp' bde'

    lem-p-hbd-p-hole : {p : pattrn} {p1 : pattrn} {w : Nat} {τ : htyp} →
                         hole-binders-disjoint-p p ⦇⌜ p1 ⌟⦈[ w , τ ] →
                         hole-unbound-in-p w p ×
                           hole-binders-disjoint-p p p1
    lem-p-hbd-p-hole HBDPUnit = HUBPUnit , HBDPUnit
    lem-p-hbd-p-hole HBDPNum = HUBPNum , HBDPNum
    lem-p-hbd-p-hole HBDPVar = HUBPVar , HBDPVar
    lem-p-hbd-p-hole (HBDPInl bd)
      with lem-p-hbd-p-hole bd
    ... | ub , bd' = HUBPInl ub , HBDPInl bd'
    lem-p-hbd-p-hole (HBDPInr bd)
      with lem-p-hbd-p-hole bd
    ... | ub , bd' = HUBPInr ub , HBDPInr bd'
    lem-p-hbd-p-hole (HBDPPair bd1 bd2)
      with lem-p-hbd-p-hole bd1 | lem-p-hbd-p-hole bd2
    ... | ub1 , bd1' | ub2 , bd2' =
      HUBPPair ub1 ub2 , HBDPPair bd1' bd2'
    lem-p-hbd-p-hole HBDPWild = HUBPWild , HBDPWild
    lem-p-hbd-p-hole (HBDPEHole (HUBPHole u≠w ub)) =
      HUBPEHole (flip u≠w) , HBDPEHole ub
    lem-p-hbd-p-hole (HBDPHole (HUBPHole u≠w ub) bd)
      with lem-p-hbd-p-hole bd
    ... | ub' , bd' =
      HUBPHole (flip u≠w) ub' , HBDPHole ub bd'
    
  mutual
    hole-binders-disjoint-sym : {e1 e2 : ihexp} →
                                hole-binders-disjoint e1 e2 →
                                hole-binders-disjoint e2 e1
    hole-binders-disjoint-sym {e2 = unit} bd = HBDUnit
    hole-binders-disjoint-sym {e2 = N n} bd = HBDNum
    hole-binders-disjoint-sym {e2 = X x} bd = HBDVar
    hole-binders-disjoint-sym {e2 = ·λ x ·[ τ ] e2} bd = 
      HBDLam (hole-binders-disjoint-sym (lem-hbd-lam bd))
    hole-binders-disjoint-sym {e2 = e2₁ ∘ e2₂} bd
      with lem-hbd-ap bd
    ... | bd1 , bd2 =
      HBDAp (hole-binders-disjoint-sym bd1)
            (hole-binders-disjoint-sym bd2)
    hole-binders-disjoint-sym {e2 = inl τ e2} bd =
      HBDInl (hole-binders-disjoint-sym (lem-hbd-inl bd))
    hole-binders-disjoint-sym {e2 = inr τ e2} bd =
      HBDInr (hole-binders-disjoint-sym (lem-hbd-inr bd))
    hole-binders-disjoint-sym
      {e2 = match e2 ·: τ of (rs-pre / r / rs-post)} bd
      with lem-hbd-match bd
    ... | bd' , bdpre , bdr , bdpost =
      HBDMatch (hole-binders-disjoint-sym bd')
               (HBDZRules (rs-hole-binders-disjoint-sym bdpre)
                          (HBDRules (r-hole-binders-disjoint-sym bdr)
                                    (rs-hole-binders-disjoint-sym bdpost)))
                        
    hole-binders-disjoint-sym {e2 = ⟨ e2₁ , e2₂ ⟩} bd
      with lem-hbd-pair bd
    ... | bd1 , bd2 =
      HBDPair (hole-binders-disjoint-sym bd1)
             (hole-binders-disjoint-sym bd2)
    hole-binders-disjoint-sym {e2 = fst e2} bd =
      HBDFst (hole-binders-disjoint-sym (lem-hbd-fst bd))
    hole-binders-disjoint-sym {e2 = snd e2} bd =
      HBDSnd (hole-binders-disjoint-sym (lem-hbd-snd bd))
    hole-binders-disjoint-sym {e2 = ⦇-⦈⟨ u , σ ⟩} bd =
      HBDEHole (σ-hole-binders-disjoint-sym (lem-hbd-ehole bd))
    hole-binders-disjoint-sym {e2 = ⦇⌜ e2 ⌟⦈⟨ u , σ ⟩} bd
      with lem-hbd-hole bd
    ... | bdσ , bd' =
      HBDHole (σ-hole-binders-disjoint-sym bdσ)
                (hole-binders-disjoint-sym bd')

    rs-hole-binders-disjoint-sym : {e : ihexp} {rs : rules} →
                                   hole-binders-disjoint e rs →
                                   hole-binders-disjoint-rs rs e
    rs-hole-binders-disjoint-sym {rs = nil} bd = HBDNoRules
    rs-hole-binders-disjoint-sym {rs = r / rs} bd
      with lem-rs-hbd bd
    ... | rbd , rsbd =
      HBDRules (r-hole-binders-disjoint-sym rbd)
              (rs-hole-binders-disjoint-sym rsbd)

    r-hole-binders-disjoint-sym : {e : ihexp} {r : rule} →
                                  hole-binders-disjoint e r →
                                  hole-binders-disjoint-r r e
    r-hole-binders-disjoint-sym {r = pr => er} bd
      with lem-r-hbd bd
    ... | bdp , bde =
      HBDRule (p-hole-binders-disjoint-sym bdp)
              (hole-binders-disjoint-sym bde)

    σ-hole-binders-disjoint-sym : {e : ihexp} {σ : subst-env} →
                                  hole-binders-disjoint e σ →
                                  hole-binders-disjoint-σ σ e
    σ-hole-binders-disjoint-sym {σ = Id Γ} bdσ = HBDσId
    σ-hole-binders-disjoint-sym {σ = Subst d y σ} bdσ
      with lem-σ-hbd-subst bdσ
    ... | bd , bdσ' =
      HBDσSubst (hole-binders-disjoint-sym bd)
                (σ-hole-binders-disjoint-sym bdσ')

    p-hole-binders-disjoint-sym : {e : ihexp} {p : pattrn} →
                                  hole-binders-disjoint e p →
                                  hole-binders-disjoint-p p e
    p-hole-binders-disjoint-sym {p = unit} bd = HBDPUnit
    p-hole-binders-disjoint-sym {p = N n} bd = HBDPNum
    p-hole-binders-disjoint-sym {p = X x} bd = HBDPVar
    p-hole-binders-disjoint-sym {p = inl p} bd =
      HBDPInl (p-hole-binders-disjoint-sym (lem-p-hbd-inl bd))
    p-hole-binders-disjoint-sym {p = inr p} bd =
      HBDPInr (p-hole-binders-disjoint-sym (lem-p-hbd-inr bd))
    p-hole-binders-disjoint-sym {p = ⟨ p1 , p2 ⟩} bd
      with lem-p-hbd-pair bd
    ... | bd1 , bd2 = 
      HBDPPair (p-hole-binders-disjoint-sym bd1)
              (p-hole-binders-disjoint-sym bd2)
    p-hole-binders-disjoint-sym {p = wild} bd = HBDPWild
    p-hole-binders-disjoint-sym {p = ⦇-⦈[ w ]} bd =
      HBDPEHole (lem-p-hbd-ehole bd)
    p-hole-binders-disjoint-sym {p = ⦇⌜ p ⌟⦈[ w , τ ]} bd
      with lem-p-hbd-hole bd
    ... | ub , bd' =
      HBDPHole ub (p-hole-binders-disjoint-sym bd')

  mutual
    hole-binders-disjoint-σ-sym : {σ : subst-env} {e : ihexp} →
                                  hole-binders-disjoint-σ σ e →
                                  hole-binders-disjoint e σ
    hole-binders-disjoint-σ-sym {e = unit} hbd = HBDUnit
    hole-binders-disjoint-σ-sym {e = N n} hbd = HBDNum
    hole-binders-disjoint-σ-sym {e = X x} hbd = HBDVar
    hole-binders-disjoint-σ-sym {e = ·λ x ·[ τ ] e} hbd
      with lem-hbd-σ-lam hbd
    ... | hbd' = HBDLam (hole-binders-disjoint-σ-sym hbd')
    hole-binders-disjoint-σ-sym {e = e1 ∘ e2} hbd
      with lem-hbd-σ-ap hbd
    ... | hbd1 , hbd2 =
      HBDAp (hole-binders-disjoint-σ-sym hbd1)
            (hole-binders-disjoint-σ-sym hbd2)
    hole-binders-disjoint-σ-sym {e = inl τ e} hbd =
      HBDInl (hole-binders-disjoint-σ-sym (lem-hbd-σ-inl hbd))
    hole-binders-disjoint-σ-sym {e = inr τ e} hbd =
      HBDInr (hole-binders-disjoint-σ-sym (lem-hbd-σ-inr hbd))
    hole-binders-disjoint-σ-sym {e = match e ·: τ of (rs-pre / r / rs-post)} hbd
      with lem-hbd-σ-match hbd
    ... | hbd' , hbdpre , hbdr , hbdpost =
      HBDMatch (hole-binders-disjoint-σ-sym hbd')
               (HBDZRules (rs-hole-binders-disjoint-σ-sym hbdpre)
                          (HBDRules (r-hole-binders-disjoint-σ-sym hbdr)
                                    (rs-hole-binders-disjoint-σ-sym hbdpost)))
    hole-binders-disjoint-σ-sym {e = ⟨ e1 , e2 ⟩} hbd
      with lem-hbd-σ-pair hbd
    ... | hbd1 , hbd2 =
      HBDPair (hole-binders-disjoint-σ-sym hbd1)
              (hole-binders-disjoint-σ-sym hbd2)
    hole-binders-disjoint-σ-sym {e = fst e} hbd =
      HBDFst (hole-binders-disjoint-σ-sym (lem-hbd-σ-fst hbd))
    hole-binders-disjoint-σ-sym {e = snd e} hbd =
      HBDSnd (hole-binders-disjoint-σ-sym (lem-hbd-σ-snd hbd))
    hole-binders-disjoint-σ-sym {e = ⦇-⦈⟨ u , σ ⟩} hbd =
      HBDEHole (σ-hole-binders-disjoint-σ-sym (lem-hbd-σ-ehole hbd))
    hole-binders-disjoint-σ-sym {e = ⦇⌜ e ⌟⦈⟨ u , σ ⟩} hbd
      with lem-hbd-σ-hole hbd
    ... | hbdσ , hbde =
      HBDHole (σ-hole-binders-disjoint-σ-sym hbdσ)
                (hole-binders-disjoint-σ-sym hbde)

    σ-hole-binders-disjoint-σ-sym : {σ1 : subst-env} {σ2 : subst-env} →
                                    hole-binders-disjoint-σ σ1 σ2 →
                                    hole-binders-disjoint-σ σ2 σ1
    σ-hole-binders-disjoint-σ-sym {σ2 = Id Γ} hbd = HBDσId
    σ-hole-binders-disjoint-σ-sym {σ2 = Subst d y σ2} hbd
      with lem-σ-hbd-σ-subst hbd
    ... | hbdd , hbdσ' =
      HBDσSubst (hole-binders-disjoint-σ-sym hbdd)
                (σ-hole-binders-disjoint-σ-sym hbdσ')

    rs-hole-binders-disjoint-σ-sym : {σ : subst-env} {rs : rules} →
                                     hole-binders-disjoint-σ σ rs →
                                     hole-binders-disjoint-rs rs σ
    rs-hole-binders-disjoint-σ-sym {rs = nil} hbd = HBDNoRules
    rs-hole-binders-disjoint-σ-sym {rs = r / rs} hbd
      with lem-rs-hbd-σ hbd
    ... | hbdr , hbdrs =
      HBDRules (r-hole-binders-disjoint-σ-sym hbdr)
               (rs-hole-binders-disjoint-σ-sym hbdrs)

    r-hole-binders-disjoint-σ-sym : {σ : subst-env} {r : rule} →
                                    hole-binders-disjoint-σ σ r →
                                    hole-binders-disjoint-r r σ
    r-hole-binders-disjoint-σ-sym {r = p => e} hbd
      with lem-r-hbd-σ hbd
    ... | hbdp , hbde =
      HBDRule (p-hole-binders-disjoint-σ-sym hbdp)
              (hole-binders-disjoint-σ-sym hbde)

    p-hole-binders-disjoint-σ-sym : {σ : subst-env} {p : pattrn} →
                                    hole-binders-disjoint-σ σ p →
                                    hole-binders-disjoint-p p σ
    p-hole-binders-disjoint-σ-sym {p = unit} hbd = HBDPUnit
    p-hole-binders-disjoint-σ-sym {p = N n} hbd = HBDPNum
    p-hole-binders-disjoint-σ-sym {p = X x} hbd = HBDPVar
    p-hole-binders-disjoint-σ-sym {p = inl p} hbd =
      HBDPInl (p-hole-binders-disjoint-σ-sym (lem-p-hbd-σ-inl hbd))
    p-hole-binders-disjoint-σ-sym {p = inr p} hbd =
      HBDPInr (p-hole-binders-disjoint-σ-sym (lem-p-hbd-σ-inr hbd))
    p-hole-binders-disjoint-σ-sym {p = ⟨ p1 , p2 ⟩} hbd
      with lem-p-hbd-σ-pair hbd
    ... | hbd1 , hbd2 =
      HBDPPair (p-hole-binders-disjoint-σ-sym hbd1)
              (p-hole-binders-disjoint-σ-sym hbd2)
    p-hole-binders-disjoint-σ-sym {p = wild} hbd = HBDPWild
    p-hole-binders-disjoint-σ-sym {p = ⦇-⦈[ w ]} hbd =
      HBDPEHole (lem-p-hbd-σ-ehole hbd)
    p-hole-binders-disjoint-σ-sym {p = ⦇⌜ p ⌟⦈[ w , τ ]} hbd
      with lem-p-hbd-σ-hole hbd
    ... | hub , hbd' =
      HBDPHole hub
                 (p-hole-binders-disjoint-σ-sym hbd')

  mutual
    hole-binders-disjoint-rs-sym : {rs : rules} {e : ihexp} →
                                   hole-binders-disjoint-rs rs e →
                                   hole-binders-disjoint e rs
    hole-binders-disjoint-rs-sym {e = unit} hbd = HBDUnit
    hole-binders-disjoint-rs-sym {e = N n} hbd = HBDNum
    hole-binders-disjoint-rs-sym {e = X x} hbd = HBDVar
    hole-binders-disjoint-rs-sym {e = ·λ x ·[ τ ] e} hbd =
      HBDLam (hole-binders-disjoint-rs-sym (lem-hbd-rs-lam hbd))
    hole-binders-disjoint-rs-sym {e = e1 ∘ e2} hbd
      with lem-hbd-rs-ap hbd
    ... | hbd1 , hbd2 =
      HBDAp (hole-binders-disjoint-rs-sym hbd1)
           (hole-binders-disjoint-rs-sym hbd2)
    hole-binders-disjoint-rs-sym {e = inl τ e} hbd =
      HBDInl (hole-binders-disjoint-rs-sym (lem-hbd-rs-inl hbd))
    hole-binders-disjoint-rs-sym {e = inr τ e} hbd =
      HBDInr (hole-binders-disjoint-rs-sym (lem-hbd-rs-inr hbd))
    hole-binders-disjoint-rs-sym {e = match e ·: τ of (rs-pre / r / rs-post)} hbd
      with lem-hbd-rs-match hbd
    ... | hbd' , hbdpre , hbdr , hbdpost =
      HBDMatch (hole-binders-disjoint-rs-sym hbd')
              (HBDZRules (rs-hole-binders-disjoint-rs-sym hbdpre)
                        (HBDRules (r-hole-binders-disjoint-rs-sym hbdr)
                                 (rs-hole-binders-disjoint-rs-sym hbdpost)))
    hole-binders-disjoint-rs-sym {e = ⟨ e1 , e2 ⟩} hbd
      with lem-hbd-rs-pair hbd
    ... | hbd1 , hbd2 =
      HBDPair (hole-binders-disjoint-rs-sym hbd1)
             (hole-binders-disjoint-rs-sym hbd2)
    hole-binders-disjoint-rs-sym {e = fst e} hbd =
      HBDFst (hole-binders-disjoint-rs-sym (lem-hbd-rs-fst hbd))
    hole-binders-disjoint-rs-sym {e = snd e} hbd =
      HBDSnd (hole-binders-disjoint-rs-sym (lem-hbd-rs-snd hbd))
    hole-binders-disjoint-rs-sym {e = ⦇-⦈⟨ u , σ ⟩} hbd =
      HBDEHole (σ-hole-binders-disjoint-rs-sym (lem-hbd-rs-ehole hbd))
    hole-binders-disjoint-rs-sym {e = ⦇⌜ e ⌟⦈⟨ u , σ ⟩} hbd
      with lem-hbd-rs-hole hbd
    ... | hbdσ , hbd' =
      HBDHole (σ-hole-binders-disjoint-rs-sym hbdσ)
               (hole-binders-disjoint-rs-sym hbd')

    σ-hole-binders-disjoint-rs-sym : {rs : rules} {σ : subst-env} →
                                     hole-binders-disjoint-rs rs σ →
                                     hole-binders-disjoint-σ σ rs
    σ-hole-binders-disjoint-rs-sym {σ = Id Γ} hbd = HBDσId
    σ-hole-binders-disjoint-rs-sym {σ = Subst d y σ} hbd
      with lem-σ-hbd-rs-subst hbd
    ... | hbd' , hbdσ = 
      HBDσSubst (hole-binders-disjoint-rs-sym hbd')
                (σ-hole-binders-disjoint-rs-sym hbdσ)

    rs-hole-binders-disjoint-rs-sym : {rs1 : rules} {rs2 : rules} →
                                      hole-binders-disjoint-rs rs1 rs2 →
                                      hole-binders-disjoint-rs rs2 rs1
    rs-hole-binders-disjoint-rs-sym {rs2 = nil} hbd = HBDNoRules
    rs-hole-binders-disjoint-rs-sym {rs2 = r2 / rs2} hbd
      with lem-rs-hbd-rs hbd
    ... | hbdr , hbdrs =
      HBDRules (r-hole-binders-disjoint-rs-sym hbdr)
               (rs-hole-binders-disjoint-rs-sym hbdrs)

    r-hole-binders-disjoint-rs-sym : {rs : rules} {r : rule} →
                                     hole-binders-disjoint-rs rs r →
                                     hole-binders-disjoint-r r rs
    r-hole-binders-disjoint-rs-sym {r = p => e} hbd
      with lem-r-hbd-rs hbd
    ... | hbdp , hbde =
      HBDRule (p-hole-binders-disjoint-rs-sym hbdp)
              (hole-binders-disjoint-rs-sym hbde)

    p-hole-binders-disjoint-rs-sym : {rs : rules} {p : pattrn} →
                                     hole-binders-disjoint-rs rs p →
                                     hole-binders-disjoint-p p rs
    p-hole-binders-disjoint-rs-sym {p = unit} hbd = HBDPUnit
    p-hole-binders-disjoint-rs-sym {p = N n} hbd = HBDPNum
    p-hole-binders-disjoint-rs-sym {p = X x} hbd = HBDPVar
    p-hole-binders-disjoint-rs-sym {p = inl p} hbd =
      HBDPInl (p-hole-binders-disjoint-rs-sym (lem-p-hbd-rs-inl hbd))
    p-hole-binders-disjoint-rs-sym {p = inr p} hbd =
      HBDPInr (p-hole-binders-disjoint-rs-sym (lem-p-hbd-rs-inr hbd))
    p-hole-binders-disjoint-rs-sym {p = ⟨ p1 , p2 ⟩} hbd
      with lem-p-hbd-rs-pair hbd
    ... | hbd1 , hbd2 =
      HBDPPair (p-hole-binders-disjoint-rs-sym hbd1)
               (p-hole-binders-disjoint-rs-sym hbd2)
    p-hole-binders-disjoint-rs-sym {p = wild} hbd = HBDPWild
    p-hole-binders-disjoint-rs-sym {p = ⦇-⦈[ w ]} hbd =
      HBDPEHole (lem-p-hbd-rs-ehole hbd)
    p-hole-binders-disjoint-rs-sym {p = ⦇⌜ p ⌟⦈[ w , τ ]} hbd
      with lem-p-hbd-rs-hole hbd
    ... | hub , hbd' =
      HBDPHole hub
                 (p-hole-binders-disjoint-rs-sym hbd')

  mutual
    hole-binders-disjoint-r-sym : {r : rule} {e : ihexp} →
                                  hole-binders-disjoint-r r e →
                                  hole-binders-disjoint e r
    hole-binders-disjoint-r-sym {e = unit} hbd = HBDUnit
    hole-binders-disjoint-r-sym {e = N n} hbd = HBDNum
    hole-binders-disjoint-r-sym {e = X x} hbd = HBDVar
    hole-binders-disjoint-r-sym {e = ·λ x ·[ τ ] e} hbd =
      HBDLam (hole-binders-disjoint-r-sym (lem-hbd-r-lam hbd))
    hole-binders-disjoint-r-sym {e = e1 ∘ e2} hbd
      with lem-hbd-r-ap hbd
    ... | hbd1 , hbd2 =
      HBDAp (hole-binders-disjoint-r-sym hbd1)
            (hole-binders-disjoint-r-sym hbd2)
    hole-binders-disjoint-r-sym {e = inl τ e} hbd =
      HBDInl (hole-binders-disjoint-r-sym (lem-hbd-r-inl hbd))
    hole-binders-disjoint-r-sym {e = inr τ e} hbd =
      HBDInr (hole-binders-disjoint-r-sym (lem-hbd-r-inr hbd))
    hole-binders-disjoint-r-sym {e = match e ·: τ of (rs-pre / r / rs-post)} hbd
      with lem-hbd-r-match hbd
    ... | hbd' , hbdpre , hbdr , hbdpost =
      HBDMatch (hole-binders-disjoint-r-sym hbd')
               (HBDZRules (rs-hole-binders-disjoint-r-sym hbdpre)
                          (HBDRules (r-hole-binders-disjoint-r-sym hbdr)
                                    (rs-hole-binders-disjoint-r-sym hbdpost)))
    hole-binders-disjoint-r-sym {e = ⟨ e1 , e2 ⟩} hbd
      with lem-hbd-r-pair hbd
    ... | hbd1 , hbd2 =
      HBDPair (hole-binders-disjoint-r-sym hbd1)
             (hole-binders-disjoint-r-sym hbd2)
    hole-binders-disjoint-r-sym {e = fst e} hbd =
      HBDFst (hole-binders-disjoint-r-sym (lem-hbd-r-fst hbd))
    hole-binders-disjoint-r-sym {e = snd e} hbd =
      HBDSnd (hole-binders-disjoint-r-sym (lem-hbd-r-snd hbd))
    hole-binders-disjoint-r-sym {e = ⦇-⦈⟨ u , σ ⟩} hbd =
      HBDEHole (σ-hole-binders-disjoint-r-sym (lem-hbd-r-ehole hbd))
    hole-binders-disjoint-r-sym {e = ⦇⌜ e ⌟⦈⟨ u , σ ⟩} hbd
      with lem-hbd-r-hole hbd
    ... | hbdσ , hbd' =
      HBDHole (σ-hole-binders-disjoint-r-sym hbdσ)
                (hole-binders-disjoint-r-sym hbd')

    σ-hole-binders-disjoint-r-sym : {r : rule} {σ : subst-env} →
                                    hole-binders-disjoint-r r σ →
                                    hole-binders-disjoint-σ σ r
    σ-hole-binders-disjoint-r-sym {σ = Id Γ} hbd = HBDσId
    σ-hole-binders-disjoint-r-sym {σ = Subst d y σ} hbd
      with lem-σ-hbd-r-subst hbd
    ... | hbd' , hbdσ =
      HBDσSubst (hole-binders-disjoint-r-sym hbd')
                (σ-hole-binders-disjoint-r-sym hbdσ)

    rs-hole-binders-disjoint-r-sym : {r : rule} {rs : rules} →
                                     hole-binders-disjoint-r r rs →
                                     hole-binders-disjoint-rs rs r
    rs-hole-binders-disjoint-r-sym {rs = nil} hbd = HBDNoRules
    rs-hole-binders-disjoint-r-sym {rs = r / rs} hbd
      with lem-rs-hbd-r hbd
    ... | hbdr , hbdrs =
      HBDRules (r-hole-binders-disjoint-r-sym hbdr)
               (rs-hole-binders-disjoint-r-sym hbdrs)

    r-hole-binders-disjoint-r-sym : {r1 : rule} {r2 : rule} →
                                    hole-binders-disjoint-r r1 r2 →
                                    hole-binders-disjoint-r r2 r1
    r-hole-binders-disjoint-r-sym {r2 = p => e} hbd
      with lem-r-hbd-r hbd
    ... | hbdp , hbde =
      HBDRule (p-hole-binders-disjoint-r-sym hbdp)
              (hole-binders-disjoint-r-sym hbde)

    p-hole-binders-disjoint-r-sym : {r : rule} {p : pattrn} →
                                    hole-binders-disjoint-r r p →
                                    hole-binders-disjoint-p p r
    p-hole-binders-disjoint-r-sym {p = unit} hbd = HBDPUnit
    p-hole-binders-disjoint-r-sym {p = N n} hbd = HBDPNum
    p-hole-binders-disjoint-r-sym {p = X x} hbd = HBDPVar
    p-hole-binders-disjoint-r-sym {p = inl p} hbd =
      HBDPInl (p-hole-binders-disjoint-r-sym (lem-p-hbd-r-inl hbd))
    p-hole-binders-disjoint-r-sym {p = inr p} hbd =
      HBDPInr (p-hole-binders-disjoint-r-sym (lem-p-hbd-r-inr hbd))
    p-hole-binders-disjoint-r-sym {p = ⟨ p1 , p2 ⟩} hbd
      with lem-p-hbd-r-pair hbd
    ... | hbd1 , hbd2 =
      HBDPPair (p-hole-binders-disjoint-r-sym hbd1)
              (p-hole-binders-disjoint-r-sym hbd2)
    p-hole-binders-disjoint-r-sym {p = wild} hbd = HBDPWild
    p-hole-binders-disjoint-r-sym {p = ⦇-⦈[ w ]} hbd =
      HBDPEHole (lem-p-hbd-r-ehole hbd)
    p-hole-binders-disjoint-r-sym {p = ⦇⌜ p ⌟⦈[ w , τ ]} hbd
      with lem-p-hbd-r-hole hbd
    ... | hub , hbd' =
      HBDPHole hub
                 (p-hole-binders-disjoint-r-sym hbd')
    
  mutual
    hole-binders-disjoint-p-sym : {p : pattrn} {e : ihexp} →
                                  hole-binders-disjoint-p p e →
                                  hole-binders-disjoint e p
    hole-binders-disjoint-p-sym {e = unit} hbd = HBDUnit
    hole-binders-disjoint-p-sym {e = N n} hbd = HBDNum
    hole-binders-disjoint-p-sym {e = X x} hbd = HBDVar
    hole-binders-disjoint-p-sym {e = ·λ x ·[ τ ] e} hbd =
      HBDLam (hole-binders-disjoint-p-sym (lem-hbd-p-lam hbd))
    hole-binders-disjoint-p-sym {e = e1 ∘ e2} hbd
      with lem-hbd-p-ap hbd
    ... | hbd1 , hbd2 =
      HBDAp (hole-binders-disjoint-p-sym hbd1)
           (hole-binders-disjoint-p-sym hbd2)
    hole-binders-disjoint-p-sym {e = inl τ e} hbd =
      HBDInl (hole-binders-disjoint-p-sym (lem-hbd-p-inl hbd))
    hole-binders-disjoint-p-sym {e = inr τ e} hbd =
      HBDInr (hole-binders-disjoint-p-sym (lem-hbd-p-inr hbd))
    hole-binders-disjoint-p-sym {e = match e ·: τ of (rs-pre / r / rs-post)} hbd
      with lem-hbd-p-match hbd
    ... | hbd' , hbdpre , hbdr , hbdpost =
      HBDMatch (hole-binders-disjoint-p-sym hbd')
               (HBDZRules (rs-hole-binders-disjoint-p-sym hbdpre)
                          (HBDRules (r-hole-binders-disjoint-p-sym hbdr)
                                    (rs-hole-binders-disjoint-p-sym hbdpost)))
    hole-binders-disjoint-p-sym {e = ⟨ e1 , e2 ⟩} hbd
      with lem-hbd-p-pair hbd
    ... | hbd1 , hbd2 =
      HBDPair (hole-binders-disjoint-p-sym hbd1)
             (hole-binders-disjoint-p-sym hbd2)
    hole-binders-disjoint-p-sym {e = fst e} hbd =
      HBDFst (hole-binders-disjoint-p-sym (lem-hbd-p-fst hbd))
    hole-binders-disjoint-p-sym {e = snd e} hbd =
      HBDSnd (hole-binders-disjoint-p-sym (lem-hbd-p-snd hbd))
    hole-binders-disjoint-p-sym {e = ⦇-⦈⟨ u , σ ⟩} hbd =
      HBDEHole (σ-hole-binders-disjoint-p-sym (lem-hbd-p-ehole hbd))
    hole-binders-disjoint-p-sym {e = ⦇⌜ e ⌟⦈⟨ u , σ ⟩} hbd
      with lem-hbd-p-hole hbd
    ... | hbdσ , hbd' =
      HBDHole (σ-hole-binders-disjoint-p-sym hbdσ)
               (hole-binders-disjoint-p-sym hbd')

    σ-hole-binders-disjoint-p-sym : {p : pattrn} {σ : subst-env} →
                                    hole-binders-disjoint-p p σ →
                                    hole-binders-disjoint-σ σ p
    σ-hole-binders-disjoint-p-sym {σ = Id Γ} hbd = HBDσId
    σ-hole-binders-disjoint-p-sym {σ = Subst d y σ} hbd
      with lem-σ-hbd-p-subst hbd
    ... | hbd' , hbdσ =
      HBDσSubst (hole-binders-disjoint-p-sym hbd')
                (σ-hole-binders-disjoint-p-sym hbdσ)

    rs-hole-binders-disjoint-p-sym : {p : pattrn} {rs : rules} →
                                     hole-binders-disjoint-p p rs →
                                     hole-binders-disjoint-rs rs p
    rs-hole-binders-disjoint-p-sym {rs = nil} hbd = HBDNoRules
    rs-hole-binders-disjoint-p-sym {rs = r / rs} hbd
      with lem-rs-hbd-p hbd
    ... | hbdr , hbdrs =
      HBDRules (r-hole-binders-disjoint-p-sym hbdr)
               (rs-hole-binders-disjoint-p-sym hbdrs)
    
    r-hole-binders-disjoint-p-sym : {p : pattrn} {r : rule} →
                                    hole-binders-disjoint-p p r →
                                    hole-binders-disjoint-r r p
    r-hole-binders-disjoint-p-sym {r = pr => er} hbd
      with lem-r-hbd-p hbd
    ... | hbdp , hbde =
      HBDRule (p-hole-binders-disjoint-p-sym hbdp)
              (hole-binders-disjoint-p-sym hbde)

    p-hole-binders-disjoint-p-sym : {p1 : pattrn} {p2 : pattrn} →
                                    hole-binders-disjoint-p p1 p2 →
                                    hole-binders-disjoint-p p2 p1
    p-hole-binders-disjoint-p-sym {p2 = unit} hbd = HBDPUnit
    p-hole-binders-disjoint-p-sym {p2 = N n} hbd = HBDPNum
    p-hole-binders-disjoint-p-sym {p2 = X x} hbd = HBDPVar
    p-hole-binders-disjoint-p-sym {p2 = inl p2} hbd =
      HBDPInl (p-hole-binders-disjoint-p-sym (lem-p-hbd-p-inl hbd))
    p-hole-binders-disjoint-p-sym {p2 = inr p2} hbd =
      HBDPInr (p-hole-binders-disjoint-p-sym (lem-p-hbd-p-inr hbd))
    p-hole-binders-disjoint-p-sym {p2 = ⟨ p2₁ , p2₂ ⟩} hbd
      with lem-p-hbd-p-pair hbd
    ... | hbd1 , hbd2 =
      HBDPPair (p-hole-binders-disjoint-p-sym hbd1)
               (p-hole-binders-disjoint-p-sym hbd2)
    p-hole-binders-disjoint-p-sym {p2 = wild} hbd = HBDPWild
    p-hole-binders-disjoint-p-sym {p2 = ⦇-⦈[ w ]} hbd =
      HBDPEHole (lem-p-hbd-p-ehole hbd)
    p-hole-binders-disjoint-p-sym {p2 = ⦇⌜ p2 ⌟⦈[ w , τ ]} hbd
      with lem-p-hbd-p-hole hbd
    ... | hub , hbd' =
      HBDPHole hub
                 (p-hole-binders-disjoint-p-sym hbd')
