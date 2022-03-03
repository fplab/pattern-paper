open import List
open import Nat
open import Prelude
open import binders-disjointness
open import contexts
open import core
open import freshness
open import lemmas-contexts
open import patterns-core

module binders-disjoint-symmetric where
  -- these lemmas build up to proving that the various
  -- disjointness judgements are symmetric.
  --
  -- more specifically, the definitions of the disjointness
  -- judgements deconstruct on the first argument, while
  -- leaving the second argument generic. these lemmas
  -- show that you can instead deconstruct on the second
  -- arugment. all of these results are entirely mechanical,
  -- but horribly tedious.
  mutual
    lem-bd-lam : {e : ihexp} {x : Nat} {τ1 : htyp} {e1 : ihexp} →
                 binders-disjoint e (·λ x ·[ τ1 ] e1) →
                 unbound-in-e x e ×
                   binders-disjoint e e1
    lem-bd-lam BDUnit = UBUnit , BDUnit
    lem-bd-lam BDNum = UBNum , BDNum 
    lem-bd-lam BDVar = UBVar , BDVar
    lem-bd-lam (BDLam (UBLam x≠y ub) bd)
      with lem-bd-lam bd
    ... | ub' , bd' =
      UBLam (flip x≠y) ub' , BDLam ub bd'
    lem-bd-lam (BDAp bd1 bd2)
      with lem-bd-lam bd1 | lem-bd-lam bd2
    ... | ub1 , bd1' | ub2 , bd2' =
      UBAp ub1 ub2 , BDAp bd1' bd2'
    lem-bd-lam (BDInl bd)
      with lem-bd-lam bd
    ... | ub , bd' = UBInl ub , BDInl bd' 
    lem-bd-lam (BDInr bd)
      with lem-bd-lam bd
    ... | ub , bd' = UBInr ub , BDInr bd'
    lem-bd-lam (BDMatch bd (BDZRules bdpre bdpost))
      with lem-bd-lam bd |
           lem-bd-rs-lam bdpre |
           lem-bd-rs-lam bdpost
    ... | ub , bd'
        | ubpre , bdpre' 
        | ubpost , bdpost'  = 
      UBMatch ub (UBZRules ubpre ubpost) ,
        BDMatch bd' (BDZRules bdpre' bdpost')
    lem-bd-lam (BDPair bd1 bd2)
      with lem-bd-lam bd1 | lem-bd-lam bd2
    ... | ub1 , bd1'  | ub2 , bd2' =
      UBPair ub1 ub2 , BDPair bd1' bd2'
    lem-bd-lam (BDFst bd)
      with lem-bd-lam bd
    ... | ub , bd' =  UBFst ub , BDFst bd'
    lem-bd-lam (BDSnd bd)
      with lem-bd-lam bd
    ... | ub , bd' = UBSnd ub , BDSnd bd'
    lem-bd-lam (BDEHole bdσ)
      with lem-bd-σ-lam bdσ
    ... | ubσ , bdσ' = UBEHole ubσ , BDEHole bdσ'
    lem-bd-lam (BDHole bdσ bd)
      with lem-bd-σ-lam bdσ | lem-bd-lam bd
    ... | ubσ , bdσ' | ub , bd' =
      UBHole ubσ ub , BDHole bdσ' bd'

    lem-bd-σ-lam : {σ : subst-env} {x : Nat} {τ1 : htyp} {e1 : ihexp} →
                   binders-disjoint-σ σ (·λ x ·[ τ1 ] e1) →
                   unbound-in-σ x σ ×
                     binders-disjoint-σ σ e1
    lem-bd-σ-lam BDσId = UBσId , BDσId
    lem-bd-σ-lam (BDσSubst bd (UBLam y≠x ub) bdσ)
      with lem-bd-lam bd | lem-bd-σ-lam bdσ
    ... | ub' , bd' | ubσ , bdσ' =
      UBσSubst ub' (flip y≠x) ubσ , BDσSubst bd' ub bdσ'
    
    lem-bd-rs-lam : {rs : rules} {x : Nat} {τ1 : htyp} {e1 : ihexp} →
                    binders-disjoint-rs rs (·λ x ·[ τ1 ] e1) →
                    unbound-in-rs x rs ×
                      binders-disjoint-rs rs e1
    lem-bd-rs-lam BDNoRules = UBNoRules , BDNoRules
    lem-bd-rs-lam (BDRules bdr bdrs)
      with lem-bd-r-lam bdr | lem-bd-rs-lam bdrs
    ... | ubr , bdr' | ubrs , bdrs' =
      UBRules ubr ubrs , BDRules bdr' bdrs'

    lem-bd-r-lam : {r : rule} {x : Nat} {τ1 : htyp} {e1 : ihexp} →
                   binders-disjoint-r r (·λ x ·[ τ1 ] e1) →
                   unbound-in-r x r ×
                     binders-disjoint-r r e1
    lem-bd-r-lam (BDRule bdp bd)
      with lem-bd-p-lam bdp | lem-bd-lam bd
    ... | ubp , bdp' | ub , bd' =
      UBRule ubp ub , BDRule bdp' bd'

    lem-bd-p-lam : {p : pattrn} {x : Nat} {τ1 : htyp} {e1 : ihexp} →
                   binders-disjoint-p p (·λ x ·[ τ1 ] e1) →
                   unbound-in-p x p ×
                     binders-disjoint-p p e1
    lem-bd-p-lam BDPUnit = UBPUnit , BDPUnit
    lem-bd-p-lam BDPNum = UBPNum , BDPNum 
    lem-bd-p-lam (BDPVar (UBLam x≠y ub)) =
      UBPVar (flip x≠y) , BDPVar ub
    lem-bd-p-lam (BDPInl bd)
      with lem-bd-p-lam bd
    ... | ub , bd' = UBPInl ub , BDPInl bd'
    lem-bd-p-lam (BDPInr bd)
      with lem-bd-p-lam bd
    ... | ub , bd' = UBPInr ub , BDPInr bd'
    lem-bd-p-lam (BDPPair bd1 bd2)
      with lem-bd-p-lam bd1 | lem-bd-p-lam bd2
    ... | ub1 , bd1' | ub2 , bd2' =
      UBPPair ub1 ub2 , BDPPair bd1' bd2'
    lem-bd-p-lam BDPWild = UBPWild , BDPWild
    lem-bd-p-lam BDPEHole = UBPEHole , BDPEHole
    lem-bd-p-lam (BDPHole bd)
      with lem-bd-p-lam bd
    ... | ub , bd' = UBPHole ub , BDPHole bd'
    
  mutual
    lem-bd-ap : {e : ihexp} {e1 e2 : ihexp} →
                binders-disjoint e (e1 ∘ e2) →
                binders-disjoint e e1 ×
                  binders-disjoint e e2
    lem-bd-ap BDUnit = BDUnit , BDUnit
    lem-bd-ap BDNum = BDNum , BDNum
    lem-bd-ap BDVar = BDVar , BDVar
    lem-bd-ap (BDLam (UBAp ub1 ub2) bd)
      with lem-bd-ap bd
    ... | bd1 , bd2 = BDLam ub1 bd1 , BDLam ub2 bd2
    lem-bd-ap (BDAp bd1 bd2)
      with lem-bd-ap bd1 | lem-bd-ap bd2
    ... | bd1₁ , bd1₂ | bd2₁ , bd2₂ =
      BDAp bd1₁ bd2₁ , BDAp bd1₂ bd2₂
    lem-bd-ap (BDInl bd)
      with lem-bd-ap bd
    ... | bd1 , bd2 = BDInl bd1 , BDInl bd2
    lem-bd-ap (BDInr bd)
      with lem-bd-ap bd
    ... | bd1 , bd2 = BDInr bd1 , BDInr bd2
    lem-bd-ap (BDMatch bd (BDZRules pret postt))
      with lem-bd-ap bd |
           lem-bd-rs-ap pret |
           lem-bd-rs-ap postt
    ... | bd1 , bd2 
        |  bdpre1 , bdpre2
        | bdpost1 , bdpost2 =
      BDMatch bd1 (BDZRules bdpre1 bdpost1) ,
      BDMatch bd2 (BDZRules bdpre2 bdpost2)
    lem-bd-ap (BDPair bd1 bd2)
      with lem-bd-ap bd1 | lem-bd-ap bd2
    ... | bd1₁ , bd1₂ | bd2₁ , bd2₂ =
      BDPair bd1₁ bd2₁ , BDPair bd1₂ bd2₂
    lem-bd-ap (BDFst bd)
      with lem-bd-ap bd
    ... | bd1 , bd2 = BDFst bd1 , BDFst bd2
    lem-bd-ap (BDSnd bd)
      with lem-bd-ap bd
    ... | bd1 , bd2 = BDSnd bd1 , BDSnd bd2
    lem-bd-ap (BDEHole bdσ)
      with lem-bd-σ-ap bdσ
    ... | bdσ1 , bdσ2 =
      BDEHole bdσ1 , BDEHole bdσ2
    lem-bd-ap (BDHole bdσ bd)
      with lem-bd-σ-ap bdσ | lem-bd-ap bd
    ... | bdσ1 , bdσ2 | bd1 , bd2 =
      BDHole bdσ1 bd1 , BDHole bdσ2 bd2

    lem-bd-σ-ap : {σ : subst-env} {e1 e2 : ihexp} →
                  binders-disjoint-σ σ (e1 ∘ e2) →
                  binders-disjoint-σ σ e1 ×
                    binders-disjoint-σ σ e2
    lem-bd-σ-ap BDσId = BDσId , BDσId
    lem-bd-σ-ap (BDσSubst bd (UBAp ub1 ub2) bdσ)
      with lem-bd-ap bd | lem-bd-σ-ap bdσ
    ... | bd1 , bd2 | bdσ1 , bdσ2 =
      BDσSubst bd1 ub1 bdσ1 , BDσSubst bd2 ub2 bdσ2
    
    lem-bd-rs-ap : {rs : rules} {e1 e2 : ihexp} →
                   binders-disjoint-rs rs (e1 ∘ e2) →
                   binders-disjoint-rs rs e1 ×
                     binders-disjoint-rs rs e2
    lem-bd-rs-ap BDNoRules = BDNoRules , BDNoRules
    lem-bd-rs-ap (BDRules bdr bdrs)
      with lem-bd-r-ap bdr | lem-bd-rs-ap bdrs
    ... | bdr1 , bdr2 | bd1 , bd2 =
      BDRules bdr1 bd1 , BDRules bdr2 bd2
      
    lem-bd-r-ap : {r : rule} {e1 e2 : ihexp} →
                  binders-disjoint-r r (e1 ∘ e2) →
                  binders-disjoint-r r e1 ×
                    binders-disjoint-r r e2
    lem-bd-r-ap (BDRule pt bd)
      with lem-bd-p-ap pt | lem-bd-ap bd
    ... | pt1 , pt2 | bd1 , bd2 =
      BDRule pt1 bd1 , BDRule pt2 bd2

    lem-bd-p-ap : {p : pattrn} {e1 e2 : ihexp} →
                  binders-disjoint-p p (e1 ∘ e2) →
                  binders-disjoint-p p e1 ×
                    binders-disjoint-p p e2
    lem-bd-p-ap BDPUnit = BDPUnit , BDPUnit
    lem-bd-p-ap BDPNum = BDPNum , BDPNum
    lem-bd-p-ap (BDPVar (UBAp ub1 ub2)) =
      BDPVar ub1 , BDPVar ub2
    lem-bd-p-ap (BDPInl bd)
      with lem-bd-p-ap bd
    ... | bd1 , bd2 = BDPInl bd1 , BDPInl bd2
    lem-bd-p-ap (BDPInr bd)
      with lem-bd-p-ap bd
    ... | bd1 , bd2 = BDPInr bd1 , BDPInr bd2
    lem-bd-p-ap (BDPPair bd1 bd2)
      with lem-bd-p-ap bd1 | lem-bd-p-ap bd2
    ... | bd1₁ , bd1₂ | bd2₁ , bd2₂ =
      BDPPair bd1₁ bd2₁ , BDPPair bd1₂ bd2₂
    lem-bd-p-ap BDPWild = BDPWild , BDPWild
    lem-bd-p-ap BDPEHole = BDPEHole , BDPEHole
    lem-bd-p-ap (BDPHole bd)
      with lem-bd-p-ap bd
    ... | bd1 , bd2 = BDPHole bd1 , BDPHole bd2

  mutual
    lem-bd-inl : {e : ihexp} {τ : htyp} {e1 : ihexp} →
                 binders-disjoint e (inl τ e1) →
                 binders-disjoint e e1
    lem-bd-inl BDUnit = BDUnit
    lem-bd-inl BDNum = BDNum
    lem-bd-inl BDVar = BDVar
    lem-bd-inl (BDLam (UBInl ub) bd) =
      BDLam ub (lem-bd-inl bd)
    lem-bd-inl (BDAp bd1 bd2) =
      BDAp (lem-bd-inl bd1) (lem-bd-inl bd2)
    lem-bd-inl (BDInl bd) = BDInl (lem-bd-inl bd)
    lem-bd-inl (BDInr bd) = BDInr (lem-bd-inl bd)
    lem-bd-inl (BDMatch bd (BDZRules bdpre bdpost)) =
      BDMatch (lem-bd-inl bd)
              (BDZRules (lem-bd-rs-inl bdpre)
                        (lem-bd-rs-inl bdpost))
    lem-bd-inl (BDPair bd1 bd2) =
      BDPair (lem-bd-inl bd1) (lem-bd-inl bd2)
    lem-bd-inl (BDFst bd) = BDFst (lem-bd-inl bd)
    lem-bd-inl (BDSnd bd) = BDSnd (lem-bd-inl bd)
    lem-bd-inl (BDEHole bdσ) = BDEHole (lem-bd-σ-inl bdσ)
    lem-bd-inl (BDHole bdσ bd) =
      BDHole (lem-bd-σ-inl bdσ)
               (lem-bd-inl bd)

    lem-bd-σ-inl : {σ : subst-env} {τ : htyp} {e1 : ihexp} →
                   binders-disjoint-σ σ (inl τ e1) →
                   binders-disjoint-σ σ e1
    lem-bd-σ-inl BDσId = BDσId
    lem-bd-σ-inl (BDσSubst bd (UBInl ub) bdσ) =
      BDσSubst (lem-bd-inl bd) ub (lem-bd-σ-inl bdσ)
                   
    lem-bd-rs-inl : {rs : rules} {τ : htyp} {e1 : ihexp} →
                    binders-disjoint-rs rs (inl τ e1) →
                    binders-disjoint-rs rs e1
    lem-bd-rs-inl BDNoRules = BDNoRules
    lem-bd-rs-inl (BDRules bdr bdrs) =
      BDRules (lem-bd-r-inl bdr) (lem-bd-rs-inl bdrs)

    lem-bd-r-inl : {r : rule} {τ : htyp} {e1 : ihexp} →
                   binders-disjoint-r r (inl τ e1) →
                   binders-disjoint-r r e1
    lem-bd-r-inl (BDRule bdp bd) =
      BDRule (lem-bd-p-inl bdp) (lem-bd-inl bd)

    lem-bd-p-inl : {p : pattrn} {τ : htyp} {e1 : ihexp} →
                   binders-disjoint-p p (inl τ e1) →
                   binders-disjoint-p p e1
    lem-bd-p-inl BDPUnit = BDPUnit
    lem-bd-p-inl BDPNum = BDPNum
    lem-bd-p-inl (BDPVar (UBInl ub)) = BDPVar ub
    lem-bd-p-inl (BDPInl bd) = BDPInl (lem-bd-p-inl bd)
    lem-bd-p-inl (BDPInr bd) = BDPInr (lem-bd-p-inl bd)
    lem-bd-p-inl (BDPPair bd1 bd2) =
      BDPPair (lem-bd-p-inl bd1) (lem-bd-p-inl bd2)
    lem-bd-p-inl BDPWild = BDPWild
    lem-bd-p-inl BDPEHole = BDPEHole
    lem-bd-p-inl (BDPHole bd) =
      BDPHole (lem-bd-p-inl bd)
    
  mutual
    lem-bd-inr : {e : ihexp} {τ : htyp} {e1 : ihexp} →
                 binders-disjoint e (inr τ e1) →
                 binders-disjoint e e1
    lem-bd-inr BDUnit = BDUnit
    lem-bd-inr BDNum = BDNum
    lem-bd-inr BDVar = BDVar
    lem-bd-inr (BDLam (UBInr ub) bd) =
      BDLam ub (lem-bd-inr bd)
    lem-bd-inr (BDAp bd1 bd2) =
      BDAp (lem-bd-inr bd1) (lem-bd-inr bd2)
    lem-bd-inr (BDInl bd) = BDInl (lem-bd-inr bd)
    lem-bd-inr (BDInr bd) = BDInr (lem-bd-inr bd)
    lem-bd-inr (BDMatch bd (BDZRules bdpre bdpost)) =
      BDMatch (lem-bd-inr bd)
              (BDZRules (lem-bd-rs-inr bdpre)
                        (lem-bd-rs-inr bdpost))
    lem-bd-inr (BDPair bd1 bd2) =
      BDPair (lem-bd-inr bd1) (lem-bd-inr bd2)
    lem-bd-inr (BDFst bd) = BDFst (lem-bd-inr bd)
    lem-bd-inr (BDSnd bd) = BDSnd (lem-bd-inr bd)
    lem-bd-inr (BDEHole bdσ) =
      BDEHole (lem-bd-σ-inr bdσ)
    lem-bd-inr (BDHole bdσ bd) =
      BDHole (lem-bd-σ-inr bdσ) (lem-bd-inr bd)

    lem-bd-σ-inr : {σ : subst-env} {τ : htyp} {e1 : ihexp} →
                   binders-disjoint-σ σ (inr τ e1) →
                   binders-disjoint-σ σ e1
    lem-bd-σ-inr BDσId = BDσId
    lem-bd-σ-inr (BDσSubst bd (UBInr ub) bdσ) =
      BDσSubst (lem-bd-inr bd) ub (lem-bd-σ-inr bdσ)
    
    lem-bd-rs-inr : {rs : rules} {τ : htyp} {e1 : ihexp} →
                    binders-disjoint-rs rs (inr τ e1) →
                    binders-disjoint-rs rs e1
    lem-bd-rs-inr BDNoRules = BDNoRules
    lem-bd-rs-inr (BDRules bdr bdrs) =
      BDRules (lem-bd-r-inr bdr) (lem-bd-rs-inr bdrs)

    lem-bd-r-inr : {r : rule} {τ : htyp} {e1 : ihexp}  →
                   binders-disjoint-r r (inr τ e1) →
                   binders-disjoint-r r e1
    lem-bd-r-inr (BDRule bdp bd) =
      BDRule (lem-bd-p-inr bdp) (lem-bd-inr bd)

    lem-bd-p-inr : {p : pattrn} {τ : htyp} {e1 : ihexp} →
                   binders-disjoint-p p (inr τ e1) →
                   binders-disjoint-p p e1
    lem-bd-p-inr BDPUnit = BDPUnit
    lem-bd-p-inr BDPNum = BDPNum
    lem-bd-p-inr (BDPVar (UBInr ub)) = BDPVar ub
    lem-bd-p-inr (BDPInl bd) = BDPInl (lem-bd-p-inr bd)
    lem-bd-p-inr (BDPInr bd) = BDPInr (lem-bd-p-inr bd)
    lem-bd-p-inr (BDPPair bd1 bd2) =
      BDPPair (lem-bd-p-inr bd1) (lem-bd-p-inr bd2)
    lem-bd-p-inr BDPWild = BDPWild
    lem-bd-p-inr BDPEHole = BDPEHole
    lem-bd-p-inr (BDPHole bd) =
      BDPHole (lem-bd-p-inr bd)
    
  mutual
    lem-bd-match : {e : ihexp} {e1 : ihexp} {τ : htyp}
                   {rs-pre : rules} {r : rule} {rs-post : rules} →
                   binders-disjoint e
                     (match e1 ·: τ of (rs-pre / r / rs-post)) →
                   binders-disjoint e e1 ×
                     binders-disjoint e rs-pre ×
                       binders-disjoint e r ×
                         binders-disjoint e rs-post
    lem-bd-match BDUnit = BDUnit , BDUnit , BDUnit , BDUnit
    lem-bd-match BDNum = BDNum , BDNum , BDNum , BDNum
    lem-bd-match BDVar = BDVar , BDVar , BDVar , BDVar
    lem-bd-match (BDLam (UBMatch ub
                                 (UBZRules ubpre (UBRules ubr ubpost)))
                 bd)
      with lem-bd-match bd
    ... | bd' , bdpre , bdr , bdpost =
      BDLam ub bd' ,
      BDLam ubpre bdpre ,
      BDLam ubr bdr ,
      BDLam ubpost bdpost
    lem-bd-match (BDAp bd1 bd2)
      with lem-bd-match bd1 | lem-bd-match bd2
    ... | bd1' , bdpre1 , bdr1 , bdpost1 |
          bd2' , bdpre2 , bdr2 , bdpost2 =
      BDAp bd1' bd2' ,
      BDAp bdpre1 bdpre2 ,
      BDAp bdr1 bdr2 ,
      BDAp bdpost1 bdpost2 
    lem-bd-match (BDInl bd)
      with lem-bd-match bd
    ... | bd' , bdpre , bdr , bdpost =
      BDInl bd' , BDInl bdpre , BDInl bdr , BDInl bdpost
    lem-bd-match (BDInr bd)
      with lem-bd-match bd
    ... | bd' , bdpre , bdr , bdpost =
      BDInr bd' , BDInr bdpre , BDInr bdr , BDInr bdpost
    lem-bd-match (BDMatch bd (BDZRules bdpre bdpost))
      with lem-bd-match bd |
           lem-bd-rs-match bdpre |
           lem-bd-rs-match bdpost
    ... | bd' , bdpre , bdr , bdpost
        | bdpre' , bdprepre , bdprer , bdprepost
        | bdpost' , bdpostpre , bdpostr , bdpostpost =
      BDMatch bd' (BDZRules bdpre' bdpost') ,
      BDMatch bdpre (BDZRules bdprepre bdpostpre) ,
      BDMatch bdr (BDZRules bdprer bdpostr) ,
      BDMatch bdpost (BDZRules bdprepost bdpostpost)
    lem-bd-match (BDPair bd1 bd2)
      with lem-bd-match bd1 | lem-bd-match bd2
    ... | bd1' , bdpre1 , bdr1 , bdpost1 |
          bd2' , bdpre2 , bdr2 , bdpost2 =
      BDPair bd1' bd2' ,
      BDPair bdpre1 bdpre2 ,
      BDPair bdr1 bdr2 ,
      BDPair bdpost1 bdpost2 
    lem-bd-match (BDFst bd)
      with lem-bd-match bd
    ... | bd' , bdpre , bdr , bdpost =
      BDFst bd' , BDFst bdpre , BDFst bdr , BDFst bdpost
    lem-bd-match (BDSnd bd)
      with lem-bd-match bd
    ... | bd' , bdpre , bdr , bdpost =
      BDSnd bd' , BDSnd bdpre , BDSnd bdr , BDSnd bdpost
    lem-bd-match (BDEHole bdσ)
      with lem-bd-σ-match bdσ
    ... | bdσ' , bdσpre , bdσr , bdσpost =
      BDEHole bdσ' ,
      BDEHole bdσpre ,
      BDEHole bdσr ,
      BDEHole bdσpost
    lem-bd-match (BDHole bdσ bd)
      with lem-bd-σ-match bdσ | lem-bd-match bd
    ... | bdσ' , bdσpre , bdσr , bdσpost
        | bd' , bdpre , bdr , bdpost =
      BDHole bdσ' bd' ,
      BDHole bdσpre bdpre ,
      BDHole bdσr bdr ,
      BDHole bdσpost bdpost

    lem-bd-σ-match : {σ : subst-env} {e1 : ihexp} {τ : htyp}
                     {rs-pre : rules} {r : rule} {rs-post : rules} →
                     binders-disjoint-σ σ
                       (match e1 ·: τ of (rs-pre / r / rs-post)) →
                     binders-disjoint-σ σ e1 ×
                       binders-disjoint-σ σ rs-pre ×
                         binders-disjoint-σ σ r ×
                           binders-disjoint-σ σ rs-post
    lem-bd-σ-match BDσId = BDσId , BDσId , BDσId , BDσId
    lem-bd-σ-match (BDσSubst bd
                             (UBMatch ube
                                      (UBZRules ubpre
                                                (UBRules ubr
                                                         ubpost)))
                             bdσ)
      with lem-bd-match bd | lem-bd-σ-match bdσ
    ... | bd' , bdpre , bdr , bdpost
        | bdσ' , bdσpre , bdσr , bdσpost =
      BDσSubst bd' ube bdσ' ,
      BDσSubst bdpre ubpre bdσpre ,
      BDσSubst bdr ubr bdσr ,
      BDσSubst bdpost ubpost bdσpost
    
    lem-bd-rs-match : {rs : rules} {e1 : ihexp} {τ : htyp}
                      {rs-pre : rules} {r : rule} {rs-post : rules} →
                      binders-disjoint-rs rs
                        (match e1 ·: τ of (rs-pre / r / rs-post)) →
                      binders-disjoint-rs rs e1 ×
                        binders-disjoint-rs rs rs-pre ×
                          binders-disjoint-rs rs r ×
                            binders-disjoint-rs rs rs-post
    lem-bd-rs-match BDNoRules =
      BDNoRules , BDNoRules , BDNoRules , BDNoRules 
    lem-bd-rs-match (BDRules bdr bdrs)
      with lem-bd-r-match bdr | lem-bd-rs-match bdrs
    ... | bdr' , bdrpre , bdrr , bdrpost
        | bdrs' , bdrspre , bdrsr , bdrspost =
      BDRules bdr' bdrs' ,
      BDRules bdrpre bdrspre ,
      BDRules bdrr bdrsr ,
      BDRules bdrpost bdrspost

    lem-bd-r-match : {r : rule} {e1 : ihexp} {τ : htyp}
                     {rs-pre : rules} {r1 : rule} {rs-post : rules} →
                     binders-disjoint-r r
                       (match e1 ·: τ of (rs-pre / r1 / rs-post)) →
                     binders-disjoint-r r e1 ×
                       binders-disjoint-r r rs-pre ×
                         binders-disjoint-r r r1 ×
                           binders-disjoint-r r rs-post
    lem-bd-r-match (BDRule bdp bd)
      with lem-bd-p-match bdp | lem-bd-match bd
    ... | bdp' , bdppre , bdpr , bdppost
        | bd' , bdpre , bdr , bdpost =
      BDRule bdp' bd' ,
      BDRule bdppre bdpre ,
      BDRule bdpr bdr ,
      BDRule bdppost bdpost
  
    lem-bd-p-match : {p : pattrn} {e1 : ihexp} {τ : htyp}
                     {rs-pre : rules} {r1 : rule} {rs-post : rules} →
                     binders-disjoint-p p
                       (match e1 ·: τ of (rs-pre / r1 / rs-post)) →
                     binders-disjoint-p p e1 ×
                       binders-disjoint-p p rs-pre ×
                         binders-disjoint-p p r1 ×
                           binders-disjoint-p p rs-post
    lem-bd-p-match BDPUnit = BDPUnit , BDPUnit , BDPUnit , BDPUnit
    lem-bd-p-match BDPNum = BDPNum , BDPNum , BDPNum , BDPNum
    lem-bd-p-match (BDPVar (UBMatch ub
                                    (UBZRules ubpre
                                              (UBRules ubr ubpost)))) =
      BDPVar ub , BDPVar ubpre , BDPVar ubr , BDPVar ubpost
    lem-bd-p-match (BDPInl bd)
      with lem-bd-p-match bd
    ... | bd' , bdpre , bdr , bdpost =
      BDPInl bd' , BDPInl bdpre , BDPInl bdr , BDPInl bdpost
    lem-bd-p-match (BDPInr bd)
      with lem-bd-p-match bd
    ... | bd' , bdpre , bdr , bdpost =
      BDPInr bd' , BDPInr bdpre , BDPInr bdr , BDPInr bdpost
    lem-bd-p-match (BDPPair bd1 bd2)
      with lem-bd-p-match bd1 | lem-bd-p-match bd2
    ... | bd1' , bdpre1 , bdr1 , bdpost1
        | bd2' , bdpre2 , bdr2 , bdpost2 =
      BDPPair bd1' bd2' ,
      BDPPair bdpre1 bdpre2 ,
      BDPPair bdr1 bdr2 ,
      BDPPair bdpost1 bdpost2
    lem-bd-p-match BDPWild =
      BDPWild , BDPWild , BDPWild , BDPWild
    lem-bd-p-match BDPEHole =
      BDPEHole , BDPEHole , BDPEHole , BDPEHole
    lem-bd-p-match (BDPHole bd)
      with lem-bd-p-match bd
    ... | bd' , bdpre , bdr , bdpost =
      BDPHole bd' , BDPHole bdpre , BDPHole bdr , BDPHole bdpost
    
  mutual
    lem-bd-pair : {e : ihexp} {e1 e2 : ihexp} →
                  binders-disjoint e ⟨ e1 , e2 ⟩ →
                  binders-disjoint e e1 ×
                    binders-disjoint e e2
    lem-bd-pair BDUnit = BDUnit , BDUnit
    lem-bd-pair BDNum = BDNum , BDNum
    lem-bd-pair BDVar = BDVar , BDVar
    lem-bd-pair (BDLam (UBPair ub1 ub2) bd)
      with lem-bd-pair bd
    ... | bd1 , bd2 = BDLam ub1 bd1 , BDLam ub2 bd2
    lem-bd-pair (BDAp bd1 bd2)
      with lem-bd-pair bd1 | lem-bd-pair bd2
    ... | bd1₁ , bd1₂ | bd2₁ , bd2₂ =
      BDAp bd1₁ bd2₁ , BDAp bd1₂ bd2₂
    lem-bd-pair (BDInl bd)
      with lem-bd-pair bd
    ... | bd1 , bd2 = BDInl bd1 , BDInl bd2
    lem-bd-pair (BDInr bd)
      with lem-bd-pair bd
    ... | bd1 , bd2 = BDInr bd1 , BDInr bd2
    lem-bd-pair (BDMatch bd (BDZRules bdpre bdpost))
      with lem-bd-pair bd |
           lem-bd-rs-pair bdpre |
           lem-bd-rs-pair bdpost
    ... | bd1 , bd2
        | bdpre1 , bdpre2
        | bdpost1 , bdpost2 =
      BDMatch bd1 (BDZRules bdpre1 bdpost1) ,
      BDMatch bd2 (BDZRules bdpre2 bdpost2)
    lem-bd-pair (BDPair bd1 bd2)
      with lem-bd-pair bd1 | lem-bd-pair bd2
    ... | bd1₁ , bd1₂ | bd2₁ , bd2₂ =
      BDPair bd1₁ bd2₁ , BDPair bd1₂ bd2₂
    lem-bd-pair (BDFst bd)
      with lem-bd-pair bd
    ... | bd1 , bd2 = BDFst bd1 , BDFst bd2
    lem-bd-pair (BDSnd bd)
      with lem-bd-pair bd
    ... | bd1 , bd2 = BDSnd bd1 , BDSnd bd2
    lem-bd-pair (BDEHole bdσ)
      with lem-bd-σ-pair bdσ
    ... | bdσ1 , bdσ2 =
      BDEHole bdσ1 , BDEHole bdσ2
    lem-bd-pair (BDHole bdσ bd)
      with lem-bd-σ-pair bdσ | lem-bd-pair bd
    ... | bdσ1 , bdσ2 | bd1 , bd2 =
      BDHole bdσ1 bd1 , BDHole bdσ2 bd2

    lem-bd-σ-pair : {σ : subst-env} {e1 e2 : ihexp} →
                    binders-disjoint-σ σ ⟨ e1 , e2 ⟩ →
                    binders-disjoint-σ σ e1 ×
                      binders-disjoint-σ σ e2
    lem-bd-σ-pair BDσId =
      BDσId , BDσId
    lem-bd-σ-pair (BDσSubst bd (UBPair ub1 ub2) bdσ)
      with lem-bd-σ-pair bdσ | lem-bd-pair bd
    ... | bdσ1 , bdσ2 | bd1 , bd2 =
      BDσSubst bd1 ub1 bdσ1 , BDσSubst bd2 ub2 bdσ2
    
    lem-bd-rs-pair : {rs : rules} {e1 e2 : ihexp} →
                     binders-disjoint-rs rs ⟨ e1 , e2 ⟩ →
                     binders-disjoint-rs rs e1 ×
                       binders-disjoint-rs rs e2
    lem-bd-rs-pair BDNoRules = BDNoRules , BDNoRules
    lem-bd-rs-pair (BDRules bdr bdrs)
      with lem-bd-r-pair bdr | lem-bd-rs-pair bdrs
    ... | bdr' , ubr | bdrs' , ubrs =
      BDRules bdr' bdrs' , BDRules ubr ubrs

    lem-bd-r-pair : {r : rule} {e1 e2 : ihexp} →
                    binders-disjoint-r r ⟨ e1 , e2 ⟩ →
                    binders-disjoint-r r e1 ×
                      binders-disjoint-r r e2
    lem-bd-r-pair (BDRule bdp bd)
      with lem-bd-p-pair bdp | lem-bd-pair bd
    ... | bdp' , ubp | bd' , ub =
      BDRule bdp' bd' , BDRule ubp ub

    lem-bd-p-pair : {p : pattrn} {e1 e2 : ihexp} →
                    binders-disjoint-p p ⟨ e1 , e2 ⟩ →
                    binders-disjoint-p p e1 ×
                      binders-disjoint-p p e2
    lem-bd-p-pair BDPUnit = BDPUnit , BDPUnit
    lem-bd-p-pair BDPNum = BDPNum , BDPNum
    lem-bd-p-pair (BDPVar (UBPair ub1 ub2)) =
      BDPVar ub1 , BDPVar ub2
    lem-bd-p-pair (BDPInl bd)
      with lem-bd-p-pair bd
    ... | bd' , ub = BDPInl bd' , BDPInl ub
    lem-bd-p-pair (BDPInr bd)
      with lem-bd-p-pair bd
    ... | bd' , ub = BDPInr bd' , BDPInr ub
    lem-bd-p-pair (BDPPair bd1 bd2)
      with lem-bd-p-pair bd1 | lem-bd-p-pair bd2
    ... | bd1' , ub1 | bd2' , ub2 =
      BDPPair bd1' bd2' , BDPPair ub1 ub2
    lem-bd-p-pair BDPWild = BDPWild , BDPWild
    lem-bd-p-pair BDPEHole = BDPEHole , BDPEHole
    lem-bd-p-pair (BDPHole bd)
      with lem-bd-p-pair bd
    ... | bd' , ub = BDPHole bd' , BDPHole ub
    
  mutual
    lem-bd-fst : {e : ihexp} {e1 : ihexp} →
                 binders-disjoint e (fst e1) →
                 binders-disjoint e e1
    lem-bd-fst BDUnit = BDUnit
    lem-bd-fst BDNum = BDNum
    lem-bd-fst BDVar = BDVar
    lem-bd-fst (BDLam (UBFst ub) bd) = BDLam ub (lem-bd-fst bd)
    lem-bd-fst (BDAp bd1 bd2) =
      BDAp (lem-bd-fst bd1) (lem-bd-fst bd2)
    lem-bd-fst (BDInl bd) = BDInl (lem-bd-fst bd)
    lem-bd-fst (BDInr bd) = BDInr (lem-bd-fst bd)
    lem-bd-fst (BDMatch bd (BDZRules bdpre bdpost)) =
      BDMatch (lem-bd-fst bd)
              (BDZRules (lem-bd-rs-fst bdpre)
                        (lem-bd-rs-fst bdpost))
    lem-bd-fst (BDPair bd1 bd2) =
      BDPair (lem-bd-fst bd1) (lem-bd-fst bd2)
    lem-bd-fst (BDFst bd) = BDFst (lem-bd-fst bd)
    lem-bd-fst (BDSnd bd) = BDSnd (lem-bd-fst bd)
    lem-bd-fst (BDEHole bdσ) = BDEHole (lem-bd-σ-fst bdσ)
    lem-bd-fst (BDHole bdσ bd) =
      BDHole (lem-bd-σ-fst bdσ) (lem-bd-fst bd)

    lem-bd-σ-fst : {σ : subst-env} {e1 : ihexp} →
                   binders-disjoint-σ σ (fst e1) →
                   binders-disjoint-σ σ e1
    lem-bd-σ-fst BDσId = BDσId
    lem-bd-σ-fst (BDσSubst bd (UBFst ub) bdσ) =
      BDσSubst (lem-bd-fst bd) ub (lem-bd-σ-fst bdσ)
    
    lem-bd-rs-fst : {rs : rules} {e1 : ihexp} →
                    binders-disjoint-rs rs (fst e1) →
                    binders-disjoint-rs rs e1
    lem-bd-rs-fst BDNoRules = BDNoRules
    lem-bd-rs-fst (BDRules bdr bdrs) =
      BDRules (lem-bd-r-fst bdr) (lem-bd-rs-fst bdrs)

    lem-bd-r-fst : {r : rule} {e1 : ihexp} →
                   binders-disjoint-r r (fst e1) →
                   binders-disjoint-r r e1
    lem-bd-r-fst (BDRule bdp bd) =
      BDRule (lem-bd-p-fst bdp) (lem-bd-fst bd)

    lem-bd-p-fst : {p : pattrn} {e1 : ihexp} →
                   binders-disjoint-p p (fst e1) →
                   binders-disjoint-p p e1
    lem-bd-p-fst BDPUnit = BDPUnit
    lem-bd-p-fst BDPNum = BDPNum
    lem-bd-p-fst (BDPVar (UBFst ub)) = BDPVar ub
    lem-bd-p-fst (BDPInl bd) = BDPInl (lem-bd-p-fst bd)
    lem-bd-p-fst (BDPInr bd) = BDPInr (lem-bd-p-fst bd)
    lem-bd-p-fst (BDPPair bd1 bd2) =
      BDPPair (lem-bd-p-fst bd1) (lem-bd-p-fst bd2)
    lem-bd-p-fst BDPWild = BDPWild
    lem-bd-p-fst BDPEHole = BDPEHole
    lem-bd-p-fst (BDPHole bd) =
      BDPHole (lem-bd-p-fst bd)
    
  mutual
    lem-bd-snd : {e : ihexp} {e1 : ihexp} →
                 binders-disjoint e (snd e1) →
                 binders-disjoint e e1
    lem-bd-snd BDUnit = BDUnit
    lem-bd-snd BDNum = BDNum
    lem-bd-snd BDVar = BDVar
    lem-bd-snd (BDLam (UBSnd ub) bd) =
      BDLam ub (lem-bd-snd bd)
    lem-bd-snd (BDAp bd1 bd2) =
      BDAp (lem-bd-snd bd1) (lem-bd-snd bd2)
    lem-bd-snd (BDInl bd) = BDInl (lem-bd-snd bd)
    lem-bd-snd (BDInr bd) = BDInr (lem-bd-snd bd)
    lem-bd-snd (BDMatch bd (BDZRules bdpre bdpost)) =
      BDMatch (lem-bd-snd bd)
              (BDZRules (lem-bd-rs-snd bdpre)
                        (lem-bd-rs-snd bdpost))
    lem-bd-snd (BDPair bd1 bd2) =
      BDPair (lem-bd-snd bd1) (lem-bd-snd bd2)
    lem-bd-snd (BDFst bd) = BDFst (lem-bd-snd bd)
    lem-bd-snd (BDSnd bd) = BDSnd (lem-bd-snd bd)
    lem-bd-snd (BDEHole bdσ) = BDEHole (lem-bd-σ-snd bdσ)
    lem-bd-snd (BDHole bdσ bd) =
      BDHole (lem-bd-σ-snd bdσ) (lem-bd-snd bd)

    lem-bd-σ-snd : {σ : subst-env} {e1 : ihexp} →
                   binders-disjoint-σ σ (snd e1) →
                   binders-disjoint-σ σ e1
    lem-bd-σ-snd BDσId = BDσId
    lem-bd-σ-snd (BDσSubst bd (UBSnd ub) bdσ) =
      BDσSubst (lem-bd-snd bd) ub (lem-bd-σ-snd bdσ)
    
    lem-bd-rs-snd : {rs : rules} {e1 : ihexp} →
                    binders-disjoint-rs rs (snd e1) →
                    binders-disjoint-rs rs e1
    lem-bd-rs-snd BDNoRules = BDNoRules
    lem-bd-rs-snd (BDRules bdr bdrs) =
      BDRules (lem-bd-r-snd bdr) (lem-bd-rs-snd bdrs)

    lem-bd-r-snd : {r : rule} {e1 : ihexp} →
                   binders-disjoint-r r (snd e1) →
                   binders-disjoint-r r e1
    lem-bd-r-snd (BDRule bdp bd) =
      BDRule (lem-bd-p-snd bdp) (lem-bd-snd bd)

    lem-bd-p-snd : {p : pattrn} {e1 : ihexp} →
                   binders-disjoint-p p (snd e1) →
                   binders-disjoint-p p e1
    lem-bd-p-snd BDPUnit = BDPUnit
    lem-bd-p-snd BDPNum = BDPNum
    lem-bd-p-snd (BDPVar (UBSnd ub)) = BDPVar ub
    lem-bd-p-snd (BDPInl bd) = BDPInl (lem-bd-p-snd bd)
    lem-bd-p-snd (BDPInr bd) = BDPInr (lem-bd-p-snd bd)
    lem-bd-p-snd (BDPPair bd1 bd2) =
      BDPPair (lem-bd-p-snd bd1) (lem-bd-p-snd bd2)
    lem-bd-p-snd BDPWild = BDPWild
    lem-bd-p-snd BDPEHole = BDPEHole
    lem-bd-p-snd (BDPHole bd) =
      BDPHole (lem-bd-p-snd bd)

  mutual
    lem-bd-ehole : {e : ihexp} {u : Nat} {σ : subst-env} →
                   binders-disjoint e ⦇-⦈⟨ u , σ ⟩ →
                   binders-disjoint e σ
    lem-bd-ehole BDUnit = BDUnit
    lem-bd-ehole BDNum = BDNum
    lem-bd-ehole BDVar = BDVar
    lem-bd-ehole (BDLam (UBEHole ubσ) bd) =
      BDLam ubσ (lem-bd-ehole bd)
    lem-bd-ehole (BDAp bd1 bd2) =
      BDAp (lem-bd-ehole bd1) (lem-bd-ehole bd2)
    lem-bd-ehole (BDInl bd) = BDInl (lem-bd-ehole bd)
    lem-bd-ehole (BDInr bd) = BDInr (lem-bd-ehole bd)
    lem-bd-ehole (BDMatch bd (BDZRules bdpre bdpost)) =
      BDMatch (lem-bd-ehole bd)
              (BDZRules (lem-bd-rs-ehole bdpre)
                        (lem-bd-rs-ehole bdpost))
    lem-bd-ehole (BDPair bd1 bd2) =
      BDPair (lem-bd-ehole bd1)
             (lem-bd-ehole bd2)
    lem-bd-ehole (BDFst bd) = BDFst (lem-bd-ehole bd)
    lem-bd-ehole (BDSnd bd) = BDSnd (lem-bd-ehole bd)
    lem-bd-ehole (BDEHole bdσ) = BDEHole (lem-bd-σ-ehole bdσ)
    lem-bd-ehole (BDHole bdσ bd) =
      BDHole (lem-bd-σ-ehole bdσ)
               (lem-bd-ehole bd)

    lem-bd-σ-ehole : {σ : subst-env} {u : Nat} {σ1 : subst-env} →
                     binders-disjoint-σ σ ⦇-⦈⟨ u , σ1 ⟩ →
                     binders-disjoint-σ σ σ1
    lem-bd-σ-ehole BDσId = BDσId
    lem-bd-σ-ehole (BDσSubst bd (UBEHole ubσ) bdσ) =
      BDσSubst (lem-bd-ehole bd) ubσ (lem-bd-σ-ehole bdσ)
    
    lem-bd-rs-ehole : {rs : rules} {u : Nat} {σ : subst-env} →
                      binders-disjoint-rs rs ⦇-⦈⟨ u , σ ⟩ →
                      binders-disjoint-rs rs σ
    lem-bd-rs-ehole BDNoRules = BDNoRules
    lem-bd-rs-ehole (BDRules bdr bdrs) =
      BDRules (lem-bd-r-ehole bdr) (lem-bd-rs-ehole bdrs)

    lem-bd-r-ehole : {r : rule} {u : Nat} {σ : subst-env} →
                     binders-disjoint-r r ⦇-⦈⟨ u , σ ⟩ →
                     binders-disjoint-r r σ
    lem-bd-r-ehole (BDRule bdp bde) =
      BDRule (lem-bd-p-ehole bdp) (lem-bd-ehole bde)
    
    lem-bd-p-ehole : {p : pattrn} {u : Nat} {σ : subst-env} →
                     binders-disjoint-p p ⦇-⦈⟨ u , σ ⟩ →
                     binders-disjoint-p p σ
    lem-bd-p-ehole BDPUnit = BDPUnit
    lem-bd-p-ehole BDPNum = BDPNum
    lem-bd-p-ehole (BDPVar (UBEHole ubσ)) = BDPVar ubσ
    lem-bd-p-ehole (BDPInl bd) = BDPInl (lem-bd-p-ehole bd)
    lem-bd-p-ehole (BDPInr bd) = BDPInr (lem-bd-p-ehole bd)
    lem-bd-p-ehole (BDPPair bd1 bd2) =
      BDPPair (lem-bd-p-ehole bd1) (lem-bd-p-ehole bd2)
    lem-bd-p-ehole BDPWild = BDPWild
    lem-bd-p-ehole BDPEHole = BDPEHole
    lem-bd-p-ehole (BDPHole bd) =
      BDPHole (lem-bd-p-ehole bd)
    
  mutual
    lem-bd-hole : {e : ihexp} {e1 : ihexp} {u : Nat} {σ : subst-env} →
                    binders-disjoint e ⦇⌜ e1 ⌟⦈⟨ u , σ ⟩ →
                    binders-disjoint e σ ×
                      binders-disjoint e e1
    lem-bd-hole BDUnit = BDUnit , BDUnit
    lem-bd-hole BDNum = BDNum , BDNum
    lem-bd-hole BDVar = BDVar , BDVar
    lem-bd-hole (BDLam (UBHole ubσ ub) bd)
      with lem-bd-hole bd
    ... | bdσ ,  bd' =
      BDLam ubσ bdσ , BDLam ub bd' 
    lem-bd-hole (BDAp bd1 bd2)
      with lem-bd-hole bd1 | lem-bd-hole bd2
    ... | bd1σ  , bd1' | bd2σ , bd2' =
      BDAp bd1σ bd2σ , BDAp bd1' bd2'
    lem-bd-hole (BDInl bd)
      with lem-bd-hole bd
    ... |  bdσ , bd' =
      BDInl bdσ , BDInl bd'
    lem-bd-hole (BDInr bd)
      with lem-bd-hole bd
    ... | bdσ , bd'  =
       BDInr bdσ , BDInr bd'
    lem-bd-hole (BDMatch bd (BDZRules bdpre bdpost))
      with lem-bd-hole bd |
           lem-bd-rs-hole bdpre |
           lem-bd-rs-hole bdpost
    ... | bdσ , bd'
        | bdpreσ , bdpre'
        | bdpostσ , bdpost' =
      BDMatch bdσ (BDZRules bdpreσ bdpostσ) ,
      BDMatch bd' (BDZRules bdpre' bdpost')
    lem-bd-hole (BDPair bd1 bd2)
      with lem-bd-hole bd1 | lem-bd-hole bd2
    ... | bdσ1 , bd1' | bdσ2 , bd2' =
      BDPair bdσ1 bdσ2 , BDPair bd1' bd2' 
    lem-bd-hole (BDFst bd)
      with lem-bd-hole bd
    ... | bdσ , bd' = BDFst bdσ , BDFst bd'
    lem-bd-hole (BDSnd bd)
      with lem-bd-hole bd
    ... | bdσ , bd' = BDSnd bdσ , BDSnd bd' 
    lem-bd-hole (BDEHole bdσ)
      with lem-bd-σ-hole bdσ
    ... | bdσσ , bdσ' =
       BDEHole bdσσ , BDEHole bdσ'
    lem-bd-hole (BDHole bdσ bde)
      with lem-bd-σ-hole bdσ | lem-bd-hole bde
    ... | bdσσ , bdσ' | bdeσ , bde' =
      BDHole bdσσ bdeσ , BDHole bdσ' bde'

    lem-bd-σ-hole : {σ : subst-env} {e1 : ihexp} {u : Nat} {σ1 : subst-env} →
                      binders-disjoint-σ σ ⦇⌜ e1 ⌟⦈⟨ u , σ1 ⟩ →
                      binders-disjoint-σ σ σ1 ×
                        binders-disjoint-σ σ e1 
    lem-bd-σ-hole BDσId = BDσId , BDσId
    lem-bd-σ-hole (BDσSubst bdd (UBHole ubσ ub) bdσ)
      with lem-bd-hole bdd | lem-bd-σ-hole bdσ
    ... | bddσ , bdd' | bdσσ , bdσ' =
      BDσSubst bddσ ubσ bdσσ , BDσSubst bdd' ub bdσ'
                        
    lem-bd-rs-hole : {rs : rules} {e1 : ihexp} {u : Nat} {σ : subst-env} →
                       binders-disjoint-rs rs ⦇⌜ e1 ⌟⦈⟨ u , σ ⟩ →
                       binders-disjoint-rs rs σ ×
                         binders-disjoint-rs rs e1
    lem-bd-rs-hole BDNoRules = BDNoRules , BDNoRules
    lem-bd-rs-hole (BDRules bdr bdrs)
      with lem-bd-r-hole bdr | lem-bd-rs-hole bdrs
    ... | bdrσ , bdr' | bdrsσ , bdrs' =
      BDRules bdrσ bdrsσ , BDRules bdr' bdrs'

    lem-bd-r-hole : {r : rule} {e1 : ihexp} {u : Nat} {σ : subst-env} →
                      binders-disjoint-r r ⦇⌜ e1 ⌟⦈⟨ u , σ ⟩ →
                      binders-disjoint-r r σ ×
                        binders-disjoint-r r e1
    lem-bd-r-hole (BDRule bdp bde)
      with lem-bd-p-hole bdp | lem-bd-hole bde
    ... | bdpσ , bdp' | bdeσ , bde' =
      BDRule bdpσ bdeσ , BDRule bdp' bde'
    
    lem-bd-p-hole : {p : pattrn} {e1 : ihexp} {u : Nat} {σ : subst-env} →
                      binders-disjoint-p p ⦇⌜ e1 ⌟⦈⟨ u , σ ⟩ →
                      binders-disjoint-p p σ ×
                        binders-disjoint-p p e1
    lem-bd-p-hole BDPUnit = BDPUnit , BDPUnit
    lem-bd-p-hole BDPNum = BDPNum , BDPNum
    lem-bd-p-hole (BDPVar (UBHole ubσ ub)) =
      BDPVar ubσ , BDPVar ub 
    lem-bd-p-hole (BDPInl bd)
      with lem-bd-p-hole bd
    ... | bdσ , bd' =
      BDPInl bdσ , BDPInl bd'
    lem-bd-p-hole (BDPInr bd)
      with lem-bd-p-hole bd
    ... | bdσ , bd' =
      BDPInr bdσ , BDPInr bd'
    lem-bd-p-hole (BDPPair bd1 bd2)
      with lem-bd-p-hole bd1 |
           lem-bd-p-hole bd2
    ... | bdσ1 , bd1' | bdσ2 , bd2' =
      BDPPair bdσ1 bdσ2 , BDPPair bd1' bd2'
    lem-bd-p-hole BDPWild = BDPWild , BDPWild
    lem-bd-p-hole BDPEHole = BDPEHole , BDPEHole
    lem-bd-p-hole (BDPHole bd)
      with lem-bd-p-hole bd
    ... | bdσ ,  bd' =
      BDPHole bdσ , BDPHole bd'
      
  mutual
    lem-σ-bd-subst : {e : ihexp} {d : ihexp} {y : Nat} {σ : subst-env} →
                     binders-disjoint e (Subst d y σ) →
                     binders-disjoint e d ×
                       unbound-in-e y e ×
                         binders-disjoint e σ
    lem-σ-bd-subst BDUnit = BDUnit , UBUnit , BDUnit
    lem-σ-bd-subst BDNum = BDNum , UBNum , BDNum
    lem-σ-bd-subst BDVar = BDVar , UBVar , BDVar
    lem-σ-bd-subst (BDLam (UBσSubst ub x≠y ubσ) bd)
      with lem-σ-bd-subst bd
    ... | bd' , ub' , bdσ =
      BDLam ub bd' , UBLam (flip x≠y) ub' , BDLam ubσ bdσ
    lem-σ-bd-subst (BDAp bd1 bd2)
      with lem-σ-bd-subst bd1 | lem-σ-bd-subst bd2
    ... | bd1' , ub1 , bdσ1 | bd2' , ub2 , bdσ2 =
      BDAp bd1' bd2' , UBAp ub1 ub2 , BDAp bdσ1 bdσ2
    lem-σ-bd-subst (BDInl bd)
      with lem-σ-bd-subst bd
    ... | bd' , ub , bdσ =
      BDInl bd' , UBInl ub , BDInl bdσ
    lem-σ-bd-subst (BDInr bd)
      with lem-σ-bd-subst bd
    ... | bd' , ub , bdσ =
      BDInr bd' , UBInr ub , BDInr bdσ
    lem-σ-bd-subst (BDMatch bd (BDZRules bdpre bdpost))
      with lem-σ-bd-subst bd |
           lem-σ-bd-rs-subst bdpre |
           lem-σ-bd-rs-subst bdpost
    ... | bd' , ub , bdσ
        | bdpre' , ubpre , bdpreσ
        | bdpost' , ubpost , bdpostσ =
      BDMatch bd' (BDZRules bdpre' bdpost') ,
      UBMatch ub (UBZRules ubpre ubpost) ,
      BDMatch bdσ (BDZRules bdpreσ bdpostσ)
    lem-σ-bd-subst (BDPair bd1 bd2)
      with lem-σ-bd-subst bd1 | lem-σ-bd-subst bd2
    ... | bd1' , ub1 , bdσ1 | bd2' , ub2 , bdσ2 =
      BDPair bd1' bd2' , UBPair ub1 ub2 , BDPair bdσ1 bdσ2
    lem-σ-bd-subst (BDFst bd)
      with lem-σ-bd-subst bd
    ... | bd' , ub , bdσ =
      BDFst bd' , UBFst ub , BDFst bdσ
    lem-σ-bd-subst (BDSnd bd)
      with lem-σ-bd-subst bd
    ... | bd' , ub , bdσ =
      BDSnd bd' , UBSnd ub , BDSnd bdσ
    lem-σ-bd-subst (BDEHole bdσ)
      with lem-σ-bd-σ-subst bdσ
    ... | bdσ' , ubσ , bdσσ =
      BDEHole bdσ' , UBEHole ubσ , BDEHole bdσσ
    lem-σ-bd-subst (BDHole bdσ bde)
      with lem-σ-bd-σ-subst bdσ | lem-σ-bd-subst bde
    ... | bdσ' , ubσ , bdσσ | bde' , ube , bdeσ =
      BDHole bdσ' bde' , UBHole ubσ ube , BDHole bdσσ bdeσ

    lem-σ-bd-σ-subst : {σ : subst-env} {d : ihexp} {y : Nat} {σ1 : subst-env} →
                       binders-disjoint-σ σ (Subst d y σ1) →
                       binders-disjoint-σ σ d ×
                         unbound-in-σ y σ ×
                           binders-disjoint-σ σ σ1
    lem-σ-bd-σ-subst BDσId = BDσId , UBσId , BDσId
    lem-σ-bd-σ-subst (BDσSubst bdd (UBσSubst ub x≠y ubσ) bdσ)
      with lem-σ-bd-subst bdd | lem-σ-bd-σ-subst bdσ
    ... | bdd' , ubd , bddσ | bdσ' , ubσ' , bdσσ =
      BDσSubst bdd' ub bdσ' ,
      UBσSubst ubd (flip x≠y) ubσ' ,
      BDσSubst bddσ ubσ bdσσ
    
    lem-σ-bd-rs-subst : {rs : rules} {d : ihexp} {y : Nat} {σ : subst-env} →
                        binders-disjoint-rs rs (Subst d y σ) →
                        binders-disjoint-rs rs d ×
                          unbound-in-rs y rs ×
                            binders-disjoint-rs rs σ
    lem-σ-bd-rs-subst BDNoRules = BDNoRules , UBNoRules , BDNoRules
    lem-σ-bd-rs-subst (BDRules bdr bdrs)
      with lem-σ-bd-r-subst bdr | lem-σ-bd-rs-subst bdrs
    ... | bdr' , ubr , bdrσ | bdrs' , ubrs , bdrsσ =
      BDRules bdr' bdrs' , UBRules ubr ubrs , BDRules bdrσ bdrsσ

    lem-σ-bd-r-subst : {r : rule} {d : ihexp} {y : Nat} {σ : subst-env} →
                       binders-disjoint-r r (Subst d y σ) →
                       binders-disjoint-r r d ×
                         unbound-in-r y r ×
                           binders-disjoint-r r σ
    lem-σ-bd-r-subst (BDRule bdp bd)
      with lem-σ-bd-p-subst bdp | lem-σ-bd-subst bd
    ... | bdp' , ubp , bdpσ | bd' , ub , bdσ =
      BDRule bdp' bd' , UBRule ubp ub , BDRule bdpσ bdσ

    lem-σ-bd-p-subst : {p : pattrn} {d : ihexp} {y : Nat} {σ : subst-env} →
                       binders-disjoint-p p (Subst d y σ) →
                       binders-disjoint-p p d ×
                         unbound-in-p y p ×
                           binders-disjoint-p p σ
    lem-σ-bd-p-subst BDPUnit = BDPUnit , UBPUnit , BDPUnit
    lem-σ-bd-p-subst BDPNum = BDPNum , UBPNum , BDPNum
    lem-σ-bd-p-subst (BDPVar (UBσSubst ub x≠y ubσ)) =
      BDPVar ub , UBPVar (flip x≠y) , BDPVar ubσ
    lem-σ-bd-p-subst (BDPInl bd)
      with lem-σ-bd-p-subst bd
    ... | bd' , ub , bdσ =
      BDPInl bd' , UBPInl ub , BDPInl bdσ
    lem-σ-bd-p-subst (BDPInr bd)
      with lem-σ-bd-p-subst bd
    ... | bd' , ub , bdσ =
      BDPInr bd' , UBPInr ub , BDPInr bdσ
    lem-σ-bd-p-subst (BDPPair bd1 bd2)
      with lem-σ-bd-p-subst bd1 | lem-σ-bd-p-subst bd2
    ... | bd1' , ub1 , bdσ1 | bd2' , ub2 , bdσ2 =
      BDPPair bd1' bd2' , UBPPair ub1 ub2 , BDPPair bdσ1 bdσ2
    lem-σ-bd-p-subst BDPWild = BDPWild , UBPWild , BDPWild
    lem-σ-bd-p-subst BDPEHole = BDPEHole , UBPEHole , BDPEHole
    lem-σ-bd-p-subst (BDPHole bd)
      with lem-σ-bd-p-subst bd
    ... | bd' , ub , bdσ =
      BDPHole bd' , UBPHole ub , BDPHole bdσ
    
  mutual
    lem-rs-bd : {e : ihexp} {r : rule} {rs : rules} →
                binders-disjoint e (r / rs) →
                binders-disjoint e r ×
                  binders-disjoint e rs
    lem-rs-bd BDUnit = BDUnit , BDUnit
    lem-rs-bd BDNum = BDNum , BDNum
    lem-rs-bd BDVar = BDVar , BDVar
    lem-rs-bd (BDLam (UBRules ubr ubrs) bd)
      with lem-rs-bd bd
    ... | bdr , bdrs = BDLam ubr bdr , BDLam ubrs bdrs
    lem-rs-bd (BDAp bd1 bd2)
      with lem-rs-bd bd1 | lem-rs-bd bd2
    ... | bdr1 , bdrs1 | bdr2 , bdrs2 =
      BDAp bdr1 bdr2 , BDAp bdrs1 bdrs2
    lem-rs-bd (BDInl bd)
      with lem-rs-bd bd
    ... | bdr , bdrs = BDInl bdr , BDInl bdrs
    lem-rs-bd (BDInr bd)
      with lem-rs-bd bd
    ... | bdr , bdrs = BDInr bdr , BDInr bdrs
    lem-rs-bd (BDMatch bd (BDZRules bdpre bdpost))
      with lem-rs-bd bd |
           lem-rs-bd-rs bdpre |
           lem-rs-bd-rs bdpost
    ... | bdr , bdrs
        | bdprer , bdprers
        | bdpostr , bdpostrs =
      BDMatch bdr (BDZRules bdprer bdpostr) ,
      BDMatch bdrs (BDZRules bdprers bdpostrs)
    lem-rs-bd (BDPair bd1 bd2)
      with lem-rs-bd bd1 | lem-rs-bd bd2
    ... | bdr1 , bdrs1 | bdr2 , bdrs2 =
      BDPair bdr1 bdr2 , BDPair bdrs1 bdrs2
    lem-rs-bd (BDFst bd)
      with lem-rs-bd bd
    ... | bdr , bdrs = BDFst bdr , BDFst bdrs
    lem-rs-bd (BDSnd bd)
      with lem-rs-bd bd
    ... | bdr , bdrs = BDSnd bdr , BDSnd bdrs
    lem-rs-bd (BDEHole bdσ)
      with lem-rs-bd-σ bdσ
    ... | bdσr , bdσrs = BDEHole bdσr , BDEHole bdσrs
    lem-rs-bd (BDHole bdσ bd)
      with lem-rs-bd-σ bdσ | lem-rs-bd bd
    ... | bdσr , bdσrs | bdr , bdrs =
      BDHole bdσr bdr , BDHole bdσrs bdrs

    lem-rs-bd-σ : {σ : subst-env} {r : rule} {rs : rules} →
                  binders-disjoint-σ σ (r / rs) →
                  binders-disjoint-σ σ r ×
                    binders-disjoint-σ σ rs
    lem-rs-bd-σ BDσId = BDσId , BDσId
    lem-rs-bd-σ (BDσSubst bd (UBRules ubr ubrs) bdσ)
      with lem-rs-bd bd | lem-rs-bd-σ bdσ
    ... | bdr , bdrs | bdσr , bdσrs =
      BDσSubst bdr ubr bdσr , BDσSubst bdrs ubrs bdσrs
    
    lem-rs-bd-rs : {rs : rules} {r : rule} {rs1 : rules} →
                   binders-disjoint-rs rs (r / rs1) →
                   binders-disjoint-rs rs r ×
                     binders-disjoint-rs rs rs1
    lem-rs-bd-rs BDNoRules = BDNoRules , BDNoRules
    lem-rs-bd-rs (BDRules bdr bdrs)
      with lem-rs-bd-r bdr | lem-rs-bd-rs bdrs
    ... | bdrr , bdrrs | bdrsr , bdrsrs =
      BDRules bdrr bdrsr , BDRules bdrrs bdrsrs
   
    lem-rs-bd-r : {r : rule} {r1 : rule} {rs : rules} →
                  binders-disjoint-r r (r1 / rs) →
                  binders-disjoint-r r r1 ×
                    binders-disjoint-r r rs
    lem-rs-bd-r (BDRule bdp bd)
      with lem-rs-bd-p bdp | lem-rs-bd bd
    ... | bdpr , bdprs | bdr , bdrs =
      BDRule bdpr bdr , BDRule bdprs bdrs

    lem-rs-bd-p : {p : pattrn} {r : rule} {rs : rules} →
                  binders-disjoint-p p (r / rs) →
                  binders-disjoint-p p r ×
                    binders-disjoint-p p rs
    lem-rs-bd-p BDPUnit = BDPUnit , BDPUnit
    lem-rs-bd-p BDPNum = BDPNum , BDPNum
    lem-rs-bd-p (BDPVar (UBRules ubr ubrs)) =
      BDPVar ubr , BDPVar ubrs
    lem-rs-bd-p (BDPInl bd)
      with lem-rs-bd-p bd
    ... | bdr , bdrs = BDPInl bdr , BDPInl bdrs
    lem-rs-bd-p (BDPInr bd)
      with lem-rs-bd-p bd
    ... | bdr , bdrs = BDPInr bdr , BDPInr bdrs
    lem-rs-bd-p (BDPPair bd1 bd2)
      with lem-rs-bd-p bd1 | lem-rs-bd-p bd2
    ... | bdr1 , bdrs1 | bdr2 , bdrs2  =
      BDPPair bdr1 bdr2 , BDPPair bdrs1 bdrs2
    lem-rs-bd-p BDPWild = BDPWild , BDPWild
    lem-rs-bd-p BDPEHole = BDPEHole , BDPEHole
    lem-rs-bd-p (BDPHole bd)
      with lem-rs-bd-p bd
    ... | bdr , bdrs = BDPHole bdr , BDPHole bdrs
    
  mutual
    lem-r-bd : {e : ihexp} {pr : pattrn} {er : ihexp} →
               binders-disjoint e (pr => er) →
               binders-disjoint e pr ×
                 binders-disjoint e er
    lem-r-bd BDUnit = BDUnit , BDUnit
    lem-r-bd BDNum = BDNum , BDNum
    lem-r-bd BDVar = BDVar , BDVar
    lem-r-bd (BDLam (UBRule ubr ube) bd)
      with lem-r-bd bd
    ... | bdp , bde = BDLam ubr bdp , BDLam ube bde
    lem-r-bd (BDAp bd1 bd2)
      with lem-r-bd bd1 | lem-r-bd bd2
    ... | bdp1 , bde1 | bdp2 , bde2 =
      BDAp bdp1 bdp2 , BDAp bde1 bde2
    lem-r-bd (BDInl bd)
      with lem-r-bd bd
    ... | bdp , bde = BDInl bdp , BDInl bde
    lem-r-bd (BDInr bd)
      with lem-r-bd bd
    ... | bdp , bde = BDInr bdp , BDInr bde
    lem-r-bd (BDMatch bd (BDZRules bdpre bdpost))
      with lem-r-bd bd |
           lem-r-bd-rs bdpre |
           lem-r-bd-rs bdpost 
    ... | bdp , bde
        | bdprep , bdpree
        | bdpostp , bdposte =
      BDMatch bdp (BDZRules bdprep bdpostp) ,
      BDMatch bde (BDZRules bdpree bdposte)
    lem-r-bd (BDPair bd1 bd2)
      with lem-r-bd bd1 | lem-r-bd bd2
    ... | bdp1 , bde1 | bdp2 , bde2 =
      BDPair bdp1 bdp2 , BDPair bde1 bde2
    lem-r-bd (BDFst bd)
      with lem-r-bd bd
    ... | bdp , bde = BDFst bdp , BDFst bde
    lem-r-bd (BDSnd bd)
      with lem-r-bd bd
    ... | bdp , bde = BDSnd bdp , BDSnd bde
    lem-r-bd (BDEHole bdσ)
      with lem-r-bd-σ bdσ
    ... | bdσp , bdσe = BDEHole bdσp , BDEHole bdσe
    lem-r-bd (BDHole bdσ bd)
      with lem-r-bd-σ bdσ | lem-r-bd bd
    ... | bdσp , bdσe | bdp , bde =
      BDHole bdσp bdp , BDHole bdσe bde

    lem-r-bd-σ : {σ : subst-env} {pr : pattrn} {er : ihexp} →
                 binders-disjoint-σ σ (pr => er) →
                 binders-disjoint-σ σ pr ×
                   binders-disjoint-σ σ er
    lem-r-bd-σ BDσId = BDσId , BDσId
    lem-r-bd-σ (BDσSubst bd (UBRule ubp ube) bdσ)
      with lem-r-bd bd | lem-r-bd-σ bdσ
    ... | bdσp , bdσe | bdp , bde =
      BDσSubst bdσp ubp bdp , BDσSubst bdσe ube bde
    
    lem-r-bd-rs : {rs : rules} {pr : pattrn} {er : ihexp} →
                  binders-disjoint-rs rs (pr => er) →
                  binders-disjoint-rs rs pr ×
                    binders-disjoint-rs rs er
    lem-r-bd-rs BDNoRules = BDNoRules , BDNoRules
    lem-r-bd-rs (BDRules bdr bdrs)
      with lem-r-bd-r bdr | lem-r-bd-rs bdrs
    ... | bdrp , bdre | bdrsp , bdrse =
      BDRules bdrp bdrsp , BDRules bdre bdrse

    lem-r-bd-r : {r : rule} {pr : pattrn} {er : ihexp} →
                 binders-disjoint-r r (pr => er) →
                 binders-disjoint-r r pr ×
                   binders-disjoint-r r er
    lem-r-bd-r (BDRule bdp bd)
      with lem-r-bd-p bdp | lem-r-bd bd
    ... | bdpp , bdpe | ebdp , ebde =
      BDRule bdpp ebdp , BDRule bdpe ebde

    lem-r-bd-p : {p : pattrn} {pr : pattrn} {er : ihexp} →
                 binders-disjoint-p p (pr => er) →
                 binders-disjoint-p p pr ×
                   binders-disjoint-p p er
    lem-r-bd-p BDPUnit = BDPUnit , BDPUnit
    lem-r-bd-p BDPNum = BDPNum , BDPNum
    lem-r-bd-p (BDPVar (UBRule ubr ubrs)) =
      BDPVar ubr , BDPVar ubrs
    lem-r-bd-p (BDPInl bd)
      with lem-r-bd-p bd
    ... | bdp , bde = BDPInl bdp , BDPInl bde
    lem-r-bd-p (BDPInr bd)
      with lem-r-bd-p bd
    ... | bdp , bde = BDPInr bdp , BDPInr bde
    lem-r-bd-p (BDPPair bd1 bd2)
      with lem-r-bd-p bd1 | lem-r-bd-p bd2
    ... | bdp1 , bde1 | bdp2 , bde2 =
      BDPPair bdp1 bdp2 , BDPPair bde1 bde2
    lem-r-bd-p BDPWild = BDPWild , BDPWild
    lem-r-bd-p BDPEHole = BDPEHole , BDPEHole
    lem-r-bd-p (BDPHole bd)
      with lem-r-bd-p bd
    ... | bdp , bde =
      BDPHole bdp , BDPHole bde

  mutual
    lem-p-bd-var : {e : ihexp} {x : Nat} →
                   binders-disjoint {T = pattrn} e (X x) →
                   unbound-in-e x e
    lem-p-bd-var BDUnit = UBUnit
    lem-p-bd-var BDNum = UBNum
    lem-p-bd-var BDVar = UBVar
    lem-p-bd-var (BDLam (UBPVar x≠y) bd) =
      UBLam (flip x≠y) (lem-p-bd-var bd)
    lem-p-bd-var (BDAp bd1 bd2) =
      UBAp (lem-p-bd-var bd1) (lem-p-bd-var bd2)
    lem-p-bd-var (BDInl bd) =
      UBInl (lem-p-bd-var bd)
    lem-p-bd-var (BDInr bd) =
      UBInr (lem-p-bd-var bd)
    lem-p-bd-var (BDMatch bd (BDZRules bdpre bdpost)) =
      UBMatch (lem-p-bd-var bd)
              (UBZRules (lem-p-bd-rs-var bdpre)
                        (lem-p-bd-rs-var bdpost))
    lem-p-bd-var (BDPair bd1 bd2) =
      UBPair (lem-p-bd-var bd1) (lem-p-bd-var bd2)
    lem-p-bd-var (BDFst bd) = UBFst (lem-p-bd-var bd)
    lem-p-bd-var (BDSnd bd) = UBSnd (lem-p-bd-var bd)
    lem-p-bd-var (BDEHole bdσ) = UBEHole (lem-p-bd-σ-var bdσ)
    lem-p-bd-var (BDHole bdσ bd) =
      UBHole (lem-p-bd-σ-var bdσ) (lem-p-bd-var bd)

    lem-p-bd-σ-var : {σ : subst-env} {x : Nat} →
                     binders-disjoint-σ {T = pattrn} σ (X x) →
                     unbound-in-σ x σ
    lem-p-bd-σ-var BDσId = UBσId
    lem-p-bd-σ-var (BDσSubst bd (UBPVar y≠x) bdσ) =
      UBσSubst (lem-p-bd-var bd) (flip y≠x) (lem-p-bd-σ-var bdσ) 
    
    lem-p-bd-rs-var : {rs : rules} {x : Nat} →
                      binders-disjoint-rs {T = pattrn} rs (X x) →
                      unbound-in-rs x rs
    lem-p-bd-rs-var BDNoRules = UBNoRules
    lem-p-bd-rs-var (BDRules bdr bdrs) =
      UBRules (lem-p-bd-r-var bdr) (lem-p-bd-rs-var bdrs)

    lem-p-bd-r-var : {r : rule} {x : Nat} →
                     binders-disjoint-r {T = pattrn} r (X x) →
                     unbound-in-r x r
    lem-p-bd-r-var (BDRule bdp bd) =
      UBRule (lem-p-bd-p-var bdp) (lem-p-bd-var bd)

    lem-p-bd-p-var : {p : pattrn} {x : Nat} →
                     binders-disjoint-p {T = pattrn} p (X x) →
                     unbound-in-p x p
    lem-p-bd-p-var BDPUnit = UBPUnit
    lem-p-bd-p-var BDPNum = UBPNum
    lem-p-bd-p-var (BDPVar (UBPVar x≠y)) =
      UBPVar (flip x≠y)
    lem-p-bd-p-var (BDPInl bd) =
      UBPInl (lem-p-bd-p-var bd)
    lem-p-bd-p-var (BDPInr bd) =
      UBPInr (lem-p-bd-p-var bd)
    lem-p-bd-p-var (BDPPair bd1 bd2) =
      UBPPair (lem-p-bd-p-var bd1)
              (lem-p-bd-p-var bd2)
    lem-p-bd-p-var BDPWild = UBPWild
    lem-p-bd-p-var BDPEHole = UBPEHole
    lem-p-bd-p-var (BDPHole bd) =
      UBPHole (lem-p-bd-p-var bd)

  mutual
    lem-p-bd-inl : {e : ihexp} {p1 : pattrn} →
                   binders-disjoint e (inl p1) →
                   binders-disjoint e p1
    lem-p-bd-inl BDUnit = BDUnit
    lem-p-bd-inl BDNum = BDNum
    lem-p-bd-inl BDVar = BDVar
    lem-p-bd-inl (BDLam (UBPInl ub) bd) =
      BDLam ub (lem-p-bd-inl bd)
    lem-p-bd-inl (BDAp bd1 bd2) =
      BDAp (lem-p-bd-inl bd1) (lem-p-bd-inl bd2)
    lem-p-bd-inl (BDInl bd) = BDInl (lem-p-bd-inl bd)
    lem-p-bd-inl (BDInr bd) = BDInr (lem-p-bd-inl bd)
    lem-p-bd-inl (BDMatch bd (BDZRules bdpre bdpost)) =
      BDMatch (lem-p-bd-inl bd)
              (BDZRules (lem-p-bd-rs-inl bdpre)
                        (lem-p-bd-rs-inl bdpost))
    lem-p-bd-inl (BDPair bd1 bd2) =
      BDPair (lem-p-bd-inl bd1) (lem-p-bd-inl bd2)
    lem-p-bd-inl (BDFst bd) =  BDFst (lem-p-bd-inl bd)
    lem-p-bd-inl (BDSnd bd) = BDSnd (lem-p-bd-inl bd)
    lem-p-bd-inl (BDEHole bdσ) =
      BDEHole (lem-p-bd-σ-inl bdσ)
    lem-p-bd-inl (BDHole bdσ bd) =
      BDHole (lem-p-bd-σ-inl bdσ) (lem-p-bd-inl bd)
    
    lem-p-bd-σ-inl : {σ : subst-env} {p1 : pattrn} →
                     binders-disjoint-σ σ (inl p1) →
                     binders-disjoint-σ σ p1
    lem-p-bd-σ-inl BDσId = BDσId
    lem-p-bd-σ-inl (BDσSubst bd (UBPInl ub) bdσ) =
      BDσSubst (lem-p-bd-inl bd) ub (lem-p-bd-σ-inl bdσ)
    
    lem-p-bd-rs-inl : {rs : rules} {p1 : pattrn} →
                      binders-disjoint-rs rs (inl p1) →
                      binders-disjoint-rs rs p1
    lem-p-bd-rs-inl BDNoRules = BDNoRules
    lem-p-bd-rs-inl (BDRules bdr bdrs) =
      BDRules (lem-p-bd-r-inl bdr) (lem-p-bd-rs-inl bdrs)

    lem-p-bd-r-inl : {r : rule} {p1 : pattrn} →
                     binders-disjoint-r r (inl p1) →
                     binders-disjoint-r r p1
    lem-p-bd-r-inl (BDRule bdp bd) =
      BDRule (lem-p-bd-p-inl bdp) (lem-p-bd-inl bd)

    lem-p-bd-p-inl : {p : pattrn} {p1 : pattrn} →
                     binders-disjoint-p p (inl p1) →
                     binders-disjoint-p p p1
    lem-p-bd-p-inl BDPUnit = BDPUnit
    lem-p-bd-p-inl BDPNum = BDPNum
    lem-p-bd-p-inl (BDPVar (UBPInl ub)) = BDPVar ub
    lem-p-bd-p-inl (BDPInl bd) =
      BDPInl (lem-p-bd-p-inl bd)
    lem-p-bd-p-inl (BDPInr bd) =
      BDPInr (lem-p-bd-p-inl bd)
    lem-p-bd-p-inl (BDPPair bd1 bd2) =
      BDPPair (lem-p-bd-p-inl bd1)
        (lem-p-bd-p-inl bd2)
    lem-p-bd-p-inl BDPWild = BDPWild
    lem-p-bd-p-inl BDPEHole = BDPEHole
    lem-p-bd-p-inl (BDPHole bd) =
      BDPHole (lem-p-bd-p-inl bd)

  mutual
    lem-p-bd-inr : {e : ihexp} {p1 : pattrn} →
                   binders-disjoint e (inr p1) →
                   binders-disjoint e p1
    lem-p-bd-inr BDUnit = BDUnit 
    lem-p-bd-inr BDNum = BDNum
    lem-p-bd-inr BDVar = BDVar
    lem-p-bd-inr (BDLam (UBPInr ub) bd) =
      BDLam ub (lem-p-bd-inr bd)
    lem-p-bd-inr (BDAp bd1 bd2) =
      BDAp (lem-p-bd-inr bd1) (lem-p-bd-inr bd2)
    lem-p-bd-inr (BDInl bd) = BDInl (lem-p-bd-inr bd)
    lem-p-bd-inr (BDInr bd) = BDInr (lem-p-bd-inr bd)
    lem-p-bd-inr (BDMatch bd (BDZRules bdpre bdpost)) =
      BDMatch (lem-p-bd-inr bd)
              (BDZRules (lem-p-bd-rs-inr bdpre)
                        (lem-p-bd-rs-inr bdpost))
    lem-p-bd-inr (BDPair bd1 bd2) =
      BDPair (lem-p-bd-inr bd1) (lem-p-bd-inr bd2)
    lem-p-bd-inr (BDFst bd) = BDFst (lem-p-bd-inr bd)
    lem-p-bd-inr (BDSnd bd) = BDSnd (lem-p-bd-inr bd)
    lem-p-bd-inr (BDEHole bdσ) =
      BDEHole (lem-p-bd-σ-inr bdσ)
    lem-p-bd-inr (BDHole bdσ bd) =
      BDHole (lem-p-bd-σ-inr bdσ) (lem-p-bd-inr bd)

    lem-p-bd-σ-inr : {σ : subst-env} {p1 : pattrn} →
                     binders-disjoint-σ σ (inr p1) →
                     binders-disjoint-σ σ p1
    lem-p-bd-σ-inr BDσId = BDσId
    lem-p-bd-σ-inr (BDσSubst bd (UBPInr ub) bdσ) =
      BDσSubst (lem-p-bd-inr bd) ub (lem-p-bd-σ-inr bdσ)
    
    lem-p-bd-rs-inr : {rs : rules} {p1 : pattrn} →
                      binders-disjoint-rs rs (inr p1) →
                      binders-disjoint-rs rs p1
    lem-p-bd-rs-inr BDNoRules = BDNoRules
    lem-p-bd-rs-inr (BDRules bdr bdrs) =
      BDRules (lem-p-bd-r-inr bdr) (lem-p-bd-rs-inr bdrs)

    lem-p-bd-r-inr : {r : rule} {p1 : pattrn} →
                     binders-disjoint-r r (inr p1) →
                     binders-disjoint-r r p1
    lem-p-bd-r-inr (BDRule bdp bd) =
      BDRule (lem-p-bd-p-inr bdp) (lem-p-bd-inr bd)

    lem-p-bd-p-inr : {p : pattrn} {p1 : pattrn} →
                     binders-disjoint-p p (inr p1) →
                     binders-disjoint-p p p1
    lem-p-bd-p-inr BDPUnit = BDPUnit
    lem-p-bd-p-inr BDPNum = BDPNum
    lem-p-bd-p-inr (BDPVar (UBPInr ub)) = BDPVar ub
    lem-p-bd-p-inr (BDPInl bd) =
      BDPInl (lem-p-bd-p-inr bd)
    lem-p-bd-p-inr (BDPInr bd) =
      BDPInr (lem-p-bd-p-inr bd)
    lem-p-bd-p-inr (BDPPair bd1 bd2) =
      BDPPair (lem-p-bd-p-inr bd1)
              (lem-p-bd-p-inr bd2)
    lem-p-bd-p-inr BDPWild = BDPWild
    lem-p-bd-p-inr BDPEHole = BDPEHole
    lem-p-bd-p-inr (BDPHole bd) =
      BDPHole (lem-p-bd-p-inr bd)

  mutual
    lem-p-bd-pair : {e : ihexp} {p1 p2 : pattrn} →
                    binders-disjoint e ⟨ p1 , p2 ⟩ →
                    binders-disjoint e p1 ×
                      binders-disjoint e p2
    lem-p-bd-pair BDUnit = BDUnit , BDUnit
    lem-p-bd-pair BDNum = BDNum , BDNum
    lem-p-bd-pair BDVar = BDVar , BDVar
    lem-p-bd-pair (BDLam (UBPPair ub1 ub2) bd)
      with lem-p-bd-pair bd
    ... | bd1 , bd2 = BDLam ub1 bd1 , BDLam ub2 bd2
    lem-p-bd-pair (BDAp bd1 bd2)
      with lem-p-bd-pair bd1 | lem-p-bd-pair bd2
    ... | bd1₁ , bd1₂ | bd2₁ , bd2₂ =
      BDAp bd1₁ bd2₁ , BDAp bd1₂ bd2₂
    lem-p-bd-pair (BDInl bd)
      with lem-p-bd-pair bd
    ... | bd1 , bd2 = BDInl bd1 , BDInl bd2
    lem-p-bd-pair (BDInr bd)
      with lem-p-bd-pair bd
    ... | bd1 , bd2 = BDInr bd1 , BDInr bd2
    lem-p-bd-pair (BDMatch bd (BDZRules bdpre bdpost))
      with lem-p-bd-pair bd |
           lem-p-bd-rs-pair bdpre |
           lem-p-bd-rs-pair bdpost
    ... | bd1 , bd2
        | bdpre1 , bdpre2
        | bdpost1 , bdpost2 =
      BDMatch bd1 (BDZRules bdpre1 bdpost1) ,
      BDMatch bd2 (BDZRules bdpre2 bdpost2)
    lem-p-bd-pair (BDPair bd1 bd2)
      with lem-p-bd-pair bd1 | lem-p-bd-pair bd2
    ... | bd1₁ , bd1₂ | bd2₁ , bd2₂ =
      BDPair bd1₁ bd2₁ , BDPair bd1₂ bd2₂
    lem-p-bd-pair (BDFst bd)
      with lem-p-bd-pair bd
    ... | bd1 , bd2 = BDFst bd1 , BDFst bd2
    lem-p-bd-pair (BDSnd bd)
      with lem-p-bd-pair bd
    ... | bd1 , bd2 = BDSnd bd1 , BDSnd bd2
    lem-p-bd-pair (BDEHole bdσ)
      with lem-p-bd-σ-pair bdσ
    ... | bdσ1 , bdσ2 = BDEHole bdσ1 , BDEHole bdσ2
    lem-p-bd-pair (BDHole bdσ bd)
      with lem-p-bd-σ-pair bdσ | lem-p-bd-pair bd
    ... | bdσ1 , bdσ2 | bd1 , bd2 =
      BDHole bdσ1 bd1 , BDHole bdσ2 bd2

    lem-p-bd-σ-pair : {σ : subst-env} {p1 p2 : pattrn} →
                      binders-disjoint-σ σ ⟨ p1 , p2 ⟩ →
                      binders-disjoint-σ σ p1 ×
                        binders-disjoint-σ σ p2
    lem-p-bd-σ-pair BDσId = BDσId , BDσId
    lem-p-bd-σ-pair (BDσSubst bd (UBPPair ub1 ub2) bdσ)
      with lem-p-bd-pair bd | lem-p-bd-σ-pair bdσ
    ... | bd1 , bd2 | bdσ1 , bdσ2 =
      BDσSubst bd1 ub1 bdσ1 , BDσSubst bd2 ub2 bdσ2
    
    lem-p-bd-rs-pair : {rs : rules} {p1 p2 : pattrn} →
                       binders-disjoint-rs rs ⟨ p1 , p2 ⟩ →
                       binders-disjoint-rs rs p1 ×
                         binders-disjoint-rs rs p2
    lem-p-bd-rs-pair BDNoRules = BDNoRules , BDNoRules
    lem-p-bd-rs-pair (BDRules bdr bdrs)
      with lem-p-bd-r-pair bdr |
           lem-p-bd-rs-pair bdrs
    ... | bdr1 , bdr2 | bdrs1 , bdrs2 =
      BDRules bdr1 bdrs1 , BDRules bdr2 bdrs2

    lem-p-bd-r-pair : {r : rule} {p1 p2 : pattrn} →
                      binders-disjoint-r r ⟨ p1 , p2 ⟩ →
                      binders-disjoint-r r p1 ×
                        binders-disjoint-r r p2
    lem-p-bd-r-pair (BDRule bdp bd)
      with lem-p-bd-p-pair bdp |
           lem-p-bd-pair bd
    ... | bdp1 , bdp2 | bd1 , bd2 =
      BDRule bdp1 bd1 , BDRule bdp2 bd2

    lem-p-bd-p-pair : {p : pattrn} {p1 p2 : pattrn} →
                      binders-disjoint-p p ⟨ p1 , p2 ⟩ →
                      binders-disjoint-p p p1 ×
                        binders-disjoint-p p p2
    lem-p-bd-p-pair BDPUnit = BDPUnit , BDPUnit
    lem-p-bd-p-pair BDPNum = BDPNum , BDPNum
    lem-p-bd-p-pair (BDPVar (UBPPair ub1 ub2)) =
      BDPVar ub1 , BDPVar ub2
    lem-p-bd-p-pair (BDPInl bd)
      with lem-p-bd-p-pair bd
    ... | bd1 , bd2 = BDPInl bd1 , BDPInl bd2
    lem-p-bd-p-pair (BDPInr bd)
      with lem-p-bd-p-pair bd
    ... | bd1 , bd2 = BDPInr bd1 , BDPInr bd2
    lem-p-bd-p-pair (BDPPair bd1 bd2)
      with lem-p-bd-p-pair bd1 |
           lem-p-bd-p-pair bd2
    ... | bd1₁ , bd1₂ | bd2₁ , bd2₂ =
      BDPPair bd1₁ bd2₁ , BDPPair bd1₂ bd2₂
    lem-p-bd-p-pair BDPWild = BDPWild , BDPWild
    lem-p-bd-p-pair BDPEHole = BDPEHole , BDPEHole
    lem-p-bd-p-pair (BDPHole bd)
      with lem-p-bd-p-pair bd
    ... | bd1 , bd2 = BDPHole bd1 , BDPHole bd2

  mutual
    lem-p-bd-hole : {e : ihexp}
                      {p1 : pattrn} {w : Nat} {τ : htyp} →
                      binders-disjoint e ⦇⌜ p1 ⌟⦈[ w , τ ] →
                      binders-disjoint e p1
    lem-p-bd-hole BDUnit = BDUnit
    lem-p-bd-hole BDNum = BDNum
    lem-p-bd-hole BDVar = BDVar
    lem-p-bd-hole (BDLam (UBPHole ub) bd) =
      BDLam ub (lem-p-bd-hole bd)
    lem-p-bd-hole (BDAp bd1 bd2) =
      BDAp (lem-p-bd-hole bd1) (lem-p-bd-hole bd2)
    lem-p-bd-hole (BDInl bd) =
      BDInl (lem-p-bd-hole bd)
    lem-p-bd-hole (BDInr bd) =
      BDInr (lem-p-bd-hole bd)
    lem-p-bd-hole (BDMatch bd (BDZRules bdpre bdpost)) =
      BDMatch (lem-p-bd-hole bd)
              (BDZRules (lem-p-bd-rs-hole bdpre)
                        (lem-p-bd-rs-hole bdpost))
    lem-p-bd-hole (BDPair bd1 bd2) =
      BDPair (lem-p-bd-hole bd1) (lem-p-bd-hole bd2)
    lem-p-bd-hole (BDFst bd) =
      BDFst (lem-p-bd-hole bd)
    lem-p-bd-hole (BDSnd bd) =
      BDSnd (lem-p-bd-hole bd)
    lem-p-bd-hole (BDEHole bdσ) =
      BDEHole (lem-p-bd-σ-hole bdσ)
    lem-p-bd-hole (BDHole bdσ bd) =
      BDHole (lem-p-bd-σ-hole bdσ) (lem-p-bd-hole bd)

    lem-p-bd-σ-hole : {σ : subst-env} {p1 : pattrn} {w : Nat} {τ : htyp} →
                        binders-disjoint-σ σ ⦇⌜ p1 ⌟⦈[ w , τ ] →
                        binders-disjoint-σ σ p1
    lem-p-bd-σ-hole BDσId = BDσId
    lem-p-bd-σ-hole (BDσSubst bd (UBPHole ub) bdσ) =
      BDσSubst (lem-p-bd-hole bd) ub (lem-p-bd-σ-hole bdσ)
    
    lem-p-bd-rs-hole : {rs : rules} {p1 : pattrn} {w : Nat} {τ : htyp} →
                         binders-disjoint-rs rs ⦇⌜ p1 ⌟⦈[ w , τ ] →
                         binders-disjoint-rs rs p1
    lem-p-bd-rs-hole BDNoRules = BDNoRules
    lem-p-bd-rs-hole (BDRules bdr bdrs) =
      BDRules (lem-p-bd-r-hole bdr) (lem-p-bd-rs-hole bdrs)

    lem-p-bd-r-hole : {r : rule} {p1 : pattrn} {w : Nat} {τ : htyp} →
                        binders-disjoint-r r ⦇⌜ p1 ⌟⦈[ w , τ ] →
                        binders-disjoint-r r p1
    lem-p-bd-r-hole (BDRule bdp bd) =
      BDRule (lem-p-bd-p-hole bdp) (lem-p-bd-hole bd)

    lem-p-bd-p-hole : {p : pattrn} {p1 : pattrn} {w : Nat} {τ : htyp} →
                        binders-disjoint-p p ⦇⌜ p1 ⌟⦈[ w , τ ] →
                        binders-disjoint-p p p1
    lem-p-bd-p-hole BDPUnit = BDPUnit
    lem-p-bd-p-hole BDPNum = BDPNum
    lem-p-bd-p-hole (BDPVar (UBPHole ub)) = BDPVar ub
    lem-p-bd-p-hole (BDPInl bd) =
      BDPInl (lem-p-bd-p-hole bd)
    lem-p-bd-p-hole (BDPInr bd) =
      BDPInr (lem-p-bd-p-hole bd)
    lem-p-bd-p-hole (BDPPair bd1 bd2) =
      BDPPair (lem-p-bd-p-hole bd1)
              (lem-p-bd-p-hole bd2)
    lem-p-bd-p-hole BDPWild = BDPWild
    lem-p-bd-p-hole BDPEHole = BDPEHole
    lem-p-bd-p-hole (BDPHole bd) =
      BDPHole (lem-p-bd-p-hole bd)

  -- the following are the main results of this file, proving
  -- that each binders-disjoint judgement is symmetric
  mutual
    binders-disjoint-sym : {e1 e2 : ihexp} →
                           binders-disjoint e1 e2 →
                           binders-disjoint e2 e1
    binders-disjoint-sym {e2 = unit} bd = BDUnit
    binders-disjoint-sym {e2 = N n} bd = BDNum
    binders-disjoint-sym {e2 = X x} bd = BDVar
    binders-disjoint-sym {e2 = ·λ x ·[ τ ] e2} bd
      with lem-bd-lam bd
    ... | ub , bd' =
      BDLam ub (binders-disjoint-sym bd')
    binders-disjoint-sym {e2 = e2₁ ∘ e2₂} bd
      with lem-bd-ap bd
    ... | bd1 , bd2 =
      BDAp (binders-disjoint-sym bd1)
           (binders-disjoint-sym bd2)
    binders-disjoint-sym {e2 = inl τ e2} bd =
      BDInl (binders-disjoint-sym (lem-bd-inl bd))
    binders-disjoint-sym {e2 = inr τ e2} bd =
      BDInr (binders-disjoint-sym (lem-bd-inr bd))
    binders-disjoint-sym
      {e2 = match e2 ·: τ of (rs-pre / r / rs-post)} bd
      with lem-bd-match bd
    ... | bd' , bdpre , bdr , bdpost =
      BDMatch (binders-disjoint-sym bd')
              (BDZRules (rs-binders-disjoint-sym bdpre)
                        (BDRules (r-binders-disjoint-sym bdr)
                                 (rs-binders-disjoint-sym bdpost)))
                        
    binders-disjoint-sym {e2 = ⟨ e2₁ , e2₂ ⟩} bd
      with lem-bd-pair bd
    ... | bd1 , bd2 =
      BDPair (binders-disjoint-sym bd1)
             (binders-disjoint-sym bd2)
    binders-disjoint-sym {e2 = fst e2} bd =
      BDFst (binders-disjoint-sym (lem-bd-fst bd))
    binders-disjoint-sym {e2 = snd e2} bd =
      BDSnd (binders-disjoint-sym (lem-bd-snd bd))
    binders-disjoint-sym {e2 = ⦇-⦈⟨ u , σ ⟩} bd =
      BDEHole (σ-binders-disjoint-sym (lem-bd-ehole bd))
    binders-disjoint-sym {e2 = ⦇⌜ e2 ⌟⦈⟨ u , σ ⟩} bd
      with lem-bd-hole bd
    ... | bdσ , bd' =
      BDHole (σ-binders-disjoint-sym bdσ)
               (binders-disjoint-sym bd')

    σ-binders-disjoint-sym : {e : ihexp} {σ : subst-env} →
                             binders-disjoint e σ →
                             binders-disjoint-σ σ e
    σ-binders-disjoint-sym {σ = Id Γ} bdσ = BDσId
    σ-binders-disjoint-sym {σ = Subst d y σ} bdσ
      with lem-σ-bd-subst bdσ
    ... | bd , ub , bdσ' =
      BDσSubst (binders-disjoint-sym bd)
               ub
               (σ-binders-disjoint-sym bdσ')
                
    rs-binders-disjoint-sym : {e : ihexp} {rs : rules} →
                              binders-disjoint e rs →
                              binders-disjoint-rs rs e
    rs-binders-disjoint-sym {rs = nil} bd = BDNoRules
    rs-binders-disjoint-sym {rs = r / rs} bd
      with lem-rs-bd bd
    ... | rbd , rsbd =
      BDRules (r-binders-disjoint-sym rbd)
              (rs-binders-disjoint-sym rsbd)

    r-binders-disjoint-sym : {e : ihexp} {r : rule} →
                             binders-disjoint e r →
                             binders-disjoint-r r e
    r-binders-disjoint-sym {r = pr => er} bd
      with lem-r-bd bd
    ... | bdp , bde =
      BDRule (p-binders-disjoint-sym bdp)
             (binders-disjoint-sym bde)
    
    p-binders-disjoint-sym : {e : ihexp} {p : pattrn} →
                             binders-disjoint e p →
                             binders-disjoint-p p e
    p-binders-disjoint-sym {p = unit} bd = BDPUnit
    p-binders-disjoint-sym {p = N n} bd = BDPNum
    p-binders-disjoint-sym {p = X x} bd =
      BDPVar (lem-p-bd-var bd)
    p-binders-disjoint-sym {p = inl p} bd =
      BDPInl (p-binders-disjoint-sym (lem-p-bd-inl bd))
    p-binders-disjoint-sym {p = inr p} bd =
      BDPInr (p-binders-disjoint-sym (lem-p-bd-inr bd))
    p-binders-disjoint-sym {p = ⟨ p1 , p2 ⟩} bd
      with lem-p-bd-pair bd
    ... | bd1 , bd2 = 
      BDPPair (p-binders-disjoint-sym bd1)
              (p-binders-disjoint-sym bd2)
    p-binders-disjoint-sym {p = wild} bd = BDPWild
    p-binders-disjoint-sym {p = ⦇-⦈[ w ]} bd = BDPEHole
    p-binders-disjoint-sym {p = ⦇⌜ p ⌟⦈[ w , τ ]} bd =
      BDPHole (p-binders-disjoint-sym (lem-p-bd-hole bd))

  mutual
    binders-disjoint-σ-sym : {σ : subst-env} {e : ihexp} →
                             binders-disjoint-σ σ e →
                             binders-disjoint e σ
    binders-disjoint-σ-sym {e = unit} bd = BDUnit
    binders-disjoint-σ-sym {e = N n} bd = BDNum
    binders-disjoint-σ-sym {e = X x} bd = BDVar
    binders-disjoint-σ-sym {e = ·λ x ·[ τ ] e} bd
      with lem-bd-σ-lam bd
    ... | ub , bd' = BDLam ub (binders-disjoint-σ-sym bd')
    binders-disjoint-σ-sym {e = e1 ∘ e2} bd
      with lem-bd-σ-ap bd
    ... | bd1 , bd2 =
      BDAp (binders-disjoint-σ-sym bd1)
           (binders-disjoint-σ-sym bd2)
    binders-disjoint-σ-sym {e = inl τ e} bd =
      BDInl (binders-disjoint-σ-sym (lem-bd-σ-inl bd))
    binders-disjoint-σ-sym {e = inr τ e} bd =
      BDInr (binders-disjoint-σ-sym (lem-bd-σ-inr bd))
    binders-disjoint-σ-sym {e = match e ·: τ of (rs-pre / r / rs-post)} bd
      with lem-bd-σ-match bd
    ... | bd' , bdpre , bdr , bdpost =
      BDMatch (binders-disjoint-σ-sym bd')
              (BDZRules (rs-binders-disjoint-σ-sym bdpre)
                        (BDRules (r-binders-disjoint-σ-sym bdr)
                                 (rs-binders-disjoint-σ-sym bdpost)))
    binders-disjoint-σ-sym {e = ⟨ e1 , e2 ⟩} bd
      with lem-bd-σ-pair bd
    ... | bd1 , bd2 =
      BDPair (binders-disjoint-σ-sym bd1)
             (binders-disjoint-σ-sym bd2)
    binders-disjoint-σ-sym {e = fst e} bd =
      BDFst (binders-disjoint-σ-sym (lem-bd-σ-fst bd))
    binders-disjoint-σ-sym {e = snd e} bd =
      BDSnd (binders-disjoint-σ-sym (lem-bd-σ-snd bd))
    binders-disjoint-σ-sym {e = ⦇-⦈⟨ u , σ ⟩} bd =
      BDEHole (σ-binders-disjoint-σ-sym (lem-bd-σ-ehole bd))
    binders-disjoint-σ-sym {e = ⦇⌜ e ⌟⦈⟨ u , σ ⟩} bd
      with lem-bd-σ-hole bd
    ... | bdσ , bde =
      BDHole (σ-binders-disjoint-σ-sym bdσ)
               (binders-disjoint-σ-sym bde)

    σ-binders-disjoint-σ-sym : {σ1 : subst-env} {σ2 : subst-env} →
                               binders-disjoint-σ σ1 σ2 →
                               binders-disjoint-σ σ2 σ1
    σ-binders-disjoint-σ-sym {σ2 = Id Γ} bd = BDσId
    σ-binders-disjoint-σ-sym {σ2 = Subst d y σ2} bd
      with lem-σ-bd-σ-subst bd
    ... | bdd , ub , bdσ' =
      BDσSubst (binders-disjoint-σ-sym bdd)
               ub
               (σ-binders-disjoint-σ-sym bdσ')
    
    rs-binders-disjoint-σ-sym : {σ : subst-env} {rs : rules} →
                                binders-disjoint-σ σ rs →
                                binders-disjoint-rs rs σ
    rs-binders-disjoint-σ-sym {rs = nil} bd = BDNoRules
    rs-binders-disjoint-σ-sym {rs = r / rs} bd
      with lem-rs-bd-σ bd
    ... | bdr , bdrs =
      BDRules (r-binders-disjoint-σ-sym bdr)
              (rs-binders-disjoint-σ-sym bdrs)

    r-binders-disjoint-σ-sym : {σ : subst-env} {r : rule} →
                               binders-disjoint-σ σ r →
                               binders-disjoint-r r σ
    r-binders-disjoint-σ-sym {r = p => e} bd
      with lem-r-bd-σ bd
    ... | bdp , bde =
      BDRule (p-binders-disjoint-σ-sym bdp)
             (binders-disjoint-σ-sym bde)

    p-binders-disjoint-σ-sym : {σ : subst-env} {p : pattrn} →
                               binders-disjoint-σ σ p →
                               binders-disjoint-p p σ
    p-binders-disjoint-σ-sym {p = unit} bd = BDPUnit
    p-binders-disjoint-σ-sym {p = N n} bd = BDPNum
    p-binders-disjoint-σ-sym {p = X x} bd =
      BDPVar (lem-p-bd-σ-var bd)
    p-binders-disjoint-σ-sym {p = inl p} bd =
      BDPInl (p-binders-disjoint-σ-sym (lem-p-bd-σ-inl bd))
    p-binders-disjoint-σ-sym {p = inr p} bd =
      BDPInr (p-binders-disjoint-σ-sym (lem-p-bd-σ-inr bd))
    p-binders-disjoint-σ-sym {p = ⟨ p1 , p2 ⟩} bd
      with lem-p-bd-σ-pair bd
    ... | bd1 , bd2 =
      BDPPair (p-binders-disjoint-σ-sym bd1)
              (p-binders-disjoint-σ-sym bd2)
    p-binders-disjoint-σ-sym {p = wild} bd = BDPWild
    p-binders-disjoint-σ-sym {p = ⦇-⦈[ w ]} bd = BDPEHole
    p-binders-disjoint-σ-sym {p = ⦇⌜ p ⌟⦈[ w , τ ]} bd =
      BDPHole (p-binders-disjoint-σ-sym (lem-p-bd-σ-hole bd))
    
  mutual
    binders-disjoint-rs-sym : {rs : rules} {e : ihexp} →
                              binders-disjoint-rs rs e →
                              binders-disjoint e rs
    binders-disjoint-rs-sym {e = unit} bd = BDUnit
    binders-disjoint-rs-sym {e = N n} bd = BDNum
    binders-disjoint-rs-sym {e = X x} bd = BDVar
    binders-disjoint-rs-sym {e = ·λ x ·[ τ ] e} bd
      with lem-bd-rs-lam bd
    ... | ub , bd' =
      BDLam ub (binders-disjoint-rs-sym bd')
    binders-disjoint-rs-sym {e = e1 ∘ e2} bd
      with lem-bd-rs-ap bd
    ... | bd1 , bd2 =
      BDAp (binders-disjoint-rs-sym bd1)
           (binders-disjoint-rs-sym bd2)
    binders-disjoint-rs-sym {e = inl τ e} bd =
      BDInl (binders-disjoint-rs-sym (lem-bd-rs-inl bd))
    binders-disjoint-rs-sym {e = inr τ e} bd =
      BDInr (binders-disjoint-rs-sym (lem-bd-rs-inr bd))
    binders-disjoint-rs-sym {e = match e ·: τ of (rs-pre / r / rs-post)} bd
      with lem-bd-rs-match bd
    ... | bd' , bdpre , bdr , bdpost =
      BDMatch (binders-disjoint-rs-sym bd')
              (BDZRules (rs-binders-disjoint-rs-sym bdpre)
                        (BDRules (r-binders-disjoint-rs-sym bdr)
                                 (rs-binders-disjoint-rs-sym bdpost)))
    binders-disjoint-rs-sym {e = ⟨ e1 , e2 ⟩} bd
      with lem-bd-rs-pair bd
    ... | bd1 , bd2 =
      BDPair (binders-disjoint-rs-sym bd1)
             (binders-disjoint-rs-sym bd2)
    binders-disjoint-rs-sym {e = fst e} bd =
      BDFst (binders-disjoint-rs-sym (lem-bd-rs-fst bd))
    binders-disjoint-rs-sym {e = snd e} bd =
      BDSnd (binders-disjoint-rs-sym (lem-bd-rs-snd bd))
    binders-disjoint-rs-sym {e = ⦇-⦈⟨ u , σ ⟩} bd =
      BDEHole (σ-binders-disjoint-rs-sym (lem-bd-rs-ehole bd))
    binders-disjoint-rs-sym {e = ⦇⌜ e ⌟⦈⟨ u , σ ⟩} bd
      with lem-bd-rs-hole bd
    ... | bdσ , bd' =
      BDHole (σ-binders-disjoint-rs-sym bdσ)
               (binders-disjoint-rs-sym bd')

    σ-binders-disjoint-rs-sym : {rs : rules} {σ : subst-env} →
                                binders-disjoint-rs rs σ →
                                binders-disjoint-σ σ rs
    σ-binders-disjoint-rs-sym {σ = Id Γ} bd = BDσId
    σ-binders-disjoint-rs-sym {σ = Subst d y σ} bd
      with lem-σ-bd-rs-subst bd
    ... | bd' , ub , bdσ = 
      BDσSubst (binders-disjoint-rs-sym bd')
               ub
               (σ-binders-disjoint-rs-sym bdσ)
    
    rs-binders-disjoint-rs-sym : {rs1 : rules} {rs2 : rules} →
                                 binders-disjoint-rs rs1 rs2 →
                                 binders-disjoint-rs rs2 rs1
    rs-binders-disjoint-rs-sym {rs2 = nil} bd = BDNoRules
    rs-binders-disjoint-rs-sym {rs2 = r2 / rs2} bd
      with lem-rs-bd-rs bd
    ... | bdr , bdrs =
      BDRules (r-binders-disjoint-rs-sym bdr)
              (rs-binders-disjoint-rs-sym bdrs)

    r-binders-disjoint-rs-sym : {rs : rules} {r : rule} →
                                binders-disjoint-rs rs r →
                                binders-disjoint-r r rs
    r-binders-disjoint-rs-sym {r = p => e} bd
      with lem-r-bd-rs bd
    ... | bdp , bde =
      BDRule (p-binders-disjoint-rs-sym bdp)
             (binders-disjoint-rs-sym bde)

    p-binders-disjoint-rs-sym : {rs : rules} {p : pattrn} →
                                binders-disjoint-rs rs p →
                                binders-disjoint-p p rs
    p-binders-disjoint-rs-sym {p = unit} bd = BDPUnit
    p-binders-disjoint-rs-sym {p = N n} bd = BDPNum
    p-binders-disjoint-rs-sym {p = X x} bd =
      BDPVar (lem-p-bd-rs-var bd)
    p-binders-disjoint-rs-sym {p = inl p} bd =
      BDPInl (p-binders-disjoint-rs-sym (lem-p-bd-rs-inl bd))
    p-binders-disjoint-rs-sym {p = inr p} bd =
      BDPInr (p-binders-disjoint-rs-sym (lem-p-bd-rs-inr bd))
    p-binders-disjoint-rs-sym {p = ⟨ p1 , p2 ⟩} bd
      with lem-p-bd-rs-pair bd
    ... | bd1 , bd2 =
      BDPPair (p-binders-disjoint-rs-sym bd1)
              (p-binders-disjoint-rs-sym bd2)
    p-binders-disjoint-rs-sym {p = wild} bd = BDPWild
    p-binders-disjoint-rs-sym {p = ⦇-⦈[ w ]} bd = BDPEHole
    p-binders-disjoint-rs-sym {p = ⦇⌜ p ⌟⦈[ w , τ ]} bd =
      BDPHole (p-binders-disjoint-rs-sym (lem-p-bd-rs-hole bd))

  mutual
    binders-disjoint-r-sym : {r : rule} {e : ihexp} →
                             binders-disjoint-r r e →
                             binders-disjoint e r
    binders-disjoint-r-sym {e = unit} bd = BDUnit
    binders-disjoint-r-sym {e = N n} bd = BDNum
    binders-disjoint-r-sym {e = X x} bd = BDVar
    binders-disjoint-r-sym {e = ·λ x ·[ τ ] e} bd
      with lem-bd-r-lam bd
    ... | ub , bd' =
      BDLam ub (binders-disjoint-r-sym bd')
    binders-disjoint-r-sym {e = e1 ∘ e2} bd
      with lem-bd-r-ap bd
    ... | bd1 , bd2 =
      BDAp (binders-disjoint-r-sym bd1)
           (binders-disjoint-r-sym bd2)
    binders-disjoint-r-sym {e = inl τ e} bd =
      BDInl (binders-disjoint-r-sym (lem-bd-r-inl bd))
    binders-disjoint-r-sym {e = inr τ e} bd =
      BDInr (binders-disjoint-r-sym (lem-bd-r-inr bd))
    binders-disjoint-r-sym {e = match e ·: τ of (rs-pre / r / rs-post)} bd
      with lem-bd-r-match bd
    ... | bd' , bdpre , bdr , bdpost =
      BDMatch (binders-disjoint-r-sym bd')
              (BDZRules (rs-binders-disjoint-r-sym bdpre)
                        (BDRules (r-binders-disjoint-r-sym bdr)
                                 (rs-binders-disjoint-r-sym bdpost)))
    binders-disjoint-r-sym {e = ⟨ e1 , e2 ⟩} bd
      with lem-bd-r-pair bd
    ... | bd1 , bd2 =
      BDPair (binders-disjoint-r-sym bd1)
             (binders-disjoint-r-sym bd2)
    binders-disjoint-r-sym {e = fst e} bd =
      BDFst (binders-disjoint-r-sym (lem-bd-r-fst bd))
    binders-disjoint-r-sym {e = snd e} bd =
      BDSnd (binders-disjoint-r-sym (lem-bd-r-snd bd))
    binders-disjoint-r-sym {e = ⦇-⦈⟨ u , σ ⟩} bd =
      BDEHole (σ-binders-disjoint-r-sym (lem-bd-r-ehole bd))
    binders-disjoint-r-sym {e = ⦇⌜ e ⌟⦈⟨ u , σ ⟩} bd
      with lem-bd-r-hole bd
    ... | bdσ , bd' =
      BDHole (σ-binders-disjoint-r-sym bdσ)
               (binders-disjoint-r-sym bd')

    σ-binders-disjoint-r-sym : {r : rule} {σ : subst-env} →
                               binders-disjoint-r r σ →
                               binders-disjoint-σ σ r
    σ-binders-disjoint-r-sym {σ = Id Γ} bd = BDσId
    σ-binders-disjoint-r-sym {σ = Subst d y σ} bd
      with lem-σ-bd-r-subst bd
    ... | bd' , ub , bdσ =
      BDσSubst (binders-disjoint-r-sym bd')
               ub
               (σ-binders-disjoint-r-sym bdσ)
    
    rs-binders-disjoint-r-sym : {r : rule} {rs : rules} →
                                binders-disjoint-r r rs →
                                binders-disjoint-rs rs r
    rs-binders-disjoint-r-sym {rs = nil} bd = BDNoRules
    rs-binders-disjoint-r-sym {rs = r / rs} bd
      with lem-rs-bd-r bd
    ... | bdr , bdrs =
      BDRules (r-binders-disjoint-r-sym bdr)
              (rs-binders-disjoint-r-sym bdrs)

    r-binders-disjoint-r-sym : {r1 : rule} {r2 : rule} →
                               binders-disjoint-r r1 r2 →
                               binders-disjoint-r r2 r1
    r-binders-disjoint-r-sym {r2 = p => e} bd
      with lem-r-bd-r bd
    ... | bdp , bde =
      BDRule (p-binders-disjoint-r-sym bdp)
             (binders-disjoint-r-sym bde)

    p-binders-disjoint-r-sym : {r : rule} {p : pattrn} →
                               binders-disjoint-r r p →
                               binders-disjoint-p p r
    p-binders-disjoint-r-sym {p = unit} bd = BDPUnit
    p-binders-disjoint-r-sym {p = N n} bd = BDPNum
    p-binders-disjoint-r-sym {p = X x} bd =
      BDPVar (lem-p-bd-r-var bd)
    p-binders-disjoint-r-sym {p = inl p} bd =
      BDPInl (p-binders-disjoint-r-sym (lem-p-bd-r-inl bd))
    p-binders-disjoint-r-sym {p = inr p} bd =
      BDPInr (p-binders-disjoint-r-sym (lem-p-bd-r-inr bd))
    p-binders-disjoint-r-sym {p = ⟨ p1 , p2 ⟩} bd
      with lem-p-bd-r-pair bd
    ... | bd1 , bd2 =
      BDPPair (p-binders-disjoint-r-sym bd1)
              (p-binders-disjoint-r-sym bd2)
    p-binders-disjoint-r-sym {p = wild} bd = BDPWild
    p-binders-disjoint-r-sym {p = ⦇-⦈[ w ]} bd = BDPEHole
    p-binders-disjoint-r-sym {p = ⦇⌜ p ⌟⦈[ w , τ ]} bd =
      BDPHole (p-binders-disjoint-r-sym (lem-p-bd-r-hole bd))
    
  mutual
    binders-disjoint-p-sym : {p : pattrn} {e : ihexp} →
                             binders-disjoint-p p e →
                             binders-disjoint e p
    binders-disjoint-p-sym {e = unit} bd = BDUnit
    binders-disjoint-p-sym {e = N n} bd = BDNum
    binders-disjoint-p-sym {e = X x} bd = BDVar
    binders-disjoint-p-sym {e = ·λ x ·[ τ ] e} bd
      with lem-bd-p-lam bd
    ... | ub , bd' =
      BDLam ub (binders-disjoint-p-sym bd')
    binders-disjoint-p-sym {e = e1 ∘ e2} bd
      with lem-bd-p-ap bd
    ... | bd1 , bd2 =
      BDAp (binders-disjoint-p-sym bd1)
           (binders-disjoint-p-sym bd2)
    binders-disjoint-p-sym {e = inl τ e} bd =
      BDInl (binders-disjoint-p-sym (lem-bd-p-inl bd))
    binders-disjoint-p-sym {e = inr τ e} bd =
      BDInr (binders-disjoint-p-sym (lem-bd-p-inr bd))
    binders-disjoint-p-sym {e = match e ·: τ of (rs-pre / r / rs-post)} bd
      with lem-bd-p-match bd
    ... | bd' , bdpre , bdr , bdpost =
      BDMatch (binders-disjoint-p-sym bd')
              (BDZRules (rs-binders-disjoint-p-sym bdpre)
                        (BDRules (r-binders-disjoint-p-sym bdr)
                                 (rs-binders-disjoint-p-sym bdpost)))
    binders-disjoint-p-sym {e = ⟨ e1 , e2 ⟩} bd
      with lem-bd-p-pair bd
    ... | bd1 , bd2 =
      BDPair (binders-disjoint-p-sym bd1)
             (binders-disjoint-p-sym bd2)
    binders-disjoint-p-sym {e = fst e} bd =
      BDFst (binders-disjoint-p-sym (lem-bd-p-fst bd))
    binders-disjoint-p-sym {e = snd e} bd =
      BDSnd (binders-disjoint-p-sym (lem-bd-p-snd bd))
    binders-disjoint-p-sym {e = ⦇-⦈⟨ u , σ ⟩} bd =
      BDEHole (σ-binders-disjoint-p-sym (lem-bd-p-ehole bd))
    binders-disjoint-p-sym {e = ⦇⌜ e ⌟⦈⟨ u , σ ⟩} bd
      with lem-bd-p-hole bd
    ... | bdσ , bd' =
      BDHole (σ-binders-disjoint-p-sym bdσ)
               (binders-disjoint-p-sym bd')

    σ-binders-disjoint-p-sym : {p : pattrn} {σ : subst-env} →
                               binders-disjoint-p p σ →
                               binders-disjoint-σ σ p
    σ-binders-disjoint-p-sym {σ = Id Γ} bd = BDσId
    σ-binders-disjoint-p-sym {σ = Subst d y σ} bd
      with lem-σ-bd-p-subst bd
    ... | bd' , ub , bdσ =
      BDσSubst (binders-disjoint-p-sym bd')
               ub
               (σ-binders-disjoint-p-sym bdσ)
    
    rs-binders-disjoint-p-sym : {p : pattrn} {rs : rules} →
                                binders-disjoint-p p rs →
                                binders-disjoint-rs rs p
    rs-binders-disjoint-p-sym {rs = nil} bd = BDNoRules
    rs-binders-disjoint-p-sym {rs = r / rs} bd
      with lem-rs-bd-p bd
    ... | bdr , bdrs =
      BDRules (r-binders-disjoint-p-sym bdr)
              (rs-binders-disjoint-p-sym bdrs)
    
    r-binders-disjoint-p-sym : {p : pattrn} {r : rule} →
                               binders-disjoint-p p r →
                               binders-disjoint-r r p
    r-binders-disjoint-p-sym {r = pr => er} bd
      with lem-r-bd-p bd
    ... | bdp , bde =
      BDRule (p-binders-disjoint-p-sym bdp)
             (binders-disjoint-p-sym bde)

    p-binders-disjoint-p-sym : {p1 : pattrn} {p2 : pattrn} →
                               binders-disjoint-p p1 p2 →
                               binders-disjoint-p p2 p1
    p-binders-disjoint-p-sym {p2 = unit} bd = BDPUnit
    p-binders-disjoint-p-sym {p2 = N n} bd = BDPNum
    p-binders-disjoint-p-sym {p2 = X x} bd =
      BDPVar (lem-p-bd-p-var bd)
    p-binders-disjoint-p-sym {p2 = inl p2} bd =
      BDPInl (p-binders-disjoint-p-sym (lem-p-bd-p-inl bd))
    p-binders-disjoint-p-sym {p2 = inr p2} bd =
      BDPInr (p-binders-disjoint-p-sym (lem-p-bd-p-inr bd))
    p-binders-disjoint-p-sym {p2 = ⟨ p2₁ , p2₂ ⟩} bd
      with lem-p-bd-p-pair bd
    ... | bd1 , bd2 =
      BDPPair (p-binders-disjoint-p-sym bd1)
              (p-binders-disjoint-p-sym bd2)
    p-binders-disjoint-p-sym {p2 = wild} bd = BDPWild
    p-binders-disjoint-p-sym {p2 = ⦇-⦈[ w ]} bd = BDPEHole
    p-binders-disjoint-p-sym {p2 = ⦇⌜ p2 ⌟⦈[ w , τ ]} bd =
      BDPHole (p-binders-disjoint-p-sym (lem-p-bd-p-hole bd))
  
