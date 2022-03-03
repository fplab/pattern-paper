open import List
open import Nat
open import Prelude
open import binders-disjointness
open import binders-disjoint-symmetric
open import binders-uniqueness
open import contexts
open import core
open import dynamics-core
open import freshness
open import lemmas-contexts
open import lemmas-freshness
open import patterns-core
open import statics-core

-- various lemmas about substitution lists
module lemmas-subst-list where
  -- applying a combined list of substitutions is the same
  -- as applying one list then applying the other
  apply-substs-concat : (θ1 θ2 : subst-list)
                        (e : ihexp) →
                        apply-substs (θ1 ++ θ2) e ==
                          apply-substs θ1 (apply-substs θ2 e)
  apply-substs-concat [] θ2 e = refl
  apply-substs-concat (( d , τ , y ) :: θ1) θ2 e =
    ap1 (λ qq → (·λ y ·[ τ ] qq) ∘ d) (apply-substs-concat θ1 θ2 e)

  -- the substituted variables in θ are unique,
  -- and none is a binder present in a substitued expression.
  -- this allows us to apply all the substitutions
  -- "simultaneously"
  data _simultaneous : (θ : subst-list) → Set where
    SθEmpty  : [] simultaneous
    SθExtend : ∀{d τ y θ} →
               unbound-in-θ y θ →
               θ simultaneous →
               ((d , τ , y) :: θ) simultaneous

  -- if θ1 and θ2 are simultaneous, then so is θ1 ++ θ2
  data jointly-simultaneous : (θ1 θ2 : subst-list) → Set where
    CθEmpty  : ∀{θ2} →
               jointly-simultaneous [] θ2
    CθExtend : ∀{d τ y θ1 θ2} →
               unbound-in-θ y θ2 →
               jointly-simultaneous θ1 θ2 →
               jointly-simultaneous ((d , τ , y) :: θ1) θ2

  -- concatting lists unions their typing assumptions
  substs-concat-type : ∀{Γ Δ Δp θ1 θ2 Γ1 Γ2} →
                       Γ , Δ , Δp ⊢ θ1 :sl: Γ1 →
                       Γ , Δ , Δp ⊢ θ2 :sl: Γ2 →
                       Γ , Δ , Δp ⊢ (θ1 ++ θ2) :sl: (Γ1 ∪ Γ2)
  substs-concat-type STEmpty st2 = st2
  substs-concat-type {Γ = Γ} {Δ = Δ} {Δp = Δp}
                   {θ1 = (d , τ , y) :: θ1} {θ2 = θ2} {Γ2 = Γ2}
                   (STExtend {Γθ = Γ1} {τ = τ} y#Γ1 st1 wt1) st2 =
    tr (λ qq → Γ , Δ , Δp ⊢ (d , τ , y) :: θ1 ++ θ2 :sl: qq)
       (! (∪-assoc (■ (y , τ)) Γ1 Γ2))
       (STExtend y#Γ1 (substs-concat-type st1 st2) wt1)

  -- if two lists are jointly simultanteous, then
  -- the combined list is simultaneous
  substs-concat-simultaneous : ∀{θ1 θ2} →
                               jointly-simultaneous θ1 θ2 →
                               θ1 simultaneous →
                               θ2 simultaneous →
                               (θ1 ++ θ2) simultaneous
  substs-concat-simultaneous CθEmpty SθEmpty sim2 = sim2
  substs-concat-simultaneous (CθExtend yubθ2 con)
                             (SθExtend yubθ sim1) sim2 =
    SθExtend (substs-concat-unbound-in yubθ yubθ2)
             (substs-concat-simultaneous con sim1 sim2)

  -- if each part of a list is jointly simultaneous with another
  -- list, then so is the whole list
  substs-concat-jointly-simultaneous : ∀{θ1 θ2 θ3} →
                                       jointly-simultaneous θ1 θ3 →
                                       jointly-simultaneous θ2 θ3 →
                                       jointly-simultaneous (θ1 ++ θ2) θ3
  substs-concat-jointly-simultaneous CθEmpty con2 = con2
  substs-concat-jointly-simultaneous (CθExtend yub3 con1) con2 =
    CθExtend yub3 (substs-concat-jointly-simultaneous con1 con2)

  -- disjoint expression matches emit jointly simultaneous
  -- substitution lists
  mat-substs-jointly-simultaneous : ∀{e1 e2 τ1 τ2 p1 p2 θ1 θ2} →
                                    binders-disjoint-p p1 p2 →
                                    binders-disjoint-p p1 e2 →
                                    e1 ·: τ1 ▹ p1 ⊣ θ1 →
                                    e2 ·: τ2 ▹ p2 ⊣ θ2 →
                                    jointly-simultaneous θ1 θ2
  mat-substs-jointly-simultaneous p1bdp2 p1bde2 MUnit mat2 = CθEmpty
  mat-substs-jointly-simultaneous p1bdp2 p1bde2 MNum mat2 = CθEmpty
  mat-substs-jointly-simultaneous (BDPVar xubp2) (BDPVar xube2) MVar mat2 =
    CθExtend (unbound-in-mat-substs xube2 xubp2 mat2) CθEmpty
  mat-substs-jointly-simultaneous (BDPInl p1bdp2) (BDPInl p1bde2) (MInl mat1) mat2 =
    mat-substs-jointly-simultaneous p1bdp2 p1bde2 mat1 mat2
  mat-substs-jointly-simultaneous (BDPInr p1bdp2) (BDPInr p1bde2) (MInr mat1) mat2 =
    mat-substs-jointly-simultaneous p1bdp2 p1bde2 mat1 mat2
  mat-substs-jointly-simultaneous (BDPPair p1₁bdp2 p1₂bdp2)
                        (BDPPair p1₁bde2 p1₂bde2)
                        (MPair {e1 = e1₁} {e2 = e1₂}
                               {τ1 = τ1₁} {τ2 = τ1₂}
                               {p1 = p1₁} {p2 = p1₂}
                               {θ1 = θ1₁} {θ2 = θ1₂}
                               mat1₁ mat1₂)
                        mat2 =
    substs-concat-jointly-simultaneous
      (mat-substs-jointly-simultaneous p1₁bdp2 p1₁bde2 mat1₁ mat2)
      (mat-substs-jointly-simultaneous p1₂bdp2 p1₂bde2 mat1₂ mat2)
  mat-substs-jointly-simultaneous (BDPPair p1₁bdp2 p1₂bdp2)
                        (BDPPair p1₁bde2 p1₂bde2)
                        (MNotIntroPair {τ1 = τ1₁} {τ2 = τ1₂}
                                       {p1 = p1₁} {p2 = p1₂}
                                       {θ1 = θ1₁} {θ2 = θ1₂}
                                       ni mat1₁ mat1₂)
                        mat2 =
    substs-concat-jointly-simultaneous
      (mat-substs-jointly-simultaneous p1₁bdp2 p1₁bde2 mat1₁ mat2)
      (mat-substs-jointly-simultaneous p1₂bdp2 p1₂bde2 mat1₂ mat2)
  mat-substs-jointly-simultaneous p1bdp2 p1bde2 MWild mat2 = CθEmpty

  -- a single match expression emits a simultaneous list of
  -- substitutions
  mat-substs-simultaneous : ∀{e τ p θ} →
                            binders-unique e →
                            binders-unique-p p →
                            binders-disjoint-p p e →
                            (e ·: τ ▹ p ⊣ θ) →
                            θ simultaneous
  mat-substs-simultaneous bue bup bd MUnit = SθEmpty
  mat-substs-simultaneous bue bup bd MNum = SθEmpty
  mat-substs-simultaneous bue bup bd MVar =
    SθExtend UBθEmpty SθEmpty
  mat-substs-simultaneous (BUInl bue) (BUPInl bup)
                          (BDPInl pbdie) (MInl mat)
    with binders-disjoint-p-sym pbdie
  ... | BDInl ebdp =
    mat-substs-simultaneous bue bup
                            (p-binders-disjoint-sym ebdp)
                            mat
  mat-substs-simultaneous (BUInr bue) (BUPInr bup)
                          (BDPInr pbdie) (MInr mat)
    with binders-disjoint-p-sym pbdie
  ... | BDInr ebdp =
    mat-substs-simultaneous bue bup
                            (p-binders-disjoint-sym ebdp)
                            mat
  mat-substs-simultaneous (BUPair bue1 bue2 e1bde2)
                          (BUPPair bup1 bup2 p1bdp2)
                          (BDPPair p1bde p2bde)
                          (MPair mat1 mat2)
    with binders-disjoint-p-sym p1bde |
         binders-disjoint-p-sym p2bde
  ... | BDPair e1bdp1 e2bdp1 | BDPair e1bdp2 e2bdp2 =
    substs-concat-simultaneous
      (mat-substs-jointly-simultaneous
        p1bdp2
        (p-binders-disjoint-sym e2bdp1)
        mat1 mat2)
      (mat-substs-simultaneous
        bue1 bup1
        (p-binders-disjoint-sym e1bdp1)
        mat1)
      (mat-substs-simultaneous
        bue2 bup2
        (p-binders-disjoint-sym e2bdp2)
        mat2)
  mat-substs-simultaneous bue
                          (BUPPair bup1 bup2 p1bdp2)
                          (BDPPair p1bde p2bde)
                          (MNotIntroPair ni mat1 mat2) =
    substs-concat-simultaneous
      (mat-substs-jointly-simultaneous
        p1bdp2
        (p-binders-disjoint-sym (BDSnd (binders-disjoint-p-sym p1bde)))
        mat1 mat2)
      (mat-substs-simultaneous
        (BUFst bue) bup1
        (p-binders-disjoint-sym (BDFst (binders-disjoint-p-sym p1bde)))
        mat1)
      (mat-substs-simultaneous
        (BUSnd bue) bup2
        (p-binders-disjoint-sym (BDSnd (binders-disjoint-p-sym p2bde)))
        mat2)
  mat-substs-simultaneous bue bup bd MWild = SθEmpty
  
