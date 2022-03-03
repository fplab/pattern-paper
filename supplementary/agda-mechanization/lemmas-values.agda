open import List
open import Nat
open import Prelude
open import constraints-core
open import contexts
open import core
open import dynamics-core
open import freshness
open import lemmas-satisfy
open import notintro-decidable
open import patterns-core
open import result-judgements
open import satisfy-decidable
open import statics-core
open import type-assignment-unicity
open import value-judgements
open import weakening

module lemmas-values where
  values-same-type : ∀{e e' Δ Δp τ} →
                     e' ∈[ Δ , Δp ]values e →
                     ∅ , Δ , Δp ⊢ e :: τ →
                     ∅ , Δ , Δp ⊢ e' :: τ
  values-same-type (IVVal eval wt₁) wt = wt
  values-same-type (IVIndet ni wt₁ eval' wt₁') wt
    with expr-type-unicity wt wt₁
  ... | refl = wt₁'
  values-same-type (IVInl ind (TInl wt₁) vals) (TInl wt)
    with expr-type-unicity wt wt₁
  ... | refl
    with values-same-type vals wt₁
  ... | wt₁' = TInl wt₁'
  values-same-type (IVInr ind (TInr wt₁) vals) (TInr wt)
    with expr-type-unicity wt wt₁
  ... | refl
    with values-same-type vals wt₁
  ... | wt₁' = TInr wt₁'
  values-same-type (IVPair ind (TPair wt1₁ wt2₁) vals1 vals2)
                   (TPair wt1 wt2)
    with expr-type-unicity wt1 wt1₁ | expr-type-unicity wt2 wt2₁
  ... | refl | refl
    with values-same-type vals1 wt1₁ | values-same-type vals2 wt2₁
  ... | wt1₁' | wt2₁' = TPair wt1₁' wt2₁'

  -- every value is val
  values-val : ∀{e e' Δ Δp} →
               e' ∈[ Δ , Δp ]values e →
               e' val
  values-val (IVVal eval wt) = eval
  values-val (IVIndet ni wt eval' wt') = eval'
  values-val (IVInl ind wt vals) = VInl (values-val vals)
  values-val (IVInr ind wt vals) = VInr (values-val vals)
  values-val (IVPair ind wt vals1 vals2) =
    VPair (values-val vals1) (values-val vals2)

  -- the only value of something which is val is itself
  val-values-self : ∀{e e' Δ Δp} →
                    e val →
                    e' ∈[ Δ , Δp ]values e →
                    e' == e
  val-values-self eval (IVVal eval₁ wt) = refl
  val-values-self eval (IVIndet ni wt e'val wt') =
    abort (val-notintro-not eval ni)
  val-values-self eval (IVInl ind wt vals) =
    abort (val-indet-not eval ind)
  val-values-self eval (IVInr ind wt vals) =
    abort (val-indet-not eval ind)
  val-values-self eval (IVPair ind wt vals1 vals2) =
    abort (val-indet-not eval ind)
  
  max-var : List Nat → Nat
  max-var [] = 0
  max-var (x :: xs) = max x (max-var xs)

  elem<sucmax : ∀{x xs} →
                x ∈l xs →
                x < suc (max-var xs)
  elem<sucmax {x = x} {xs = x :: xs} here =
    arg1<sucmax x (max-var xs)
  elem<sucmax {x = x} {xs = x' :: xs} (there x∈xs) =
    <-trans-suc (elem<sucmax x∈xs)
                (arg2<sucmax x' (max-var xs))

  -- there is an expression e of type τ such that e val,
  -- and moreover, all the elements of vars are fresh in e
  type-has-val : (τ : htyp) →
                 (vars : List Nat) →
                 (Δ : hctx) →
                 (Δp : phctx) →
                 Σ[ e ∈ ihexp ]
                   e val ×
                   (∅ , Δ , Δp ⊢ e :: τ) ×
                   (∀{x} → x ∈l vars → fresh x e)
  type-has-val unit vars Δ Δp =
    unit , VUnit , TUnit , λ _ → FUnit
  type-has-val num vars Δ Δp =
    N 0 , VNum , TNum , λ _ → FNum
  type-has-val (τ1 ==> τ2) vars Δ Δp
    with type-has-val τ2
                      (suc (max-var vars) :: vars)
                      Δ Δp
  ... | e2 , val2 , wt2 , frsh2 =
    (·λ (suc (max-var vars)) ·[ τ1 ] e2) , VLam ,
    TLam refl (weaken-ta-Γ (frsh2 here) wt2) ,
    λ x∈vars →
      FLam (<-≠ (elem<sucmax x∈vars))
           (frsh2 (there x∈vars))
  type-has-val (τ1 ⊕ τ2) vars Δ Δp
    with type-has-val τ1 vars Δ Δp
  ... | e1 , val1 , wt1 , frsh1 =
    inl τ2 e1 , VInl val1 , TInl wt1 ,
      λ x∈vars → FInl (frsh1 x∈vars)
  type-has-val (τ1 ⊠ τ2) vars Δ Δp
    with type-has-val τ1 vars Δ Δp |
         type-has-val τ2 vars Δ Δp
  ... | e1 , val1 , wt1 , frsh1
      | e2 , val2 , wt2 , frsh2 =
    ⟨ e1 , e2 ⟩ , VPair val1 val2 , TPair wt1 wt2 ,
    λ x∈vars → FPair (frsh1 x∈vars) (frsh2 x∈vars)

  -- every indet expression has some value
  indet-has-values : ∀{e Δ Δp τ} →
                     e indet →
                     ∅ , Δ , Δp ⊢ e :: τ →
                     Σ[ e' ∈ ihexp ] (e' ∈[ Δ , Δp ]values e)
  indet-has-values {Δ = Δ} {Δp = Δp} {τ = τ}
                   (IAp ind1 fin2) (TAp wt1 wt2)
    with type-has-val τ [] Δ Δp
  ... | e , eval , ewt , _ = e , IVIndet NVAp (TAp wt1 wt2) eval ewt
  indet-has-values (IInl ind) (TInl wt)
    with indet-has-values ind wt
  ... | e' , evals = inl _ e' , IVInl (IInl ind) (TInl wt) evals
  indet-has-values (IInr ind) (TInr wt)
    with indet-has-values ind wt
  ... | e' , evals = inr _ e' , IVInr (IInr ind) (TInr wt) evals
  indet-has-values {Δ = Δ} {Δp = Δp} {τ = τ}
                   (IMatch fin mp) wt
    with type-has-val τ [] Δ Δp
  ... | e , eval , ewt , _ = e , IVIndet NVMatch wt eval ewt
  indet-has-values {e = ⟨ e1 , e2 ⟩} (IPairL ind1 val2) (TPair wt1 wt2)
    with indet-has-values ind1 wt1
  ... | e1' , e1vals =
    ⟨ e1' , e2 ⟩ ,
    IVPair (IPairL ind1 val2) (TPair wt1 wt2) e1vals (IVVal val2 wt2)
  indet-has-values {e = ⟨ e1 , e2 ⟩} (IPairR val1 ind2) (TPair wt1 wt2)
    with indet-has-values ind2 wt2
  ... | e2' , e2vals = 
    ⟨ e1 , e2' ⟩ ,
    IVPair (IPairR val1 ind2) (TPair wt1 wt2) (IVVal val1 wt1) e2vals
  indet-has-values {e = ⟨ e1 , e2 ⟩} (IPair ind1 ind2) (TPair wt1 wt2)
    with indet-has-values ind1 wt1 | indet-has-values ind2 wt2
  ... | e1' , e1vals | e2' , e2vals =
    ⟨ e1' , e2' ⟩ ,
    IVPair (IPair ind1 ind2) (TPair wt1 wt2) e1vals e2vals
  indet-has-values {Δ = Δ} {Δp = Δp} {τ = τ} (IFst npr ind1) wt
    with type-has-val τ [] Δ Δp
  ... | e , eval , ewt , _ = e , IVIndet NVFst wt eval ewt
  indet-has-values {Δ = Δ} {Δp = Δp} {τ = τ} (ISnd npr ind2) wt
    with type-has-val τ [] Δ Δp
  ... | e , eval , ewt , _ = e , IVIndet NVSnd wt eval ewt
  indet-has-values {Δ = Δ} {Δp = Δp} {τ = τ} IEHole wt
    with type-has-val τ [] Δ Δp
  ... | e , eval , ewt , _ = e , IVIndet NVEHole wt eval ewt
  indet-has-values {Δ = Δ} {Δp = Δp} {τ = τ} (IHole x) wt
    with type-has-val τ [] Δ Δp
  ... | e , eval , ewt , _ = e , IVIndet NVHole wt eval ewt

  -- if an expression does not satormay a constraint,
  -- then neither does any of its values
  indet-values-not-satormay : ∀{e Δ Δp τ ξ e'} →
                              e indet →
                              e' ∈[ Δ , Δp ]values e →
                              ∅ , Δ , Δp ⊢ e :: τ →
                              ξ :c: τ →
                              (e ⊧̇†? ξ → ⊥) →
                              e' ⊧̇†? ξ →
                              ⊥
  indet-values-not-satormay ind vals wt CTTruth ¬satm satm' =
    ¬satm (CSMSSat CSTruth)
  indet-values-not-satormay ind vals wt CTFalsity ¬satm
                            (CSMSMay (CMSNotIntro _ _ ()))
  indet-values-not-satormay ind vals wt CTUnknown ¬satm satm' =
    ¬satm (CSMSMay CMSUnknown)
  indet-values-not-satormay (IAp ind1 fin2) vals wt CTNum ¬satm satm' =
    ¬satm (CSMSMay (CMSNotIntro NVAp RXNum PNum))
  indet-values-not-satormay (IMatch fin mp) vals wt CTNum ¬satm satm' =
    ¬satm (CSMSMay (CMSNotIntro NVMatch RXNum PNum))
  indet-values-not-satormay (IFst npr ind) vals wt CTNum ¬satm satm' =
    ¬satm (CSMSMay (CMSNotIntro NVFst RXNum PNum))
  indet-values-not-satormay (ISnd npr ind) vals wt CTNum ¬satm satm' =
    ¬satm (CSMSMay (CMSNotIntro NVSnd RXNum PNum))
  indet-values-not-satormay IEHole vals wt CTNum ¬satm satm' =
    ¬satm (CSMSMay (CMSNotIntro NVEHole RXNum PNum))
  indet-values-not-satormay (IHole fin) vals wt CTNum ¬satm satm' =
    ¬satm (CSMSMay (CMSNotIntro NVHole RXNum PNum))
  indet-values-not-satormay (IAp ind1 fin2) vals wt (CTInl ct) ¬satm satm' =
    ¬satm (CSMSMay (CMSNotIntro NVAp RXInl (satormay-pos satm')))
  indet-values-not-satormay (IInl ind) (IVVal eval wt₁) (TInl wt)
                            (CTInl ct) ¬satm satm' = ¬satm satm'
  indet-values-not-satormay (IInl ind) (IVInl ind₁ wt₁ vals) (TInl wt)
                            (CTInl ct) ¬satm satm' =
    indet-values-not-satormay ind vals wt ct
                              (λ satm → ¬satm (satormay-inl satm))
                              (inl-satormay satm')
  indet-values-not-satormay (IInr ind) (IVVal eval wt₁) (TInr wt)
                            (CTInl ct) ¬satm (CSMSMay (CMSNotIntro () _ _))
  indet-values-not-satormay (IInr ind) (IVInr ind₁ wt₁ vals) (TInr wt)
                            (CTInl ct) ¬satm (CSMSMay (CMSNotIntro () _ _))
  indet-values-not-satormay (IMatch fin mp) vals wt (CTInl ct) ¬satm satm' =
    ¬satm (CSMSMay (CMSNotIntro NVMatch RXInl (satormay-pos satm')))
  indet-values-not-satormay (IFst npr ind) vals wt (CTInl ct) ¬satm satm' =
    ¬satm (CSMSMay (CMSNotIntro NVFst RXInl (satormay-pos satm')))
  indet-values-not-satormay (ISnd npr ind) vals wt (CTInl ct) ¬satm satm' =
    ¬satm (CSMSMay (CMSNotIntro NVSnd RXInl (satormay-pos satm')))
  indet-values-not-satormay IEHole vals wt (CTInl ct) ¬satm satm' =
    ¬satm (CSMSMay (CMSNotIntro NVEHole RXInl (satormay-pos satm')))
  indet-values-not-satormay (IHole x) vals wt (CTInl ct) ¬satm satm' =
    ¬satm (CSMSMay (CMSNotIntro NVHole RXInl (satormay-pos satm')))
  indet-values-not-satormay (IAp ind x) vals wt (CTInr ct) ¬satm satm' =
    ¬satm (CSMSMay (CMSNotIntro NVAp RXInr (satormay-pos satm')))
  indet-values-not-satormay (IInl ind) (IVVal eval wt₁) (TInl wt)
                            (CTInr ct) ¬satm (CSMSMay (CMSNotIntro () _ _))
  indet-values-not-satormay (IInl ind) (IVInl ind₁ wt₁ vals) (TInl wt)
                            (CTInr ct) ¬satm (CSMSMay (CMSNotIntro () _ _))
  indet-values-not-satormay (IInr ind) (IVVal eval wt₁) (TInr wt)
                            (CTInr ct) ¬satm satm' = ¬satm satm'
  indet-values-not-satormay (IInr ind) (IVInr ind₁ wt₁ vals) (TInr wt)
                            (CTInr ct) ¬satm satm' =
    indet-values-not-satormay ind vals wt ct
                              (λ satm → ¬satm (satormay-inr satm))
                              (inr-satormay satm')
  indet-values-not-satormay (IMatch x x₁) vals wt (CTInr ct) ¬satm satm' =
    ¬satm (CSMSMay (CMSNotIntro NVMatch RXInr (satormay-pos satm')))
  indet-values-not-satormay (IFst npr ind) vals wt (CTInr ct) ¬satm satm' =
    ¬satm (CSMSMay (CMSNotIntro NVFst RXInr (satormay-pos satm')))
  indet-values-not-satormay (ISnd npr ind) vals wt (CTInr ct) ¬satm satm' =
    ¬satm (CSMSMay (CMSNotIntro NVSnd RXInr (satormay-pos satm')))
  indet-values-not-satormay IEHole vals wt (CTInr ct) ¬satm satm' =
    ¬satm (CSMSMay (CMSNotIntro NVEHole RXInr (satormay-pos satm')))
  indet-values-not-satormay (IHole x) vals wt (CTInr ct) ¬satm satm' =
    ¬satm (CSMSMay (CMSNotIntro NVHole RXInr (satormay-pos satm')))
  indet-values-not-satormay {e = e} {ξ = ⟨ ξ1 , ξ2 ⟩} ind vals wt
                            (CTPair ct1 ct2) ¬satm satm'
    with notintro-dec e
  ... | Inl ni 
    with satisfyormay-dec (fst e) ξ1
  ... | Inl satm1
    with satisfyormay-dec (snd e) ξ2
  ... | Inl satm2
    with satm1
  ... | CSMSMay msat1 =
    ¬satm (CSMSMay (CMSNotIntro ni
                                (RXPairL (notintro-maysat-ref NVFst msat1))
                                (satormay-pos satm')))
  ... | CSMSSat sat1
    with satm2
  ... | CSMSMay msat2 =
    ¬satm (CSMSMay (CMSNotIntro ni
                                (RXPairR (notintro-maysat-ref NVSnd msat2))
                                (satormay-pos satm')))
  ... | CSMSSat sat2 = ¬satm (CSMSSat (CSNotIntroPair ni sat1 sat2))
  
  indet-values-not-satormay {e = e} {ξ = ⟨ ξ1 , ξ2 ⟩} ind vals wt
                            (CTPair ct1 ct2) ¬satm satm' 
      | Inl ni | Inl satm1 | Inr ¬satm2
    with vals
  ... | IVVal eval wt₁ = val-notintro-not eval ni
  ... | IVIndet ni₁ wt₁ eval' wt'
    with expr-type-unicity wt wt₁
  ... | refl with eval'
  ... | VPair val1 val2
    with wt'
  ... | TPair wt1' wt2' =
    indet-values-not-satormay
     (ISnd (λ{e1 e2 refl → contra ni (λ ()) }) ind)
     (IVIndet NVSnd (TSnd wt) val2 wt2')
     (TSnd wt) ct2 ¬satm2 (π2 (pair-satormay satm'))
  indet-values-not-satormay {e = e} {ξ = ⟨ ξ1 , ξ2 ⟩} ind vals wt
                            (CTPair ct1 ct2) ¬satm satm' 
      | Inl ni | Inr ¬satm1
    with vals
  ... | IVVal eval wt₁ = val-notintro-not eval ni
  ... | IVIndet ni₁ wt₁ eval' wt'
    with expr-type-unicity wt wt₁
  ... | refl with eval'
  ... | VPair val1 val2
    with wt'
  ... | TPair wt1' wt2' =
    indet-values-not-satormay
      (IFst (λ{e1 e2 refl → contra ni (λ ())}) ind)
      (IVIndet NVFst (TFst wt) val1 wt1')
      (TFst wt) ct1 ¬satm1 (π1 (pair-satormay satm'))
  indet-values-not-satormay ind vals wt (CTPair ct1 ct2) ¬satm satm'
      | Inr ¬ni
    with vals
  ... | IVVal _ _ = ¬satm satm'
  ... | IVIndet ni _ _ _ = ¬ni ni
  ... | IVPair _ _ vals1 vals2
    with wt
  ... | TPair wt1 wt2
    with ind
  indet-values-not-satormay {e = ⟨ e1 , e2 ⟩} {ξ = ⟨ ξ1 , ξ2 ⟩}
                            ind vals wt (CTPair ct1 ct2) ¬satm satm'
      | Inr ¬ni | IVPair _ _ vals1 vals2 | TPair wt1 wt2 | IPair ind1 ind2
    with satisfyormay-dec e1 ξ1
  ... | Inr ¬sat1 =
    indet-values-not-satormay ind1 vals1 wt1 ct1 ¬sat1
                              (π1 (pair-satormay satm'))
  ... | Inl sat1
    with satisfyormay-dec e2 ξ2
  ... | Inl sat2 = ¬satm (satormay-pair sat1 sat2)
  ... | Inr ¬sat2 =
    indet-values-not-satormay ind2 vals2 wt2 ct2 ¬sat2
                              (π2 (pair-satormay satm'))
  indet-values-not-satormay {e = ⟨ e1 , e2 ⟩} {ξ = ⟨ ξ1 , ξ2 ⟩}
                            ind vals wt (CTPair ct1 ct2) ¬satm satm'
      | Inr ¬ni | IVPair _ _ vals1 vals2 | TPair wt1 wt2 | IPairL ind1 val2
    with satisfyormay-dec e1 ξ1
  ... | Inr ¬sat1 = 
    indet-values-not-satormay ind1 vals1 wt1 ct1 ¬sat1
                              (π1 (pair-satormay satm'))
  indet-values-not-satormay {e = ⟨ e1 , e2 ⟩} {ξ = ⟨ ξ1 , ξ2 ⟩}
                            ind vals wt (CTPair ct1 ct2) ¬satm satm'
      | Inr ¬ni | IVPair _ _ vals1 vals2 | TPair wt1 wt2 | IPairL ind1 val2
      | Inl sat1
    with satisfyormay-dec e2 ξ2
  ... | Inl sat2 = ¬satm (satormay-pair sat1 sat2)
  ... | Inr ¬sat2
    with vals2
  ... | IVVal _ _ = ¬sat2 (π2 (pair-satormay satm'))
  ... | IVIndet ni2 _ _ _ = val-notintro-not val2 ni2
  ... | IVInl ind2 _ _ = val-indet-not val2 ind2
  ... | IVInr ind2 _ _ = val-indet-not val2 ind2
  ... | IVPair ind2 _ _ _ = val-indet-not val2 ind2
  
  indet-values-not-satormay {e = ⟨ e1 , e2 ⟩} {ξ = ⟨ ξ1 , ξ2 ⟩}
                            ind vals wt (CTPair ct1 ct2) ¬satm satm'
      | Inr ¬ni | IVPair _ _ vals1 vals2 |  TPair wt1 wt2 | IPairR val1 ind2
    with satisfyormay-dec e2 ξ2
  ... | Inr ¬sat2 =
    indet-values-not-satormay ind2 vals2 wt2 ct2 ¬sat2
                              (π2 (pair-satormay satm'))
  ... | Inl sat2
    with satisfyormay-dec e1 ξ1
  ... | Inl sat1 = ¬satm (satormay-pair sat1 sat2)
  ... | Inr ¬sat1
    with vals1
  ... | IVVal _ _ = ¬sat1 (π1 (pair-satormay satm'))
  ... | IVIndet ni1 _ _ _ = val-notintro-not val1 ni1
  ... | IVInl ind1 _ _ = val-indet-not val1 ind1
  ... | IVInr ind1 _ _ = val-indet-not val1 ind1
  ... | IVPair ind1 _ _ _ = val-indet-not val1 ind1
  indet-values-not-satormay ind vals wt (CTOr ct1 ct2) ¬satm satm'
    with or-satormay satm'
  ... | Inl satm1' =
    indet-values-not-satormay ind vals wt ct1
                              (λ satm1 → ¬satm (satormay-or-l satm1)) satm1'
  ... | Inr satm2' =
    indet-values-not-satormay ind vals wt ct2
                              (λ satm2 → ¬satm (satormay-or-r satm2)) satm2'
  
