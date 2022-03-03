open import List
open import Nat
open import Prelude
open import constraints-core
open import contexts
open import core
open import exchange
open import freshness
open import lemmas-contexts
open import lemmas-freshness
open import patterns-core
open import statics-core
open import result-judgements

module weakening where
  mutual
    weaken-ta-∪Γ : ∀{Γ' Γ Δ Δp e τ} →
                   (∀{x} →
                    dom Γ' x →
                    fresh x e) →
                    Γ , Δ , Δp ⊢ e :: τ →
                   (Γ' ∪ Γ) , Δ , Δp ⊢ e :: τ
    weaken-ta-∪Γ frsh TUnit = TUnit
    weaken-ta-∪Γ frsh TNum = TNum
    weaken-ta-∪Γ {Γ' = Γ'} {Γ = Γ} {τ = τ} frsh (TVar {x = x} x∈Γ)
      with Γ' x in Γ'x
    ... | None = TVar (dom-r-union Γ' Γ x τ x∈Γ Γ'x)
    ... | Some τ'
      with frsh (τ' , Γ'x)
    ... | FVar x≠x = abort (x≠x refl)
    weaken-ta-∪Γ {Γ' = Γ'} {Γ = Γ} {Δ = Δ} {e = ·λ x ·[ τ1 ] e}
                 frsh (TLam {τ2 = τ2} x#Γ wt)
      with Γ' x in Γ'x
    ... | Some τ'
      with frsh (τ' , Γ'x)
    ... | FLam x≠x f = abort (x≠x refl)
    weaken-ta-∪Γ {Γ' = Γ'} {Γ = Γ} {Δ = Δ} {Δp = Δp}
                 {e = ·λ x ·[ τ1 ] e}
                 frsh (TLam {τ2 = τ2} x#Γ wt)
        | None =
      TLam (apart-parts Γ' Γ x Γ'x x#Γ)
            (tr (λ qq → qq , Δ , Δp ⊢ e :: τ2) eq
                (weaken-ta-∪Γ frsh' wt))
      where
        frsh' : ∀{z} →
                dom Γ' z →
                fresh z e
        frsh' z∈Γ' with frsh z∈Γ'
        ... | FLam z≠x f = f
        
        eq : Γ' ∪ (Γ ,, (x , τ1)) == (Γ' ∪ Γ) ,, (x , τ1)
        eq = ! (∪-assoc Γ' (■ (x , τ1)) Γ) ·
             (ap1 (λ qq → qq ∪ Γ)
                  (∪-comm Γ' (■ (x , τ1))
                         (##-sym (apart-singleton-disjoint Γ'x))) ·
              (∪-assoc (■ (x , τ1)) Γ' Γ))
    weaken-ta-∪Γ {Γ' = Γ'} {e = e1 ∘ e2} frsh (TAp wt1 wt2) =
      TAp (weaken-ta-∪Γ frsh1 wt1)
           (weaken-ta-∪Γ frsh2 wt2)
      where
        frsh1 : ∀{z} →
                dom Γ' z →
                fresh z e1
        frsh1 z∈Γ' with frsh z∈Γ'
        ... | FAp f1 f2 = f1
        frsh2 : ∀{z} →
                dom Γ' z →
                fresh z e2
        frsh2 z∈Γ' with frsh z∈Γ'
        ... | FAp f1 f2 = f2
    weaken-ta-∪Γ {Γ' = Γ'} {e = inl τ1 e} frsh (TInl wt) =
      TInl (weaken-ta-∪Γ frsh' wt)
      where
        frsh' : ∀{z} →
                dom Γ' z →
                fresh z e
        frsh' z∈Γ' with frsh z∈Γ'
        ... | FInl f = f
    weaken-ta-∪Γ {Γ' = Γ'} {e = inr τ e} frsh (TInr wt) = 
      TInr (weaken-ta-∪Γ frsh' wt)
      where
        frsh' : ∀{z} →
                dom Γ' z →
                fresh z e
        frsh' z∈Γ' with frsh z∈Γ'
        ... | FInr f = f
    weaken-ta-∪Γ {Γ' = Γ'} {e = match e ·: τ of (nil / r / rs)}
                 frsh (TMatchZPre wt rst) =
      TMatchZPre (weaken-ta-∪Γ frsh' wt)
                  (weaken-rules-∪Γ frshr rst)
      where
        frsh' : ∀{z} →
                dom Γ' z →
                fresh z e
        frsh' z∈Γ' with frsh z∈Γ'
        ... | FMatch f frs = f
        frshr : ∀{z} →
                dom Γ' z →
                fresh-rs z (r / rs)
        frshr z∈Γ' with frsh z∈Γ'
        ... | FMatch f (FZRules FNoRules (FRules fr frs)) = FRules fr frs
    weaken-ta-∪Γ {Γ' = Γ'} {e = match e ·: τ of (rs-pre / r / rs-post)}
                 frsh (TMatchNZPre wt fin pret postt ¬red) =
      TMatchNZPre (weaken-ta-∪Γ frsh' wt)
                   fin
                   (weaken-rules-∪Γ frshpre pret)
                   (weaken-rules-∪Γ frshpost postt)
                   ¬red
      where
        frsh' : ∀{z} →
                dom Γ' z →
                fresh z e
        frsh' z∈Γ' with frsh z∈Γ'
        ... | FMatch f frs = f
        frshpre : ∀{z} →
                  dom Γ' z →
                  fresh-rs z rs-pre
        frshpre z∈Γ' with frsh z∈Γ'
        ... | FMatch f (FZRules fpre (FRules fr fpost)) = fpre
        frshpost : ∀{z} →
                   dom Γ' z →
                   fresh-rs z (r / rs-post)
        frshpost z∈Γ' with frsh z∈Γ'
        ... | FMatch f (FZRules fpre (FRules fr fpost)) = FRules fr fpost
    weaken-ta-∪Γ {Γ' = Γ'} {e = ⟨ e1 , e2 ⟩} frsh (TPair wt1 wt2) = 
      TPair (weaken-ta-∪Γ frsh1 wt1)
           (weaken-ta-∪Γ frsh2 wt2)
      where
        frsh1 : ∀{z} →
                dom Γ' z →
                fresh z e1
        frsh1 z∈Γ' with frsh z∈Γ'
        ... | FPair f1 f2 = f1
        frsh2 : ∀{z} →
                dom Γ' z →
                fresh z e2
        frsh2 z∈Γ' with frsh z∈Γ'
        ... | FPair f1 f2 = f2
    weaken-ta-∪Γ {Γ' = Γ'} {e = fst e} frsh (TFst wt) =
      TFst (weaken-ta-∪Γ frsh' wt)
      where
        frsh' : ∀{z} →
                dom Γ' z →
                fresh z e
        frsh' z∈Γ' with frsh z∈Γ'
        ... | FFst f = f 
    weaken-ta-∪Γ {Γ' = Γ'} {e = snd e} frsh (TSnd wt) =
      TSnd (weaken-ta-∪Γ frsh' wt)
      where
        frsh' : ∀{z} →
                dom Γ' z →
                fresh z e
        frsh' z∈Γ' with frsh z∈Γ'
        ... | FSnd f = f 
    weaken-ta-∪Γ {Γ' = Γ'} {e = ⦇-⦈⟨ u , σ ⟩} frsh (TEHole u∈Δ st) =
      TEHole u∈Δ (weaken-σ-∪Γ frshσ st)
      where
        frshσ : ∀{z} →
                dom Γ' z →
                fresh-σ z σ
        frshσ z∈Γ' with frsh z∈Γ'
        ... | FEHole hfσ = hfσ
    weaken-ta-∪Γ {Γ' = Γ'} {e = ⦇⌜ e ⌟⦈⟨ u , σ ⟩} frsh (THole u∈Δ st wt) =
      THole u∈Δ
               (weaken-σ-∪Γ frshσ st)
               (weaken-ta-∪Γ frsh' wt) 
      where
        frshσ : ∀{z} →
                dom Γ' z →
                fresh-σ z σ
        frshσ z∈Γ' with frsh z∈Γ'
        ... | FHole hfσ hf = hfσ
        frsh' : ∀{z} →
                dom Γ' z →
                fresh z e
        frsh' z∈Γ' with frsh z∈Γ'
        ... | FHole hfσ hf = hf

    weaken-θ-∪Γ : ∀{Γ' Γ Δ Δp θ Γθ} →
                  (∀{x} →
                   dom Γ' x →
                   fresh-θ x θ) →
                  Γ , Δ , Δp ⊢ θ :sl: Γθ →
                  (Γ' ∪ Γ) , Δ , Δp ⊢ θ :sl: Γθ
    weaken-θ-∪Γ frshθ STEmpty = STEmpty
    weaken-θ-∪Γ {Γ' = Γ'} {Γ = Γ} frshθ
                (STExtend {θ = θ} {d = d} {y = y} y#Γ wst wt) =
      STExtend (apart-parts Γ' Γ y y#Γ' y#Γ)
                (weaken-θ-∪Γ {Γ' = Γ'} frshθ' wst)
                (weaken-ta-∪Γ {Γ' = Γ'} frsh wt)
      where
        y#Γ' : y # Γ'
        y#Γ' with Γ' y in Γ'y
        ... | None = refl
        ... | Some τ'
          with frshθ (τ' , Γ'y)
        ... | FθExtend f x≠y fθ = abort (x≠y refl)
        
        frshθ' : ∀{x} →
                 dom Γ' x →
                 fresh-θ x θ
        frshθ' x∈Γ' with frshθ x∈Γ'
        ... | FθExtend f x≠y fθ = fθ
        frsh : ∀{x} →
               dom Γ' x →
               fresh x d
        frsh x∈Γ' with frshθ x∈Γ'
        ... | FθExtend f x≠y fθ = f
       
    weaken-σ-∪Γ : ∀{Γ' Γ Δ Δp σ Γσ} →
                  (∀{x} →
                   dom Γ' x →
                   fresh-σ x σ) →
                  Γ , Δ , Δp ⊢ σ :se: Γσ →
                  (Γ' ∪ Γ) , Δ , Δp ⊢ σ :se: Γσ
    weaken-σ-∪Γ {Γ' = Γ'} {Γ = Γ} {Γσ = Γσ}
                frsh (STId Γσ⊆Γ) =
      STId Γσ⊆Γ'∪Γ
      where
        Γσ⊆Γ'∪Γ : (x : Nat) (τ : htyp) →
                  (x , τ) ∈ Γσ →
                  (x , τ) ∈ (Γ' ∪ Γ)
        Γσ⊆Γ'∪Γ x τ x∈Γσ
          with Γ' x in Γ'x
        ... | None = Γσ⊆Γ x τ x∈Γσ
        ... | Some τ'
          with frsh (τ' , Γ'x)
        ... | FσId x#Γσ = abort (some-not-none (! x∈Γσ · x#Γσ))
    weaken-σ-∪Γ {Γ' = Γ'} {Γ = Γ} {Δ = Δ} {Δp = Δp}
                {σ = Subst d y σ} {Γσ = Γσ}
                frsh (STSubst {τ = τ} st wt) =
      STSubst (tr (λ qq → qq , Δ , Δp ⊢ σ :se: Γσ)
                   ((! (∪-assoc Γ' (■ (y , τ)) Γ) ·
                     ap1 (λ qq → qq ∪ Γ)
                         (∪-comm Γ'
                                 (■ (y , τ))
                                 (##-sym
                                   (apart-singleton-disjoint y#Γ')))) ·
                     ∪-assoc (■ (y , τ)) Γ' Γ)
                   (weaken-σ-∪Γ {Γ' = Γ'} frshσ st))
               (weaken-ta-∪Γ frsh' wt)
      where
        y#Γ' : y # Γ'
        y#Γ' with Γ' y in Γ'y
        ... | None = refl
        ... | Some τ with frsh (τ , Γ'y)
        ... | FσSubst f y≠y fσ = abort (y≠y refl) 
        frshσ : ∀{z} →
                dom Γ' z  →
                fresh-σ z σ
        frshσ z∈Γ' with frsh z∈Γ'
        ... | FσSubst f z≠y fσ = fσ
        frsh' : ∀{z} →
                dom Γ' z →
                fresh z d
        frsh' z∈Γ' with frsh z∈Γ'
        ... | FσSubst f z≠y fσ = f
              
    weaken-rules-∪Γ : ∀{Γ' Γ Δ Δp rs τ1 ξ τ2} →
                      (∀{x} →
                       dom Γ' x →
                       fresh-rs x rs) →
                      Γ , Δ , Δp ⊢ rs ::s τ1 [ ξ ]=> τ2 →
                      (Γ' ∪ Γ) , Δ , Δp ⊢ rs ::s τ1 [ ξ ]=> τ2
    weaken-rules-∪Γ {Γ' = Γ'} frsh (RTOneRule {r = p => e} rt) =
      RTOneRule (weaken-rule-∪Γ frsh' rt)
      where
        frsh' : ∀{z} →
                dom Γ' z →
                fresh-r z (p => e)
        frsh' z∈Γ' with frsh z∈Γ'
        ... | FRules fr frs = fr
    weaken-rules-∪Γ {Γ' = Γ'} frsh (RTRules {r = r} {rs = rs} rt rst) =
      RTRules (weaken-rule-∪Γ frshr rt)
              (weaken-rules-∪Γ frshrs rst)
      where
        frshr : ∀{z} →
                dom Γ' z →
                fresh-r z r
        frshr z∈Γ' with frsh z∈Γ'
        ... | FRules f frs = f
        frshrs : ∀{z} →
                 dom Γ' z →
                 fresh-rs z rs
        frshrs z∈Γ' with frsh z∈Γ'
        ... | FRules f frs = frs
    
    weaken-rule-∪Γ : ∀{Γ' Γ Δ Δp r τ1 ξ τ2} →
                     (∀{x} →
                      dom Γ' x →
                      fresh-r x r) →
                     Γ , Δ , Δp ⊢ r :: τ1 [ ξ ]=> τ2 →
                     (Γ' ∪ Γ) , Δ , Δp ⊢ r :: τ1 [ ξ ]=> τ2
    weaken-rule-∪Γ {Γ' = Γ'} {Γ = Γ} {Δ = Δ} {Δp = Δp}
                   {τ2 = τ2} frsh
                   (RTRule {e = e} {Γp = Γp} 
                           pt Γ##Γp wt) =
      RTRule pt
             (disjoint-parts Γ'##Γp Γ##Γp)
             (tr (λ qq → qq , Δ , Δp ⊢ e :: τ2)
                 (! (∪-assoc Γ' Γ Γp))
                 (weaken-ta-∪Γ frsh' wt))
      where
        Γ'##Γp : Γ' ## Γp
        Γ'##Γp = disj1 , disj2
          where
            disj1 : (x : Nat) →
                    dom Γ' x →
                    x # Γp
            disj1 x x∈Γ' with frsh x∈Γ'
            ... | FRule ub f = unbound-in-p-apart-Γp pt ub
            disj2 : (x : Nat) →
                    dom Γp x →
                    x # Γ'
            disj2 x x∈Γp
              with Γ' x in Γ'x
            ... | None = refl
            ... | Some τ1 
              with disj1 x (τ1 , Γ'x)
            ... | x#Γp = abort (some-not-none (! (π2 x∈Γp) · x#Γp))

        frsh' : ∀{z} →
                dom Γ' z →
                fresh z e
        frsh' z∈Γ' with frsh z∈Γ'
        ... | FRule ub f = f
    
    -- Commutativity of union requires disjointness, so we
    -- make use of th identity
    -- Γ ∪ Γ' = Γ ⊔ (Γ' \ Γ) = (Γ' \ Γ) ⊔ Γ
    weaken-ta-Γ∪ : ∀{Γ Γ' Δ Δp e τ} →
                   (∀{x} →
                    dom Γ' x →
                    fresh x e) →
                   Γ , Δ , Δp ⊢ e :: τ →
                   (Γ ∪ Γ') , Δ , Δp ⊢ e :: τ
    weaken-ta-Γ∪ {Γ = Γ} {Γ' = Γ'} {Δ = Δ} {Δp = Δp}
                 {e = e} {τ = τ} frsh wt =
      tr (λ qq → qq , Δ , Δp ⊢ e :: τ)
         (! (union-with-diff Γ Γ' ·
             ∪-comm Γ (Γ' ∖ Γ) (r-disjoint-diff-r Γ' Γ)))
         (weaken-ta-∪Γ frsh' wt)
      where
        frsh' : ∀{z} →
                dom (Γ' ∖ Γ) z →
                fresh z e
        frsh' {z = z} (τ , z∈Γ'∖Γ) =
          frsh (τ , dom-diff-dom-l {Γ1 = Γ'} {Γ2 = Γ} z∈Γ'∖Γ)
         
    -- convenience functions
    weaken-ta-Γ : ∀{Γ x τ' Δ Δp e τ} →
                  fresh x e →
                  Γ , Δ , Δp ⊢ e :: τ →
                  (Γ ,, (x , τ')) , Δ , Δp ⊢ e :: τ
    weaken-ta-Γ {x = x} {τ' = τ'} {e = e} frsh wt =
      weaken-ta-∪Γ frsh' wt
      where
        frsh' : ∀{z} →
                dom (■ (x , τ')) z →
                fresh z e
        frsh' d with dom-singleton-eq d
        ... | refl = frsh

  mutual
    weaken-ta-∪Δ : ∀{Γ Δ' Δ Δp e τ} →
                   (∀{u} →
                    dom Δ' u →
                    hole-fresh u e) →
                   Γ , Δ , Δp ⊢ e :: τ →
                   Γ , (Δ' ∪ Δ) , Δp ⊢ e :: τ
    weaken-ta-∪Δ frsh TUnit = TUnit
    weaken-ta-∪Δ frsh TNum = TNum
    weaken-ta-∪Δ frsh (TVar x∈Γ) = TVar x∈Γ
    weaken-ta-∪Δ {Δ' = Δ'} {e = ·λ x ·[ τ1 ] e}
                 frsh (TLam x#Γ wt) =
      TLam x#Γ
            (weaken-ta-∪Δ frsh' wt)
      where
        frsh' : ∀{z} →
                dom Δ' z →
                hole-fresh z e
        frsh' z∈Δ' with frsh z∈Δ'
        ... | HFLam hf = hf
    weaken-ta-∪Δ {Δ' = Δ'} {e = e1 ∘ e2} frsh (TAp wt1 wt2) =
      TAp (weaken-ta-∪Δ frsh1 wt1)
           (weaken-ta-∪Δ frsh2 wt2)
      where
        frsh1 : ∀{z} →
                dom Δ' z →
                hole-fresh z e1
        frsh1 z∈Δ' with frsh z∈Δ'
        ... | HFAp hf1 hf2 = hf1
        frsh2 : ∀{z} →
                dom Δ' z →
                hole-fresh z e2
        frsh2 z∈Δ' with frsh z∈Δ'
        ... | HFAp hf1 hf2 = hf2
    weaken-ta-∪Δ {Δ' = Δ'} {e = inl τ1 e} frsh (TInl wt) =
      TInl (weaken-ta-∪Δ frsh' wt)
      where
        frsh' : ∀{z} →
                dom Δ' z →
                hole-fresh z e
        frsh' z∈Δ' with frsh z∈Δ'
        ... | HFInl hf = hf
    weaken-ta-∪Δ {Δ' = Δ'} {e = inr τ1 e} frsh (TInr wt) =
      TInr (weaken-ta-∪Δ frsh' wt)
      where
        frsh' : ∀{z} →
                dom Δ' z →
                hole-fresh z e
        frsh' z∈Δ' with frsh z∈Δ'
        ... | HFInr hf = hf
    weaken-ta-∪Δ {Δ' = Δ'} {e = match e ·: τ of (nil / r / rs)}
                 frsh (TMatchZPre wt rst) =
      TMatchZPre (weaken-ta-∪Δ frsh' wt)
                  (weaken-rules-∪Δ frshr rst)
      where
        frsh' : ∀{z} →
                dom Δ' z →
                hole-fresh z e
        frsh' z∈Δ' with frsh z∈Δ'
        ... | HFMatch hf hfrs = hf
        frshr : ∀{z} →
                dom Δ' z →
                hole-fresh-rs z (r / rs)
        frshr z∈Δ' with frsh z∈Δ'
        ... | HFMatch hf (HFZRules HFNoRules (HFRules hfr hfrs)) =
          HFRules hfr hfrs
    weaken-ta-∪Δ {Δ' = Δ'} {e = match e ·: τ of (rs-pre / r / rs-post)}
                 frsh (TMatchNZPre wt fin pret postt ¬red) =
      TMatchNZPre (weaken-ta-∪Δ frsh' wt)
                   fin
                   (weaken-rules-∪Δ frshpre pret)
                   (weaken-rules-∪Δ frshpost postt)
                   ¬red
      where
        frsh' : ∀{z} →
                dom Δ' z →
                hole-fresh z e
        frsh' z∈Δ' with frsh z∈Δ'
        ... | HFMatch hf hfrs = hf
        frshpre : ∀{z} →
                  dom Δ' z →
                  hole-fresh-rs z rs-pre
        frshpre z∈Δ' with frsh z∈Δ'
        ... | HFMatch hf (HFZRules hfpre (HFRules hfr hfpost)) = hfpre
        frshpost : ∀{z} →
                   dom Δ' z →
                   hole-fresh-rs z (r / rs-post)
        frshpost z∈Δ' with frsh z∈Δ'
        ... | HFMatch hf (HFZRules hfpre (HFRules hfr hfpost)) =
          HFRules hfr hfpost
    weaken-ta-∪Δ {Δ' = Δ'} {e = ⟨ e1 , e2 ⟩} frsh (TPair wt1 wt2) =
      TPair (weaken-ta-∪Δ frsh1 wt1)
             (weaken-ta-∪Δ frsh2 wt2)
      where
        frsh1 : ∀{z} →
                dom Δ' z →
                hole-fresh z e1
        frsh1 z∈Δ' with frsh z∈Δ'
        ... | HFPair hf1 hf2 = hf1
        frsh2 : ∀{z} →
                dom Δ' z →
                hole-fresh z e2
        frsh2 z∈Δ' with frsh z∈Δ'
        ... | HFPair hf1 hf2 = hf2
    weaken-ta-∪Δ {Δ' = Δ'} {e = fst e} frsh (TFst wt) = 
      TFst (weaken-ta-∪Δ frsh' wt)
      where
        frsh' : ∀{z} →
                dom Δ' z →
                hole-fresh z e
        frsh' z∈Δ' with frsh z∈Δ'
        ... | HFFst hf = hf
    weaken-ta-∪Δ {Δ' = Δ'} {e = snd e} frsh (TSnd wt) =
      TSnd (weaken-ta-∪Δ frsh' wt)
      where
        frsh' : ∀{z} →
                dom Δ' z →
                hole-fresh z e
        frsh' z∈Δ' with frsh z∈Δ'
        ... | HFSnd hf = hf
    weaken-ta-∪Δ {Δ' = Δ'} {Δ = Δ} frsh (TEHole {u = u} {τ = τ} u∈Δ st)
      with Δ' u in Δ'u
    ... | Some τ'
      with frsh (τ' , Δ'u)
    ... | HFEHole u≠u hfσ = abort (u≠u refl)
    weaken-ta-∪Δ {Δ' = Δ'} {Δ = Δ} {e = ⦇-⦈⟨ u , σ ⟩}
                 frsh (TEHole {u = u} {Γ' = Γ'} {τ = τ} u∈Δ st)
        | None =
      TEHole (dom-r-union Δ' Δ u (Γ' , τ) u∈Δ Δ'u)
              (weaken-σ-∪Δ frshσ st)
      where
        frshσ : ∀{z} →
                dom Δ' z →
                hole-fresh-σ z σ
        frshσ z∈Δ' with frsh z∈Δ'
        ... | HFEHole z≠u hfσ = hfσ
    weaken-ta-∪Δ {Δ' = Δ'} {Δ = Δ} frsh (THole {u = u} {τ = τ} u∈Δ st wt)
      with Δ' u in Δ'u
    ... | Some τ'
      with frsh (τ' , Δ'u)
    ... | HFHole u≠u hfσ hf = abort (u≠u refl)
    weaken-ta-∪Δ {Δ' = Δ'} {Δ = Δ} {e = ⦇⌜ e ⌟⦈⟨ u , σ ⟩}
                 frsh (THole {Γ' = Γ'} {τ = τ} u∈Δ st wt)
        | None =
      THole (dom-r-union Δ' Δ u (Γ' , τ) u∈Δ Δ'u)
               (weaken-σ-∪Δ frshσ st)
               (weaken-ta-∪Δ frsh' wt)
      where
        frshσ : ∀{z} →
                dom Δ' z →
                hole-fresh-σ z σ
        frshσ z∈Δ' with frsh z∈Δ'
        ... | HFHole z≠u hfσ hf = hfσ
        frsh' : ∀{z} →
                dom Δ' z →
                hole-fresh z e
        frsh' z∈Δ' with frsh z∈Δ'
        ... | HFHole z≠u hfσ hf = hf

    weaken-σ-∪Δ : ∀{Γ Δ' Δ Δp σ Γσ} →
                  (∀{x} →
                   dom Δ' x →
                   hole-fresh-σ x σ) →
                  Γ , Δ , Δp ⊢ σ :se: Γσ →
                  Γ , (Δ' ∪ Δ) , Δp ⊢ σ :se: Γσ
    weaken-σ-∪Δ frsh (STId Γσ⊆Γ) = STId Γσ⊆Γ
    weaken-σ-∪Δ {Δ' = Δ'} {σ = Subst d y σ}
                frsh (STSubst st wt) =
      STSubst (weaken-σ-∪Δ frshσ st)
               (weaken-ta-∪Δ frsh' wt)
      where
        frshσ : ∀{z} →
                dom Δ' z →
                hole-fresh-σ z σ
        frshσ z∈Δ' with frsh z∈Δ'
        ... | HFσSubst hf hfσ = hfσ
        frsh' : ∀{z} →
                dom Δ' z →
                hole-fresh z d
        frsh' z∈Δ' with frsh z∈Δ'
        ... | HFσSubst hf hfσ = hf
    weaken-rules-∪Δ : ∀{Γ Δ' Δ Δp rs τ1 ξ τ2} →
                      (∀{u} →
                       dom Δ' u →
                       hole-fresh-rs u rs) →
                      Γ , Δ , Δp ⊢ rs ::s τ1 [ ξ ]=> τ2 →
                      Γ , (Δ' ∪ Δ) , Δp ⊢ rs ::s τ1 [ ξ ]=> τ2
    weaken-rules-∪Δ {Δ' = Δ'} frsh (RTOneRule {r = p => e} rt) =
      RTOneRule (weaken-rule-∪Δ frsh' rt)
      where
        frsh' : ∀{z} →
                dom Δ' z →
                hole-fresh-r z (p => e)
        frsh' z∈Δ' with frsh z∈Δ'
        ... | HFRules hfr hfrs = hfr
    weaken-rules-∪Δ {Δ' = Δ'} frsh (RTRules {r = r} {rs = rs} rt rst) =
      RTRules (weaken-rule-∪Δ frshr rt)
              (weaken-rules-∪Δ frshrs rst)
      where
        frshr : ∀{z} →
                dom Δ' z →
                hole-fresh-r z r
        frshr z∈Δ' with frsh z∈Δ'
        ... | HFRules f frs = f
        frshrs : ∀{z} →
                 dom Δ' z →
                 hole-fresh-rs z rs
        frshrs z∈Δ' with frsh z∈Δ'
        ... | HFRules hf hfrs = hfrs
        
    weaken-rule-∪Δ : ∀{Γ Δ' Δ Δp r τ1 ξ τ2} →
                     (∀{u} →
                      dom Δ' u →
                      hole-fresh-r u r) →
                     Γ , Δ , Δp ⊢ r :: τ1 [ ξ ]=> τ2 →
                     Γ , (Δ' ∪ Δ) , Δp ⊢ r :: τ1 [ ξ ]=> τ2
    weaken-rule-∪Δ {Γ = Γ} {Δ' = Δ'} {Δ = Δ} {Δp = Δp}
                   {τ1 = τ1} {ξ = ξ} {τ2 = τ2} frsh
                   (RTRule {p = p} {e = e}
                           {Γp = Γp} 
                           pt Γ##Γp wt) =
      RTRule pt Γ##Γp (weaken-ta-∪Δ frsh' wt)
      -- tr (λ qq → Γ , qq , Δp ⊢ p => e :: τ1 [ ξ ]=> τ2)
      --    (∪-assoc Δ' Δe Δp)
      --    (RTRule pt Γ##Γp
      --            (disjoint-parts Δ'##Δp Δe##Δp)
      --            (weaken-ta-∪Δ frsh' wt))
      where
        frsh' : ∀{z} →
                dom Δ' z →
                hole-fresh z e
        frsh' z∈Δ' with frsh z∈Δ'
        ... | HFRule hub hf = hf

    -- Commutativity of union requires disjointness, so we
    -- make use of the identity
    -- Δ ∪ Δ' = Δ ⊔ (Δ' \ Δ) = (Δ' \ Δ) ⊔ Δ
    weaken-ta-Δ∪ : ∀{Γ Δ Δ' Δp e τ} →
                   (∀{u} →
                    dom Δ' u →
                    hole-fresh u e) →
                   Γ , Δ , Δp ⊢ e :: τ →
                   Γ , (Δ ∪ Δ') , Δp ⊢ e :: τ
    weaken-ta-Δ∪ {Γ = Γ} {Δ = Δ} {Δ' = Δ'} {Δp = Δp}
                 {e = e} {τ = τ} frsh wt =
      tr (λ qq → Γ , qq , Δp ⊢ e :: τ)
         (! (union-with-diff Δ Δ' ·
             ∪-comm Δ (Δ' ∖ Δ) (r-disjoint-diff-r Δ' Δ)))
         (weaken-ta-∪Δ frsh' wt)
      where
        frsh' : ∀{z} →
                dom (Δ' ∖ Δ) z →
                hole-fresh z e
        frsh' {z = z} (τ , z∈Δ'∖Δ) =
          frsh (τ , dom-diff-dom-l {Γ1 = Δ'} {Γ2 = Δ} z∈Δ'∖Δ)
         
    -- convenience function
    weaken-ta-Δ : ∀{Γ Δ Δp u τ' e τ} →
                  hole-fresh u e →
                  Γ , Δ , Δp ⊢ e :: τ →
                  Γ , (Δ ,, (u , τ')) , Δp ⊢ e :: τ
    weaken-ta-Δ {u = u} {τ' = τ'} {e = e} frsh wt =
      weaken-ta-∪Δ frsh' wt
      where
        frsh' : ∀{z} →
                dom (■ (u , τ')) z →
                hole-fresh z e
        frsh' d with dom-singleton-eq d
        ... | refl = frsh
