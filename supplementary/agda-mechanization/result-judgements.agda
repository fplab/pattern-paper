open import List
open import Prelude
open import core
open import patterns-core
open import value-judgements

module result-judgements where
  open value-judgements public
  mutual
    -- e is indeterminate
    data _indet : (e : ihexp) → Set where
      IAp     : ∀{e1 e2} →
                e1 indet →
                e2 final →
                (e1 ∘ e2) indet
      IInl    : ∀{e τ} →
                e indet →
                (inl τ e) indet
      IInr    : ∀{e τ} →
                e indet →
                (inr τ e) indet
      IMatch  : ∀{e τ rs-pre pr er rs-post} →
                e final →
                e ·: τ ?▹ pr →
                (match e ·: τ of (rs-pre / (pr => er) / rs-post)) indet
      IPairL  : ∀{e1 e2} →
                e1 indet →
                e2 val →
                ⟨ e1 , e2 ⟩ indet
      IPairR  : ∀{e1 e2} →
                e1 val →
                e2 indet →
                ⟨ e1 , e2 ⟩ indet
      IPair   : ∀{e1 e2} →
                e1 indet →
                e2 indet →
                ⟨ e1 , e2 ⟩ indet
      IFst    : ∀{e} →
                ((e1 e2 : ihexp) →
                 e ≠ ⟨ e1 , e2 ⟩) →
                e indet →
                (fst e) indet
      ISnd    : ∀{e} →
                ((e1 e2 : ihexp) →
                 e ≠ ⟨ e1 , e2 ⟩) →
                e indet →
                (snd e) indet
      IEHole  : ∀{u σ} →
                ⦇-⦈⟨ u , σ ⟩ indet
      IHole : ∀{e u σ} →
                e final →
                ⦇⌜ e ⌟⦈⟨ u , σ ⟩ indet
                
    -- e is final
    data _final : (e : ihexp) → Set where
      FVal   : ∀{e} →
               e val →
               e final
      FIndet : ∀{e} →
               e indet →
               e final

    -- all substitutions in θ are final
    data _final-θ : subst-list → Set where
      FθEmpty  : [] final-θ
      FθExtend : ∀{d y θ} →
                 θ final-θ →
                 d final →
                 ((d , y) :: θ) final-θ

    inl-final : ∀{e τ} → (inl τ e) final → e final
    inl-final (FVal (VInl eval)) = FVal eval
    inl-final (FIndet (IInl eind)) = FIndet eind

    final-inl : ∀{e τ} → e final → (inl τ e) final
    final-inl (FVal eval) = FVal (VInl eval)
    final-inl (FIndet ind) = FIndet (IInl ind)
    
    inr-final : ∀{e τ} → (inr τ e) final → e final
    inr-final (FVal (VInr eval)) = FVal eval
    inr-final (FIndet (IInr eind)) = FIndet eind

    final-inr : ∀{e τ} → e final → (inr τ e) final
    final-inr (FVal eval) = FVal (VInr eval)
    final-inr (FIndet ind) = FIndet (IInr ind)
    
    pair-final : ∀{e1 e2} →
                 ⟨ e1 , e2 ⟩ final →
                 e1 final × e2 final
    pair-final (FVal (VPair val1 val2)) = FVal val1 , FVal val2
    pair-final (FIndet (IPairL ind1 val2)) =
      FIndet ind1 , FVal val2
    pair-final (FIndet (IPairR val1 ind2)) =
      FVal val1 , FIndet ind2
    pair-final (FIndet (IPair ind1 ind2)) =
      FIndet ind1 , FIndet ind2

    final-pair : ∀{e1 e2} →
                 e1 final →
                 e2 final →
                 ⟨ e1 , e2 ⟩ final
    final-pair (FVal val1) (FVal val2) =
      FVal (VPair val1 val2)
    final-pair (FVal val1) (FIndet ind2) =
      FIndet (IPairR val1 ind2)
    final-pair (FIndet ind1) (FVal val2) =
      FIndet (IPairL ind1 val2)
    final-pair (FIndet ind1) (FIndet ind2) =
      FIndet (IPair ind1 ind2)
    
    final-notintro-indet : ∀{e} →
                           e final →
                           e notintro →
                           e indet
    final-notintro-indet (FVal ()) NVAp
    final-notintro-indet (FVal ()) NVMatch
    final-notintro-indet (FVal ()) NVFst
    final-notintro-indet (FVal ()) NVSnd
    final-notintro-indet (FVal ()) NVEHole
    final-notintro-indet (FVal ()) NVHole
    final-notintro-indet (FIndet ind) ni = ind

    val-indet-not : ∀{e} →
                    e val →
                    e indet →
                    ⊥
    val-indet-not VNum ()
    val-indet-not VLam ()
    val-indet-not (VInl eval) (IInl ind) =
      val-indet-not eval ind
    val-indet-not (VInr eval) (IInr ind) =
      val-indet-not eval ind
    val-indet-not (VPair eval1 eval2) (IPairL ind1 val2) =
      val-indet-not eval1 ind1
    val-indet-not (VPair eval1 eval2) (IPairR val1 ind2) =
      val-indet-not eval2 ind2
    val-indet-not (VPair eval1 eval2) (IPair ind1 ind2) =
      val-indet-not eval1 ind1

                        
