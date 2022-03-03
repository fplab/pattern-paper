open import List
open import Nat
open import Prelude
open import contexts
open import core
open import freshness
open import freshness-decidable
open import patterns-core
open import result-judgements
open import statics-core

module dynamics-core where
  -- e' is one of the possible values of e
  data _∈[_,_]values_ : (e' : ihexp) →
                        (Δ : hctx) → (Δp : phctx) →
                        (e : ihexp) → Set where
    IVVal   : ∀{Δ Δp e τ} →
              e val →
              ∅ , Δ , Δp ⊢ e :: τ →
              e ∈[ Δ , Δp ]values e
    IVIndet : ∀{Δ Δp e e' τ} →
              e notintro →
              ∅ , Δ , Δp ⊢ e :: τ →
              e' val →
              ∅ , Δ , Δp ⊢ e' :: τ →
              e' ∈[ Δ , Δp ]values e
    IVInl   : ∀{Δ Δp e1 e1' τ2 τ} →
              (inl τ2 e1) indet →
              ∅ , Δ , Δp ⊢ inl τ2 e1 :: τ →
              e1' ∈[ Δ , Δp ]values e1 →
              (inl τ2 e1') ∈[ Δ , Δp ]values (inl τ2 e1)
    IVInr   : ∀{Δ Δp e2 e2' τ1 τ} →
              (inr τ1 e2) indet →
              ∅ , Δ , Δp ⊢ inr τ1 e2 :: τ →
              e2' ∈[ Δ , Δp ]values e2 →
              (inr τ1 e2') ∈[ Δ , Δp ]values (inr τ1 e2)
    IVPair  : ∀{Δ Δp e1 e1' e2 e2' τ} →
              ⟨ e1 , e2 ⟩ indet →
              ∅ , Δ , Δp ⊢ ⟨ e1 , e2 ⟩ :: τ →
              e1' ∈[ Δ , Δp ]values e1 →
              e2' ∈[ Δ , Δp ]values e2 →
              ⟨ e1' , e2' ⟩ ∈[ Δ , Δp ]values ⟨ e1 , e2 ⟩

  -- substitution
  mutual
    [_/_]r : ihexp → Nat → rule → rule
    [ d / y ]r (p => e) with unbound-in-p-dec y p
    ... | Inl _ = p => ([ d / y ] e)
    ... | Inr _ = p => e

    [_/_]rs : ihexp → Nat → rules → rules
    [ d / y ]rs nil = nil
    [ d / y ]rs (r / rs) =
      ([ d / y ]r r) / ([ d / y ]rs rs)

    [_/_]zrs : ihexp → Nat → zrules → zrules
    [ d / y ]zrs (rs-pre / r / rs-post) =
      ([ d / y ]rs rs-pre) / ([ d / y ]r r) / ([ d / y ]rs rs-post)
      
    [_/_]_ : ihexp → Nat → ihexp → ihexp
    [ d / y ] unit = unit
    [ d / y ] (N n) = N n
    [ d / y ] X x
      with nat-dec x y
    [ d / y ] X .y | Inl refl = d
    [ d / y ] X x  | Inr x≠y = X x
    [ d / y ] (·λ x ·[ τ ] d')
      with nat-dec x y
    [ d / y ] (·λ .y ·[ τ ] d') | Inl refl = ·λ y ·[ τ ] d'
    [ d / y ] (·λ x ·[ τ ] d')  | Inr x≠y =
      ·λ x ·[ τ ] ( [ d / y ] d')
    [ d / y ] (d1 ∘ d2) = ([ d / y ] d1) ∘ ([ d / y ] d2)
    [ d / y ] (inl τ d') = inl τ ([ d / y ] d')
    [ d / y ] (inr τ d') = inr τ ([ d / y ] d')
    [ d / y ] match d' ·: τ of rs =
      match ([ d / y ] d') ·: τ of ([ d / y ]zrs rs) 
    [ d / y ] ⟨ d1 , d2 ⟩ = ⟨ [ d / y ] d1 , [ d / y ] d2 ⟩
    [ d / y ] (fst d') = fst ([ d / y ] d')
    [ d / y ] (snd d') = snd ([ d / y ] d')
    [ d / y ] ⦇-⦈⟨ u , σ ⟩ = ⦇-⦈⟨ u , Subst d y σ ⟩
    [ d / y ] ⦇⌜ d' ⌟⦈⟨ u , σ ⟩ =
      ⦇⌜ [ d / y ] d' ⌟⦈⟨ u , Subst d y σ ⟩

  -- apply a list of substitutions one by one
  --
  -- in contrast to the paper, rather than actually
  -- applying each substitution immediately, we wrap
  -- the given expression with appropriate lambdas
  -- and applications. semantically, this is the same,
  -- but it breaks the evaluation into multiple steps.
  --
  -- to see why this is necessary, consider the
  -- MNotIntroPair rule. if we match an expression e
  -- which is notintro against the pattern ⟨ x , y ⟩,
  -- then we emit the substitutions
  -- [ fst e / x ] [ snd e / y ]. if we tried to apply
  -- both of these substitutions immediately, then
  -- the binders of e will appear multiple times in the
  -- resulting term, breaking the binders uniqueness
  -- assumptions required by many of our results à la
  -- Barendregt's convention. however, preservation
  -- (the only theorem where this is relevant) only
  -- requires us to reason about a single evaluation step.
  -- thus, by separating the substitutions into multiple
  -- evaluation steps, we can effectively assume that
  -- we rename all the binders before the actual
  -- substitution is applied.
  --
  -- note that we only have half-annotated lambdas, so
  -- in order to perform this expansion, the emitted
  -- substitution lists must also record typing information.
  -- however, our matching judgements don't actually have
  -- any typing information, so we make this possible by
  -- including a type ascription on match scrutinees
  apply-substs : subst-list → ihexp → ihexp
  apply-substs [] e = e
  apply-substs ((d , τ , y) :: θ) e =
    (·λ y ·[ τ ] (apply-substs θ e)) ∘ d
  
  -- e takes a step to e'
  data _↦_ : (e : ihexp) → (e' : ihexp) → Set where
    ITpFun   : ∀{e1 e1' e2} →
                e1 ↦ e1' →
                (e1 ∘ e2) ↦ (e1' ∘ e2)
    ITpArg   : ∀{e1 e2 e2'} →
                e1 final →
                e2 ↦ e2' →
                (e1 ∘ e2) ↦ (e1 ∘ e2')
    ITp      : ∀{x τ e1 e2} →
                e2 final →
                ((·λ x ·[ τ ] e1) ∘ e2) ↦ ([ e2 / x ] e1)
    ITPairL   : ∀{e1 e1' e2} →
                e1 ↦ e1' →
                ⟨ e1 , e2 ⟩ ↦ ⟨ e1' , e2 ⟩
    ITPairR   : ∀{e1 e2 e2'} →
                e1 final →
                e2 ↦ e2' →
                ⟨ e1 , e2 ⟩ ↦ ⟨ e1 , e2' ⟩
    ITFst     : ∀{e e'} →
                e ↦ e' →
                (fst e) ↦ (fst e')
    ITFstPair : ∀{e1 e2} →
                ⟨ e1 , e2 ⟩ final →
                fst ⟨ e1 , e2 ⟩ ↦ e1
    ITSnd     : ∀{e e'} →
                e ↦ e' →
                (snd e) ↦ (snd e')
    ITSndPair : ∀{e1 e2} →
                ⟨ e1 , e2 ⟩ final →
                snd ⟨ e1 , e2 ⟩ ↦ e2
    ITInl     : ∀{e e' τ} →
                e ↦ e' →
                inl τ e ↦ inl τ e'
    ITInr     : ∀{e e' τ} →
                e ↦ e' →
                inr τ e ↦ inr τ e'
    ITExpMatch  : ∀{e e' τ rs} →
                  e ↦ e' →
                  match e ·: τ of rs ↦ match e' ·: τ of rs
    ITSuccMatch : ∀{e τ θ rs-pre pr er rs-post} →
                  e final →
                  e ·: τ ▹ pr ⊣ θ →
                  match e ·: τ of (rs-pre / (pr => er) / rs-post) ↦
                    apply-substs θ er
    ITFailMatch : ∀{e τ rs pr er rss r' rs'} →
                  e final →
                  e ⊥▹ pr →
                  erase-r (rs / (pr => er) / nil) rss →
                  match e ·: τ of (rs / (pr => er) / (r' / rs')) ↦
                    match e ·: τ of (rss / r' / rs')
    ITHole : ∀{e e' u σ} →
               e ↦ e' →
               ⦇⌜ e ⌟⦈⟨ u , σ ⟩ ↦ ⦇⌜ e' ⌟⦈⟨ u , σ ⟩
