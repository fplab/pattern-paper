open import List
open import Nat
open import Prelude
open import contexts
open import constraints-core
open import core
open import value-judgements

module patterns-core where
  -- pointer erasure for pattern rules
  _◆er : zrules → rules
  (nil / r / rs) ◆er = r / rs
  ((r' / rs') / r / rs) ◆er = r' / ((rs' / r / rs) ◆er)

  -- a judgemental version of the above which
  -- is often easier to work with
  data erase-r : zrules → rules → Set where
    ERZPre  : ∀{r rs} →
              erase-r (nil / r / rs) (r / rs)
    ERNZPre : ∀{r' rs' r rs er} →
              erase-r (rs' / r / rs) er →
              erase-r ((r' / rs') / r / rs) (r' / er)
  
  -- a pattern p is refutable
  data _refutable : (p : pattrn) → Set where
    RNum    : ∀{n} →
              (N n) refutable
    RInl    : ∀{p} →
              (inl p) refutable
    RInr    : ∀{p} →
              (inr p) refutable
    RPairL  : ∀{p1 p2} →
              p1 refutable →
              ⟨ p1 , p2 ⟩ refutable
    RPairR  : ∀{p1 p2} →
              p2 refutable →
              ⟨ p1 , p2 ⟩ refutable
    REHole  : ∀{w} →
              ⦇-⦈[ w ] refutable
    RHole : ∀{p w τ} →
              ⦇⌜ p ⌟⦈[ w , τ ] refutable

  -- lists of substitutions as emitted by pattern matches
  --
  -- note that, in contrast to the paper, we include
  -- the type of substituted expressions in the emitted
  -- substitution. see the comment on the apply-substs
  -- function in dynamics-core.agda for why this is necessary
  subst-list : Set
  subst-list = List (ihexp × htyp × Nat)

  -- e matches the pattern p, emitting the substitutions θ
  --
  -- again, we include type ascriptions here
  -- in order to record typing information in the emitted
  -- substitution list.
  data _·:_▹_⊣_ : (e : ihexp) → (τ : htyp) →
                  (p : pattrn) → (θ : subst-list) → Set where
    MUnit : ∀{e} →
            e ·: unit ▹ unit ⊣ []
    MNum  : ∀{n} →
            (N n) ·: num ▹ (N n) ⊣ []
    MVar  : ∀{e τ x} →
            e ·: τ ▹ (X x) ⊣ ((e , τ , x) :: [])
    MInl  : ∀{e τ1 τ2 p θ} →
            e ·: τ1 ▹ p ⊣ θ →
            inl τ2 e ·: τ1 ⊕ τ2 ▹ inl p ⊣ θ
    MInr  : ∀{e τ1 τ2 p θ} →
            e ·: τ2 ▹ p ⊣ θ →
            inr τ1 e ·: τ1 ⊕ τ2 ▹ inr p ⊣ θ
    MPair : ∀{e1 e2 τ1 τ2 p1 p2 θ1 θ2} →
            e1 ·: τ1 ▹ p1 ⊣ θ1 →
            e2 ·: τ2 ▹ p2 ⊣ θ2 →
            ⟨ e1 , e2 ⟩ ·: τ1 ⊠ τ2 ▹ ⟨ p1 , p2 ⟩ ⊣ (θ1 ++ θ2)
    MNotIntroPair : ∀{e τ1 τ2 p1 p2 θ1 θ2} →
                    e notintro →
                    fst e ·: τ1 ▹ p1 ⊣ θ1 →
                    snd e ·: τ2 ▹ p2 ⊣ θ2 →
                    e ·: τ1 ⊠ τ2 ▹ ⟨ p1 , p2 ⟩ ⊣ (θ1 ++ θ2)
    MWild : ∀{e τ} →
            e ·: τ ▹ wild ⊣ []

  -- e may match p
  --
  -- the type ascription here is really only required
  -- to pass it down to the e ·: τ ▹ p judgement above
  data _·:_?▹_ : (e : ihexp) → (τ : htyp) →
                 (p : pattrn) → Set where
    MMNotIntro : ∀{e τ p} →
                 e notintro →
                 p refutable →
                 e ·: τ ?▹ p
    MMInl      : ∀{e τ1 τ2 p} →
                 e ·: τ1 ?▹ p →
                 inl τ2 e ·: (τ1 ⊕ τ2) ?▹ inl p
    MMInr      : ∀{e τ1 τ2 p} →
                 e ·: τ2 ?▹ p →
                 inr τ1 e ·: τ1 ⊕ τ2 ?▹ inr p
    MMPairL    : ∀{e1 e2 τ1 τ2 p1 p2 θ} →
                 e1 ·: τ1 ?▹ p1 →
                 e2 ·: τ2 ▹ p2 ⊣ θ →
                 ⟨ e1 , e2 ⟩ ·: τ1 ⊠ τ2 ?▹ ⟨ p1 , p2 ⟩
    MMPairR    : ∀{e1 e2 τ1 τ2 p1 p2 θ} →
                 e1 ·: τ1 ▹ p1 ⊣ θ →
                 e2 ·: τ2 ?▹ p2 →
                 ⟨ e1 , e2 ⟩ ·: τ1 ⊠ τ2 ?▹ ⟨ p1 , p2 ⟩
    MMPair     : ∀{e1 e2 τ1 τ2 p1 p2} →
                 e1 ·: τ1 ?▹ p1 →
                 e2 ·: τ2 ?▹ p2 →
                 ⟨ e1 , e2 ⟩ ·: τ1 ⊠ τ2 ?▹ ⟨ p1 , p2 ⟩
    MMEHole    : ∀{e τ w} →
                 e ·: τ ?▹ ⦇-⦈[ w ]
    MMHole   : ∀{e τ p w τ'} →
                 e ·: τ ?▹ ⦇⌜ p ⌟⦈[ w , τ' ]
    
  -- e does not match p
  data _⊥▹_ : (e : ihexp) → (p : pattrn) → Set where
    NMNum   : ∀{n1 n2} →
              n1 ≠ n2 →
              (N n1) ⊥▹ (N n2)
    NMConfL : ∀{e τ p} →
              inr τ e ⊥▹ inl p
    NMConfR : ∀{e τ p} →
              inl τ e ⊥▹ inr p
    NMInl   : ∀{e τ p} →
              e ⊥▹ p →
              inl τ e ⊥▹ inl p
    NMInr   : ∀{e τ p} →
              e ⊥▹ p →
              inr τ e ⊥▹ inr p
    NMPairL : ∀{e1 e2 p1 p2} →
              e1 ⊥▹ p1 →
              ⟨ e1 , e2 ⟩ ⊥▹ ⟨ p1 , p2 ⟩
    NMPairR : ∀{e1 e2 p1 p2} →
              e2 ⊥▹ p2 →
              ⟨ e1 , e2 ⟩ ⊥▹ ⟨ p1 , p2 ⟩
    

  -- in the pattern hole context Δp, p is assigned type τ and
  -- emits constraint ξ, where Γ records assumptions about the
  -- type of free variables
  data _⊢_::_[_]⊣_ : (Δp : phctx) → (p : pattrn) → (τ : htyp) →
                     (ξ : constr) → (Γ : tctx) → Set where
    PTUnit   : ∀{Δp} →
               Δp ⊢ unit :: unit [ ·⊤ ]⊣ ∅
    PTNum    : ∀{Δp n} →
               Δp ⊢ N n :: num [ N n ]⊣ ∅
    PTVar    : ∀{Δp x τ} →
               Δp ⊢ X x :: τ [ ·⊤ ]⊣ (■ (x , τ))
    PTInl    : ∀{Δp p τ1 τ2 ξ Γ} →
               Δp ⊢ p :: τ1 [ ξ ]⊣ Γ →
               Δp ⊢ inl p :: (τ1 ⊕ τ2) [ inl ξ ]⊣ Γ
    PTInr    : ∀{Δp p τ1 τ2 ξ Γ} →
               Δp ⊢ p :: τ2 [ ξ ]⊣ Γ →
               Δp ⊢ inr p :: (τ1 ⊕ τ2) [ inr ξ ]⊣ Γ
    PTPair   : ∀{Δp p1 p2 τ1 τ2 ξ1 ξ2 Γ1 Γ2} →
               Γ1 ## Γ2 →
               Δp ⊢ p1 :: τ1 [ ξ1 ]⊣ Γ1 →
               Δp ⊢ p2 :: τ2 [ ξ2 ]⊣ Γ2  →
               Δp ⊢ ⟨ p1 , p2 ⟩ :: (τ1 ⊠ τ2) [ ⟨ ξ1 , ξ2 ⟩ ]⊣ (Γ1 ∪ Γ2)
    PTEHole  : ∀{Δp w τ} →
               (w , τ) ∈ Δp →
               Δp ⊢ ⦇-⦈[ w ] :: τ [ ·? ]⊣ ∅
    PTHole : ∀{Δp p w τ τ' ξ Γ} →
               (w , τ') ∈ Δp →
               Δp ⊢ p :: τ [ ξ ]⊣ Γ →
               Δp ⊢ ⦇⌜ p ⌟⦈[ w , τ ] :: τ' [ ·? ]⊣ Γ
    PTWild   : ∀{Δp τ} →
               Δp ⊢ wild :: τ [ ·⊤ ]⊣ ∅
    
