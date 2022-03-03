open import List
open import Nat
open import Prelude
open import constraints-core
open import core

module complete-constraints-core where
   -- complete match constraints
  data comp-constr : Set where
    ·⊤    : comp-constr
    ·⊥    : comp-constr
    N     : Nat → comp-constr
    N̸     : Nat → comp-constr
    inl   : comp-constr → comp-constr
    inr   : comp-constr → comp-constr
    ⟨_,_⟩ : comp-constr → comp-constr → comp-constr
    _∨_   : comp-constr → comp-constr → comp-constr
    _∧_   : comp-constr → comp-constr → comp-constr

  -- ξ constrains final expressions of type τ
  data _:cc:_ : (ξ : comp-constr) → (τ : htyp) → Set where
    CTTruth   : ∀{τ} →
                ·⊤ :cc: τ
    CTFalsity : ∀{τ} →
                ·⊥ :cc: τ
    CTNum     : ∀{n} →
                N n :cc: num
    CTNotNum  : ∀{n} →
                N̸ n :cc: num
    CTInl     : ∀{ξ τ1 τ2} →
                ξ :cc: τ1 →
                inl ξ :cc: τ1 ⊕ τ2
    CTInr     : ∀{ξ τ1 τ2} →
                ξ :cc: τ2 →
                inr ξ :cc: τ1 ⊕ τ2
    CTPair    : ∀{ξ1 ξ2 τ1 τ2} →
                ξ1 :cc: τ1 →
                ξ2 :cc: τ2 →
                ⟨ ξ1 , ξ2 ⟩ :cc: τ1 ⊠ τ2
    CTOr      : ∀{ξ1 ξ2 τ} →
                ξ1 :cc: τ →
                ξ2 :cc: τ →
                (ξ1 ∨ ξ2) :cc: τ
    CTnd     : ∀{ξ1 ξ2 τ} →
                ξ1 :cc: τ →
                ξ2 :cc: τ →
                (ξ1 ∧ ξ2) :cc: τ
    
  -- e satisfies ξ
  data _⊧_ : (e : ihexp) → (ξ : comp-constr) → Set where
    CSTruth  : ∀{e} →
               e ⊧ ·⊤
    CSNum    : ∀{n} →
               (N n) ⊧ (N n)
    CSNotNum : ∀{n1 n2} →
               n1 ≠ n2 →
               (N n1) ⊧ (N̸ n2)
    CSInl    : ∀{e τ ξ} →
               e ⊧ ξ →
               (inl τ e) ⊧ (inl ξ)
    CSInr    : ∀{e τ ξ} →
               e ⊧ ξ →
               (inr τ e) ⊧ (inr ξ)
    CSPair   : ∀{e1 e2 ξ1 ξ2} →
               e1 ⊧ ξ1 →
               e2 ⊧ ξ2 →
               ⟨ e1 , e2 ⟩ ⊧ ⟨ ξ1 , ξ2 ⟩
    CSOrL    : ∀{e ξ1 ξ2} →
               e ⊧ ξ1 →
               e ⊧ (ξ1 ∨ ξ2)
    CSOrR    : ∀{e ξ1 ξ2} →
               e ⊧ ξ2 →
               e ⊧ (ξ1 ∨ ξ2)
    CSAnd    : ∀{e ξ1 ξ2} →
               e ⊧ ξ1 →
               e ⊧ ξ2 →
               e ⊧ (ξ1 ∧ ξ2)

  -- compute the dual of a constraint
  _◆d : comp-constr → comp-constr
  ·⊤ ◆d = ·⊥
  ·⊥ ◆d = ·⊤
  (N n) ◆d = N̸ n
  (N̸ n) ◆d = N n
  (inl ξ) ◆d = inl (ξ ◆d) ∨ inr ·⊤
  (inr ξ) ◆d = inr (ξ ◆d) ∨ inl ·⊤
  ⟨ ξ1 , ξ2 ⟩ ◆d =
    (⟨ ξ1 , ξ2 ◆d ⟩ ∨ ⟨ ξ1 ◆d , ξ2 ⟩) ∨ ⟨ ξ1 ◆d , ξ2 ◆d ⟩
  (ξ1 ∨ ξ2) ◆d = (ξ1 ◆d) ∧ (ξ2 ◆d)
  (ξ1 ∧ ξ2) ◆d = (ξ1 ◆d) ∨ (ξ2 ◆d)
  
  -- substitute ⊤ for ? in ξ
  _◆⊤ : constr → comp-constr
  ·⊤ ◆⊤ = ·⊤
  ·⊥ ◆⊤ = ·⊥
  ·? ◆⊤ = ·⊤
  (N n) ◆⊤ = N n
  (inl ξ) ◆⊤ = inl (ξ ◆⊤)
  (inr ξ) ◆⊤ = inr (ξ ◆⊤)
  ⟨ ξ1 , ξ2 ⟩ ◆⊤ = ⟨ ξ1 ◆⊤ , ξ2 ◆⊤ ⟩
  (ξ1 ∨ ξ2) ◆⊤ = (ξ1 ◆⊤) ∨ (ξ2 ◆⊤)

  -- substitute ⊥ for ? in ξ
  _◆⊥ : constr → comp-constr
  ·⊤ ◆⊥ = ·⊤
  ·⊥ ◆⊥ = ·⊥
  ·? ◆⊥ = ·⊥
  (N n) ◆⊥ = N n
  (inl ξ) ◆⊥ = inl (ξ ◆⊥)
  (inr ξ) ◆⊥ = inr (ξ ◆⊥)
  ⟨ ξ1 , ξ2 ⟩ ◆⊥ = ⟨ ξ1 ◆⊥ , ξ2 ◆⊥ ⟩
  (ξ1 ∨ ξ2) ◆⊥ = (ξ1 ◆⊥) ∨ (ξ2 ◆⊥)

  dual-same-type : ∀{ξ τ} →
                   ξ :cc: τ →
                   (ξ ◆d) :cc: τ
  dual-same-type CTTruth = CTFalsity
  dual-same-type CTFalsity = CTTruth
  dual-same-type CTNum = CTNotNum
  dual-same-type CTNotNum = CTNum
  dual-same-type (CTInl ct) =
    CTOr (CTInl (dual-same-type ct)) (CTInr CTTruth)
  dual-same-type (CTInr ct) =
    CTOr (CTInr (dual-same-type ct)) (CTInl CTTruth)
  dual-same-type (CTPair ct1 ct2) =
    CTOr (CTOr (CTPair ct1 (dual-same-type ct2))
               (CTPair (dual-same-type ct1) ct2))
               (CTPair (dual-same-type ct1) (dual-same-type ct2))
  dual-same-type (CTOr ct1 ct2) =
    CTnd (dual-same-type ct1) (dual-same-type ct2)
  dual-same-type (CTnd ct1 ct2) =
    CTOr (dual-same-type ct1) (dual-same-type ct2)
  
  same-type-dual : ∀{ξ τ} →
                   (ξ ◆d) :cc: τ →
                   ξ :cc: τ
  same-type-dual {ξ = ·⊤} CTFalsity = CTTruth
  same-type-dual {ξ = ·⊥} CTTruth = CTFalsity
  same-type-dual {ξ = N n} CTNotNum = CTNum
  same-type-dual {ξ = N̸ n} CTNum = CTNotNum
  same-type-dual {ξ = inl ξ} {τ = τ1 ⊕ τ2} (CTOr (CTInl dct1) dct2) =
    CTInl (same-type-dual dct1)
  same-type-dual {ξ = inr ξ} {τ = τ1 ⊕ τ2} (CTOr (CTInr dct1) dct2) =
    CTInr (same-type-dual dct1)
  same-type-dual {ξ = ⟨ ξ1 , ξ2 ⟩} {τ = τ1 ⊠ τ2}
                 (CTOr (CTOr (CTPair dct1 dct2) (CTPair dct3 dct4)) dct5) =
    CTPair dct1 dct4
  same-type-dual {ξ = ξ1 ∨ ξ2} (CTnd dct1 dct2) =
    CTOr (same-type-dual dct1) (same-type-dual dct2)
  same-type-dual {ξ = ξ1 ∧ ξ2} (CTOr dct1 dct2) =
    CTnd (same-type-dual dct1) (same-type-dual dct2)
