open import Bool
open import Nat
open import Prelude
open import complete-constraints-core
open import core

module complete-satisfy-decidable where
  comp-satisfy-bool : ihexp → comp-constr → Bool
  comp-satisfy-bool e ·⊤ = true
  comp-satisfy-bool e ·⊥ = false
  comp-satisfy-bool (N n1) (N n2) with nat-dec n1 n2
  ... | Inl _ = true
  ... | Inr _ = false
  comp-satisfy-bool (N n1) (N̸ n2) with nat-dec n1 n2
  ... | Inl _ = false
  ... | Inr _ = true
  comp-satisfy-bool (inl τ e) (inl ξ) = comp-satisfy-bool e ξ
  comp-satisfy-bool (inr τ e) (inr ξ) = comp-satisfy-bool e ξ
  comp-satisfy-bool ⟨ e1 , e2 ⟩ ⟨ ξ1 , ξ2 ⟩ =
    comp-satisfy-bool e1 ξ1 and comp-satisfy-bool e2 ξ2
  comp-satisfy-bool e (ξ1 ∨ ξ2) = comp-satisfy-bool e ξ1 or comp-satisfy-bool e ξ2
  comp-satisfy-bool e (ξ1 ∧ ξ2) = comp-satisfy-bool e ξ1 and comp-satisfy-bool e ξ2
  -- otherwise,
  -- comp-satisfy-bool e ξ = false.
  -- we expand things out so that all clauses hold definitionally
  comp-satisfy-bool unit (N n) = false
  comp-satisfy-bool (X x) (N n) = false
  comp-satisfy-bool (·λ x ·[ τ ] e) (N n) = false
  comp-satisfy-bool (e1 ∘ e2) (N n) = false
  comp-satisfy-bool (inl τ e) (N n) = false
  comp-satisfy-bool (inr τ e) (N n) = false
  comp-satisfy-bool (match e ·: τ of rs) (N n) = false
  comp-satisfy-bool ⟨ e1 , e2 ⟩ (N n) = false
  comp-satisfy-bool (fst e) (N n) = false
  comp-satisfy-bool (snd e) (N n) = false
  comp-satisfy-bool ⦇-⦈⟨ u , σ ⟩ (N n) = false
  comp-satisfy-bool ⦇⌜ e ⌟⦈⟨ u , σ ⟩ (N n) = false
  comp-satisfy-bool unit (N̸ n) = false
  comp-satisfy-bool (X x) (N̸ n) = false
  comp-satisfy-bool (·λ x ·[ τ ] e) (N̸ n) = false
  comp-satisfy-bool (e1 ∘ e2) (N̸ n) = false
  comp-satisfy-bool (inl τ e) (N̸ n) = false
  comp-satisfy-bool (inr τ e) (N̸ n) = false
  comp-satisfy-bool (match e ·: τ of rs) (N̸ n) = false
  comp-satisfy-bool ⟨ e1 , e2 ⟩ (N̸ n) = false
  comp-satisfy-bool (fst e) (N̸ n) = false
  comp-satisfy-bool (snd e) (N̸ n) = false
  comp-satisfy-bool ⦇-⦈⟨ u , σ ⟩ (N̸ n) = false
  comp-satisfy-bool ⦇⌜ e ⌟⦈⟨ u , σ ⟩ (N̸ n) = false
  comp-satisfy-bool unit (inl ξ) = false
  comp-satisfy-bool (N n) (inl ξ) = false
  comp-satisfy-bool (X x) (inl ξ) = false
  comp-satisfy-bool (·λ x ·[ τ ] e) (inl ξ) = false
  comp-satisfy-bool (e1 ∘ e2) (inl ξ) = false
  comp-satisfy-bool (inr τ e) (inl ξ) = false
  comp-satisfy-bool (match e ·: τ of rs) (inl ξ) = false
  comp-satisfy-bool ⟨ e1 , e2 ⟩ (inl ξ) = false
  comp-satisfy-bool (fst e) (inl ξ) = false
  comp-satisfy-bool (snd e) (inl ξ) = false
  comp-satisfy-bool ⦇-⦈⟨ u , σ ⟩ (inl ξ) = false
  comp-satisfy-bool ⦇⌜ e ⌟⦈⟨ u , σ ⟩ (inl ξ) = false
  comp-satisfy-bool unit (inr ξ) = false
  comp-satisfy-bool (N n) (inr ξ) = false
  comp-satisfy-bool (X x) (inr ξ) = false
  comp-satisfy-bool (·λ x ·[ τ ] e) (inr ξ) = false
  comp-satisfy-bool (e1 ∘ e2) (inr ξ) = false
  comp-satisfy-bool (inl τ e) (inr ξ) = false
  comp-satisfy-bool (match e ·: τ of rs) (inr ξ) = false
  comp-satisfy-bool ⟨ e1 , e2 ⟩ (inr ξ) = false
  comp-satisfy-bool (fst e) (inr ξ) = false
  comp-satisfy-bool (snd e) (inr ξ) = false
  comp-satisfy-bool ⦇-⦈⟨ u , σ ⟩ (inr ξ) = false
  comp-satisfy-bool ⦇⌜ e ⌟⦈⟨ u , σ ⟩ (inr ξ) = false
  comp-satisfy-bool unit ⟨ ξ1 , ξ2 ⟩ = false
  comp-satisfy-bool (N n) ⟨ ξ1 , ξ2 ⟩ = false
  comp-satisfy-bool (X x) ⟨ ξ1 , ξ2 ⟩ = false
  comp-satisfy-bool (·λ x ·[ τ ] e) ⟨ ξ1 , ξ2 ⟩ = false
  comp-satisfy-bool (e1 ∘ e2) ⟨ ξ1 , ξ2 ⟩ = false
  comp-satisfy-bool (inl τ e) ⟨ ξ1 , ξ2 ⟩ = false
  comp-satisfy-bool (inr τ e) ⟨ ξ1 , ξ2 ⟩ = false
  comp-satisfy-bool (match e ·: τ of rs) ⟨ ξ1 , ξ2 ⟩ = false
  comp-satisfy-bool (fst e) ⟨ ξ1 , ξ2 ⟩ = false
  comp-satisfy-bool (snd e) ⟨ ξ1 , ξ2 ⟩ = false
  comp-satisfy-bool ⦇-⦈⟨ u , σ ⟩ ⟨ ξ1 , ξ2 ⟩ = false
  comp-satisfy-bool ⦇⌜ e ⌟⦈⟨ u , σ ⟩ ⟨ ξ1 , ξ2 ⟩ = false

  -- soundness of satisfy function
  comp-satisfy-sound : ∀{e ξ} →
                       e ⊧ ξ →
                       comp-satisfy-bool e ξ == true
  comp-satisfy-sound CSTruth = refl
  comp-satisfy-sound (CSNum {n = n}) with nat-dec n n
  ... | Inl refl = refl
  ... | Inr ¬n=n = abort (¬n=n refl)
  comp-satisfy-sound (CSNotNum {n1 = n1} {n2 = n2} n1≠n2) with nat-dec n1 n2
  ... | Inl refl = abort (n1≠n2 refl)
  ... | Inr n1≠n2 = refl
  comp-satisfy-sound (CSInl sat) = comp-satisfy-sound sat
  comp-satisfy-sound (CSInr sat) = comp-satisfy-sound sat
  comp-satisfy-sound (CSPair sat1 sat2) =
    and-true (comp-satisfy-sound sat1) (comp-satisfy-sound sat2)
  comp-satisfy-sound (CSOrL sat) = or-true-l (comp-satisfy-sound sat)
  comp-satisfy-sound (CSOrR sat) = or-true-r (comp-satisfy-sound sat)
  comp-satisfy-sound (CSAnd sat1 sat2) =
    and-true (comp-satisfy-sound sat1) (comp-satisfy-sound sat2)
  
  -- completeness of comp-satisfy function
  comp-satisfy-complete : ∀{e ξ} →
                          comp-satisfy-bool e ξ == true →
                          e ⊧ ξ
  comp-satisfy-complete {ξ = ·⊤} eq = CSTruth
  comp-satisfy-complete {e = N n1} {ξ = N n2} eq
    with nat-dec n1 n2
  ... | Inl refl = CSNum
  ... | Inr ¬n1=n2 with eq
  ... | ()
  comp-satisfy-complete {e = N n1} {ξ = N̸ n2} eq
    with nat-dec n1 n2
  ... | Inr ¬n1=n2 = CSNotNum ¬n1=n2
  ... | Inl refl with eq
  ... | ()
  comp-satisfy-complete {e = inl τ e} {ξ = inl ξ} eq = CSInl (comp-satisfy-complete eq)
  comp-satisfy-complete {e = inr τ e} {ξ = inr ξ} eq = CSInr (comp-satisfy-complete eq)
  comp-satisfy-complete {e = ⟨ e1 , e2 ⟩} {ξ = ⟨ ξ1 , ξ2 ⟩} eq
    with true-and {P = comp-satisfy-bool e1 ξ1} {Q = comp-satisfy-bool e2 ξ2} eq
  ... | sat1 , sat2 = CSPair (comp-satisfy-complete sat1) (comp-satisfy-complete sat2)
  comp-satisfy-complete {e = e} {ξ = ξ1 ∨ ξ2} eq
    with true-or {P = comp-satisfy-bool e ξ1} {Q = comp-satisfy-bool e ξ2} eq
  ... | Inl sat1 = CSOrL (comp-satisfy-complete sat1)
  ... | Inr sat2 = CSOrR (comp-satisfy-complete sat2)
  comp-satisfy-complete {e = e} {ξ = ξ1 ∧ ξ2} eq
    with true-and {P = comp-satisfy-bool e ξ1} {Q = comp-satisfy-bool e ξ2} eq
  ... | sat1 , sat2 = CSAnd (comp-satisfy-complete sat1) (comp-satisfy-complete sat2)
  
  -- combination of the above to explicitly show
  -- that the satisfy judgement is decidable
  comp-satisfy-dec : (e : ihexp) →
                     (ξ : comp-constr) →
                     (e ⊧ ξ) + (e ⊧ ξ → ⊥)
  comp-satisfy-dec e ξ with comp-satisfy-bool e ξ in eq
  ... | false = Inr (λ sat → false-neq-true eq (comp-satisfy-sound sat))
  ... | true = Inl (comp-satisfy-complete eq)
