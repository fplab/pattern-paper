open import Nat
open import Prelude
open import complete-satisfy-decidable
open import complete-constraints-core
open import contexts
open import core
open import result-judgements
open import statics-core
open import value-judgements

-- theorem showing that duals are indeed duals, i.e.,
-- an expression satisfies a constraint if and only if
-- it does not satisfy the dual
module complete-satisfy-exclusive where
  -- lemma showing that a value is does not satisfy
  -- a constraint only if its dual does satisfy it
  val-not-sat-sat-dual : ∀{Δ Δp e τ ξ} →
                         e val →
                         ∅ , Δ , Δp ⊢ e :: τ →
                         ξ :cc: τ →
                         (e ⊧ ξ → ⊥) →
                         e ⊧ (ξ ◆d)
  val-not-sat-sat-dual {ξ = ·⊤} eval wt ct ¬sat = abort (¬sat CSTruth)
  val-not-sat-sat-dual {ξ = ·⊥} eval wt ct ¬sat = CSTruth
  val-not-sat-sat-dual {ξ = N n} eval (TNum {n = m}) ct ¬sat
    with nat-dec m n
  ... | Inl refl = CSNotNum (λ _ → ¬sat CSNum)
  ... | Inr m≠n = CSNotNum m≠n
  val-not-sat-sat-dual {ξ = N̸ n} eval (TNum {n = m}) ct ¬sat
    with nat-dec m n
  ... | Inl refl = CSNum
  ... | Inr m≠n = abort (¬sat (CSNotNum m≠n))
  val-not-sat-sat-dual {e = inl τ e} {ξ = inl ξ}
                     (VInl eval) (TInl wt) (CTInl ct) ¬sat
    with comp-satisfy-dec e ξ
  ... | Inl esat = abort (¬sat (CSInl esat))
  ... | Inr ¬esat = CSOrL (CSInl (val-not-sat-sat-dual eval wt ct ¬esat))
  val-not-sat-sat-dual {e = inr τ e} {ξ = inl ξ}
                     (VInr eval) (TInr wt) (CTInl ct) ¬sat =
    CSOrR (CSInr CSTruth)
  val-not-sat-sat-dual {e = inl τ e} {ξ = inr ξ}
                     (VInl eval) (TInl wt) (CTInr ct) ¬sat =
    CSOrR (CSInl CSTruth)
  val-not-sat-sat-dual {e = inr τ e} {ξ = inr ξ}
                     (VInr eval) (TInr wt) (CTInr ct) ¬sat
    with comp-satisfy-dec e ξ
  ... | Inl esat = abort (¬sat (CSInr esat))
  ... | Inr ¬esat = CSOrL (CSInr (val-not-sat-sat-dual eval wt ct ¬esat))
  val-not-sat-sat-dual {e = ⟨ e1 , e2 ⟩} {ξ = ⟨ ξ1 , ξ2 ⟩}
                     (VPair eval1 eval2) (TPair wt1 wt2)
                     (CTPair ct1 ct2) ¬sat
    with comp-satisfy-dec e1 ξ1 | comp-satisfy-dec e2 ξ2
  ... | Inl sat1 | Inl sat2 = abort (¬sat (CSPair sat1 sat2))
  ... | Inl sat1 | Inr ¬sat2 =
    CSOrL (CSOrL (CSPair sat1 (val-not-sat-sat-dual eval2 wt2 ct2 ¬sat2)))
  ... | Inr ¬sat1 | Inl sat2 =
    CSOrL (CSOrR (CSPair (val-not-sat-sat-dual eval1 wt1 ct1 ¬sat1) sat2))
  ... | Inr ¬sat1 | Inr ¬sat2 =
    CSOrR (CSPair (val-not-sat-sat-dual eval1 wt1 ct1 ¬sat1)
                  (val-not-sat-sat-dual eval2 wt2 ct2 ¬sat2))
  val-not-sat-sat-dual {e = e} {ξ = ξ1 ∨ ξ2} eval wt (CTOr ct1 ct2) ¬sat
    with comp-satisfy-dec e ξ1 | comp-satisfy-dec e ξ2
  ... | Inl sat1 | Inl sat2 = abort (¬sat (CSOrL sat1))
  ... | Inl sat1 | Inr ¬sat2 = abort (¬sat (CSOrL sat1))
  ... | Inr ¬sat1 | Inl sat2 = abort (¬sat (CSOrR sat2))
  ... | Inr ¬sat1 | Inr ¬sat2 =
    CSAnd (val-not-sat-sat-dual eval wt ct1 ¬sat1)
          (val-not-sat-sat-dual eval wt ct2 ¬sat2)
  val-not-sat-sat-dual {e = e} {ξ = ξ1 ∧ ξ2} eval wt (CTnd ct1 ct2) ¬sat
    with comp-satisfy-dec e ξ1 | comp-satisfy-dec e ξ2
  ... | Inl sat1 | Inl sat2 = abort (¬sat (CSAnd sat1 sat2))
  ... | Inl sat1 | Inr ¬sat2 = CSOrR (val-not-sat-sat-dual eval wt ct2 ¬sat2)
  ... | Inr ¬sat1 | Inl sat2 = CSOrL (val-not-sat-sat-dual eval wt ct1 ¬sat1)
  ... | Inr ¬sat1 | Inr ¬sat2 = CSOrL (val-not-sat-sat-dual eval wt ct1 ¬sat1)

  -- converse of the above, i.e., if the dual satisfies a constraint
  -- then the original constraint does not
  val-sat-dual-not-sat : ∀{e ξ} →
                         e val →
                         e ⊧ (ξ ◆d) →
                         e ⊧ ξ →
                         ⊥
  val-sat-dual-not-sat {ξ = N n} eval (CSNotNum n≠n) CSNum = n≠n refl
  val-sat-dual-not-sat {ξ = N̸ n} eval CSNum (CSNotNum n≠n) = n≠n refl
  val-sat-dual-not-sat {ξ = inl ξ} (VInl eval) (CSOrL (CSInl satd)) (CSInl sat) =
    val-sat-dual-not-sat eval satd sat
  val-sat-dual-not-sat {ξ = inr ξ} (VInr eval) (CSOrL (CSInr satd)) (CSInr sat) =
    val-sat-dual-not-sat eval satd sat
  val-sat-dual-not-sat {ξ = ⟨ ξ1 , ξ2 ⟩} (VPair eval1 eval2)
                     (CSOrL (CSOrL (CSPair satd1 satd2))) (CSPair sat1 sat2) =
    val-sat-dual-not-sat eval2 satd2 sat2
  val-sat-dual-not-sat {ξ = ⟨ ξ1 , ξ2 ⟩} (VPair eval1 eval2)
                     (CSOrL (CSOrR (CSPair satd1 satd2))) (CSPair sat1 sat2) =
    val-sat-dual-not-sat eval1 satd1 sat1
  val-sat-dual-not-sat {ξ = ⟨ ξ1 , ξ2 ⟩} (VPair eval1 eval2)
                     (CSOrR (CSPair satd1 satd2)) (CSPair sat1 sat2) =
    val-sat-dual-not-sat eval2 satd2 sat2
  val-sat-dual-not-sat {ξ = ξ1 ∨ ξ2} eval (CSAnd satd1 satd2) (CSOrL sat) =
    val-sat-dual-not-sat eval satd1 sat
  val-sat-dual-not-sat {ξ = ξ1 ∨ ξ2} eval (CSAnd satd1 satd2) (CSOrR sat) =
    val-sat-dual-not-sat eval satd2 sat
  val-sat-dual-not-sat {ξ = ξ1 ∧ ξ2} eval (CSOrL satd) (CSAnd sat1 sat2) =
    val-sat-dual-not-sat eval satd sat1
  val-sat-dual-not-sat {ξ = ξ1 ∧ ξ2} eval (CSOrR satd) (CSAnd sat1 sat2) =
    val-sat-dual-not-sat eval satd sat2
  
  -- result of the exclusivity theorem
  data ExCompSat (e : ihexp) (ξ : comp-constr) : Set where
    Satisfy     : (e ⊧ ξ)     → (e ⊧ (ξ ◆d) → ⊥) → ExCompSat e ξ
    SatisfyDual : (e ⊧ ξ → ⊥) → (e ⊧ (ξ ◆d))     → ExCompSat e ξ

  -- for a value e and constraint ξ of the same type,
  -- e satisfies either ξ or its dual, but not both
  comp-satisfy-exclusive : ∀{ξ τ Δ Δp e} →
                           ξ :cc: τ →
                           ∅ , Δ , Δp ⊢ e :: τ →
                           e val →
                           ExCompSat e ξ
  comp-satisfy-exclusive {ξ = ξ} {e = e} ct wt eval
    with comp-satisfy-dec e ξ | comp-satisfy-dec e (ξ ◆d)
  ... | Inl sat | Inl satd =
    abort (val-sat-dual-not-sat eval satd sat)
  ... | Inr ¬sat | Inr ¬satd =
    abort (¬satd (val-not-sat-sat-dual eval wt ct ¬sat))
  ... | Inl sat | Inr ¬satd = Satisfy sat ¬satd
  ... | Inr ¬sat | Inl satd = SatisfyDual ¬sat satd

  
