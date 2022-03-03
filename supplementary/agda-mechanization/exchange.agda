open import Prelude
open import Nat
open import core
open import contexts
open import lemmas-contexts
open import statics-core

module exchange where
  -- contexts with two disequal elements exchanged
  -- are the same. we reassociate the unions,
  -- swap as above, and then associate them back.
  swap : {A : Set} {x y : Nat} {τ1 τ2 : A} →
         (Γ : A ctx) →
         (x≠y : x == y → ⊥) →
         ((Γ ,, (x , τ1)) ,, (y , τ2)) ==
           ((Γ ,, (y , τ2)) ,, (x , τ1))
  swap {A} {x} {y} {τ1} {τ2} Γ neq = funext eq
    where
      eq : (z : Nat) →
           ((Γ ,, (x , τ1)) ,, (y , τ2)) z ==
             ((Γ ,, (y , τ2)) ,, (x , τ1)) z
      eq z with nat-dec y z
      ... | Inr y≠z with nat-dec x z
      ... | Inl refl = refl
      ... | Inr x≠z with nat-dec y z
      ... | Inl refl = abort (y≠z refl)
      ... | Inr y≠z' = refl
      eq z | Inl refl with nat-dec x z
      ... | Inl refl = abort (neq refl)
      ... | Inr x≠z with nat-dec z z
      ... | Inl refl = refl
      ... | Inr z≠z = abort (z≠z refl)

  exchange-ta-Γ : ∀{Γ Δ Δp x y τ1 τ2 e τ} →
                  x ≠ y →
                  (Γ ,, (x , τ1) ,, (y , τ2)) , Δ , Δp ⊢ e :: τ →
                  (Γ ,, (y , τ2) ,, (x , τ1)) , Δ , Δp ⊢ e :: τ
  exchange-ta-Γ {Γ = Γ} {Δ = Δ} {Δp = Δp} {e = e} {τ = τ} x≠y wt =
    tr (λ qq → qq , Δ , Δp ⊢ e :: τ) (swap Γ x≠y) wt
