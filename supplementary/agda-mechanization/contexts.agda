open import Prelude
open import Nat

module contexts where
  -- we represent contexts as functions from variable names
  -- to possible bindings. for simplicity, this mechanization
  -- assumes all variable names are natural numbers
  _ctx : Set → Set
  A ctx = Nat → Maybe A

  -- convenient shorthand for the
  -- (unique up to function extensionality) empty context
  ∅ : {A : Set} → A ctx
  ∅ _ = None

  -- the domain of a context is those naturals
  -- which cuase it to emit some τ
  dom : {A : Set} → A ctx → Nat → Set
  dom {A} Γ x = Σ[ τ ∈ A ] (Γ x == Some τ)

  -- membership, or presence, in a context
  _∈_ : {A : Set} (p : Nat × A) → (Γ : A ctx) → Set
  (x , τ) ∈ Γ = (Γ x) == Some τ
  
  -- apartness for contexts
  _#_ : {A : Set} (n : Nat) →
        (Γ : A ctx) →
        Set
  x # Γ = (Γ x) == None

  -- disjoint contexts are those which share no mappings
  _##_ : {A : Set} → A ctx → A ctx → Set
  _##_ {A} Γ1 Γ2 =
    ((x : Nat) → dom Γ1 x → x # Γ2) ×
     ((x : Nat) → dom Γ2 x → x # Γ1)

  -- WARNING : this union is asymmetric unless the
  -- contexts are disjoint. the left hand side context is
  -- preferred when there is an overlap
  _∪_ : {A : Set} → A ctx → A ctx → A ctx
  (Γ1 ∪ Γ2) x with Γ1 x
  ... | Some τ = Some τ
  ... | None = Γ2 x
  
  -- the singleton context
  ■_ : {A : Set} → (Nat × A) → A ctx
  (■ (x , τ)) y with nat-dec x y
  ... | Inl refl = Some τ
  ... | Inr _ = None

  infix 25 ■_
  
  -- context extension. note that due to the asymmetry of unions,
  -- this will update the binding of x if x is not apart from Γ
  _,,_ : {A : Set} → A ctx → (Nat × A) → A ctx
  (Γ ,, (x , τ)) = (■ (x , τ)) ∪ Γ

  infixl 10 _,,_

  -- difference. Γ1 but with any element of Γ2 removed
  _∖_ : {A : Set} → A ctx → A ctx → A ctx
  (Γ1 ∖ Γ2) x with Γ2 x
  ... | Some _ = None
  ... | None = Γ1 x
