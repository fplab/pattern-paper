open import Prelude

module Bool where
  data Bool : Set where
    false true : Bool
  {-# BUILTIN BOOL Bool #-}
  {-# BUILTIN TRUE true #-}
  {-# BUILTIN FALSE false #-}

  not : Bool → Bool
  not false = true
  not true = false
  
  infixr 6 _and_
  _and_ : Bool → Bool → Bool
  false and b = false
  true and b = b
  
  infixr 5 _or_
  _or_ : Bool → Bool → Bool
  false or b = b
  true or b = true

  -- when proving results about functions returning a boolean, e.g.,
  -- when arguing about decidability, Agda often struggles to match
  -- on the result, so these functions can be used instead
  neq-true-false : ∀{P} → ((P == true) → ⊥) → P == false
  neq-true-false {false} ¬true = refl
  neq-true-false {true} ¬true = abort (¬true refl)

  false-neq-true : ∀{P} → P == false → (P == true → ⊥)
  false-neq-true {false} refl = λ ()

  not-true-false : ∀{P} → not P == true → P == false
  not-true-false {false} refl = refl

  false-not-true : ∀{P} → P == false → not P == true
  false-not-true refl = refl
  
  and-true : ∀{P Q} → P == true → Q == true → (P and Q) == true
  and-true refl refl = refl

  true-and : ∀{P Q} → (P and Q) == true → (P == true) × (Q == true)
  true-and {true} {true} eq = refl , refl

  true-or : ∀{P Q} → (P or Q) == true → (P == true) + (Q == true)
  true-or {false} eq = Inr eq
  true-or {true} eq = Inl refl
  
  or-true-l : ∀{P Q} → P == true → P or Q == true
  or-true-l refl = refl
  
  or-true-r : ∀{P Q} → Q == true → P or Q == true
  or-true-r {P} refl with P
  ... | false = refl
  ... | true = refl


  
