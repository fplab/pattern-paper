open import Prelude
open import Nat

module List where
  infixr 5 _::_

  -- standard definition of polymorphic lists
  data List (A : Set) : Set where
    [] : List A
    _::_ : A → List A → List A

  {-# BUILTIN LIST List #-}
  
  -- list append
  infixr 5 _++_
  _++_ : {A : Set} → List A → List A → List A
  [] ++ l2 = l2
  (x :: l1) ++ l2 = x :: (l1 ++ l2)

  -- number of elements in a list
  length : {A : Set} → List A → Nat
  length [] = 0
  length (x :: xs) = suc (length xs)
  
  -- map f to every element of a list
  map : {A B : Set} → (A → B) → List A → List B
  map f [] = []
  map f (x :: xs) = f x :: map f xs
  
  -- O(n^2) list reverse
  reverse : {A : Set} → List A → List A
  reverse [] = []
  reverse (x :: l) = l ++ (x :: [])

  -- an element is contained within a list
  data _∈l_ {A : Set} : A → List A → Set where
    here  : ∀{y xs} →
            y ∈l (y :: xs)
    there : ∀{y x xs} →
            y ∈l xs →
            y ∈l (x :: xs)
