open import Prelude

module Nat where
  data Nat : Set where
    zero : Nat
    suc : Nat → Nat

  {-# BUILTIN NATURAL Nat #-}

  -- the succ operation is injective
  suc-inj : (x y : Nat) →
           (suc x == suc y) →
           x == y
  suc-inj zero .0 refl = refl
  suc-inj (suc x) .(suc x) refl = refl

  -- equality of naturals is decidable
  nat-dec : (x y : Nat) →
            ((x == y) + ((x == y) → ⊥))
  nat-dec zero zero = Inl refl
  nat-dec zero (suc y) = Inr (λ ())
  nat-dec (suc x) zero = Inr (λ ())
  nat-dec (suc x) (suc y) with nat-dec x y
  ... | Inl refl = Inl refl
  ... | Inr x≠y = Inr (λ refl → x≠y (suc-inj x y refl))

  -- we already use + for sum types, so we use ✦ for the sum of nats
  infixl 6 _✦_
  _✦_ : Nat → Nat → Nat
  zero ✦ y = y
  (suc x) ✦ y = suc (x ✦ y)

  ✦-identityʳ : (n : Nat) → n ✦ 0 == n
  ✦-identityʳ zero = refl
  ✦-identityʳ (suc n) =
    ap1 (λ qq → suc qq) (✦-identityʳ n) 

  ✦-suc : (m n : Nat) → m ✦ (suc n) == suc (m ✦ n)
  ✦-suc zero n = refl
  ✦-suc (suc m) n = ap1 (λ qq → suc qq) (✦-suc m n)
  
  ✦-comm : (m n : Nat) → m ✦ n == n ✦ m
  ✦-comm m zero = ✦-identityʳ m
  ✦-comm m (suc n) =
    ✦-suc m n · ap1 (λ qq → suc qq) (✦-comm m n) 

  ✦-assoc : (a b c : Nat) →
            a ✦ (b ✦ c) == (a ✦ b) ✦ c
  ✦-assoc zero b c = refl
  ✦-assoc (suc a) b c = ap1 suc (✦-assoc a b c)

  infix 4 _<_
  data _<_ : Nat → Nat → Set where
    z<suc : ∀{n} → zero < (suc n)
    suc<suc : ∀{m n} → m < n → (suc m) < (suc n)

  n<sucn : (n : Nat) →
           n < (suc n)
  n<sucn zero = z<suc
  n<sucn (suc n) = suc<suc (n<sucn n)

  <-≠ : ∀{n m} →
        n < m →
        n ≠ m
  <-≠ (suc<suc m<m) refl = <-≠ m<m refl

  <suc-≤ : ∀{n m} →
           n < suc m →
           (n < m) + (n == m)
  <suc-≤ {n = .zero} {m = zero} z<suc = Inr refl
  <suc-≤ {n = .zero} {m = suc m} z<suc = Inl z<suc
  <suc-≤ {n = suc n} {m = suc m} (suc<suc n<sucm)
    with <suc-≤ n<sucm
  ... | Inl n<m = Inl (suc<suc n<m)
  ... | Inr refl = Inr refl
  
  <-trans-suc : ∀{a b c} →
                a < suc b →
                b < c →
                a < c
  <-trans-suc z<suc z<suc = z<suc
  <-trans-suc z<suc (suc<suc b<c) = z<suc
  <-trans-suc (suc<suc a<sucb) (suc<suc b<c) =
    suc<suc (<-trans-suc a<sucb b<c)

  <-trans : {a b c : Nat} →
            a < b →
            b < c →
            a < c
  <-trans z<suc (suc<suc b<c) = z<suc
  <-trans (suc<suc a<b) (suc<suc b<c) =
    suc<suc (<-trans a<b b<c)
  
  ✦-monoʳ-< : (a b c : Nat) →
              b < c →
              (a ✦ b) < (a ✦ c)
  ✦-monoʳ-< zero b c b<c = b<c
  ✦-monoʳ-< (suc a) b c b<c = suc<suc (✦-monoʳ-< a b c b<c)
  
  ✦-monoˡ-< : (a b c : Nat) →
              b < c →
              (b ✦ a) < (c ✦ a)
  ✦-monoˡ-< a b c b<c =
    tr (λ qq → qq < (c ✦ a)) (✦-comm a b)
      (tr (λ qq → (a ✦ b) < qq) (✦-comm a c)
        (✦-monoʳ-< a b c b<c))
       
  ✦-mono-< : {a b c d : Nat} →
             a < b →
             c < d →
             (a ✦ c) < (b ✦ d)
  ✦-mono-< {a = a} {b = b} {c = c} {d = d}
           a<b c<d =
    <-trans (✦-monoˡ-< c a b a<b)
            (✦-monoʳ-< b c d c<d)

  ✦-mono-<-suc : {a b c d : Nat} →
                 a < b →
                 c < suc d →
                 (a ✦ c) < (b ✦ d)
  ✦-mono-<-suc {a = a} {b = b} {c = c} {d = d}
               a<b c<sucd
    with <suc-≤ c<sucd
  ... | Inl c<d = ✦-mono-< a<b c<d
  ... | Inr refl = ✦-monoˡ-< c a b a<b
  
  max : Nat → Nat → Nat
  max zero n = n
  max (suc m) zero = suc m
  max (suc m) (suc n) = suc (max m n)

  arg1<sucmax : (m n : Nat) →
                m < suc (max m n)
  arg1<sucmax zero n = z<suc
  arg1<sucmax (suc m) zero = suc<suc (n<sucn m)
  arg1<sucmax (suc m) (suc n) =
    suc<suc (arg1<sucmax m n)

  arg2<sucmax : (m n : Nat) →
                n < suc (max m n)
  arg2<sucmax zero n = n<sucn n
  arg2<sucmax (suc m) zero = z<suc
  arg2<sucmax (suc m) (suc n) =
    suc<suc (arg2<sucmax m n)
