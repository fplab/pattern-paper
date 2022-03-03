open import Nat
open import Prelude
open import contexts

module lemmas-contexts where
  -- contexts give at most one binding for each variable
  ctx-unicity : {A : Set} {Γ : A ctx} {x : Nat} {τ τ' : A} →
                (x , τ) ∈ Γ →
                (x , τ') ∈ Γ →
                τ == τ'
  ctx-unicity {x = x} p q with nat-dec x x
  ... | Inl refl = some-inj (! p · q)
  ... | Inr x≠x = abort (x≠x refl)

  -- order of extension is irrelevant
  ctx-exchange : {A : Set} {x y : Nat} {τ1 τ2 : A} →
                 (Γ : A ctx) →
                 x ≠ y →
                 ((Γ ,, (x , τ1)) ,, (y , τ2)) ==
                 ((Γ ,, (y , τ2)) ,, (x , τ1))
  ctx-exchange {x = x} {y = y} {τ1 = τ1} {τ2 = τ2}
               Γ x≠y = funext eq
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
      ... | Inl refl = abort (x≠y refl)
      ... | Inr x≠z with nat-dec z z
      ... | Inl refl = refl
      ... | Inr z≠z = abort (z≠z refl)


  -- an element is in the context formed with just itself
  self-dom-singleton : {A : Set} (x : Nat) (τ : A) →
                       (x , τ) ∈ (■ (x , τ))
  self-dom-singleton x τ with nat-dec x x
  ... | Inl refl = refl
  ... | Inr x≠x = abort (x≠x refl)
  
  -- if an index is in the domain of a singleton context,
  -- it is exactly the index in the singleton
  dom-singleton-eq : {A : Set} {τ : A} {x y : Nat} →
                     dom (■ (y , τ)) x →
                     x == y
  dom-singleton-eq {x = x} {y = y} (τ' , x∈■) with nat-dec y x
  ... | Inl refl = refl
  ... | Inr y≠x = abort (some-not-none (! x∈■))

  -- if an index is apart from a context,
  -- then its singleton is dijoint from that context
  apart-singleton-disjoint : {A : Set} {Γ : A ctx} {x : Nat} {τ : A}  →
                             x # Γ →
                             (■ (x , τ)) ## Γ
  apart-singleton-disjoint {Γ = Γ} {x = x} {τ = τ} x#Γ = disj1 , disj2
    where
      disj1 : (y : Nat) → dom (■ (x , τ)) y → y # Γ
      disj1 y y∈■ with dom-singleton-eq y∈■
      ... | refl = x#Γ

      disj2 : (y : Nat) → dom Γ y → y # (■ (x , τ))
      disj2 y (τ' , y∈■) with nat-dec x y
      ... | Inl refl = abort (some-not-none (! y∈■ · x#Γ ))
      ... | Inr x≠y = refl

  -- if a singleton is disjoint from a context,
  -- then its index is apart from that context
  disjoint-singleton-apart : {A : Set} {Γ : A ctx} {x : Nat} {τ : A} →
                             (■ (x , τ)) ## Γ →
                             x # Γ
  disjoint-singleton-apart {x = x} {τ = τ} (disj1 , disj2) =
    disj1 x (τ , self-dom-singleton x τ)

  -- if an index is apart from a singleton context,
  -- then it is not equal to the index of that singleton
  apart-singleton-neq : {A : Set} {x y : Nat} {τ : A} →
                        x # (■ (y , τ)) →
                        x ≠ y
  apart-singleton-neq {x = x} {y = y} x#■  with nat-dec y x
  ... | Inl refl = abort (some-not-none x#■)
  ... | Inr y≠x = flip y≠x

  -- if and index is not equal to the index of a singleton,
  -- then it is apart from that singleton context
  neq-apart-singleton : {A : Set} {x y : Nat} {τ : A} →
                        x ≠ y →
                        x # (■ (y , τ))
  neq-apart-singleton {x = x} {y = y} x≠y with nat-dec y x
  ... | Inl refl = abort (x≠y refl)
  ... | Inr y≠x = refl

  -- empty is the identity wrt unions
  ∪-identityʳ : {A : Set} (Γ : A ctx) →
                Γ ∪ ∅ == Γ
  ∪-identityʳ Γ = funext eq
    where
      eq : (x : Nat) →
           (Γ ∪ ∅) x == Γ x
      eq x
        with Γ x
      ... | Some τ = refl
      ... | None = refl
      
  ∪-identityˡ : {A : Set} (Γ : A ctx) →
                ∅ ∪ Γ == Γ
  ∪-identityˡ {A = A} Γ = funext eq
    where
      eq : (x : Nat) →
           (∅ ∪ Γ) x == Γ x
      eq x
        with (∅ {A = A}) x
      ... | Some τ = refl
      ... | None = refl
                
  -- union is associative
  ∪-assoc : {A : Set} (Γ1 Γ2 Γ3 : A ctx) →
            (Γ1 ∪ Γ2) ∪ Γ3 == Γ1 ∪ (Γ2 ∪ Γ3)
  ∪-assoc Γ1 Γ2 Γ3 = funext eq
    where
      eq : (z : Nat) →
           ((Γ1 ∪ Γ2) ∪ Γ3) z == (Γ1 ∪ (Γ2 ∪ Γ3)) z
      eq z with Γ1 z
      ... | Some τ1 = refl
      ... | None with Γ2 z
      ... | Some τ2 = refl
      ... | None = refl

  -- if the contexts in are disjoint, then union is commutative
  ∪-comm : {A : Set} →
           (Γ1 Γ2 : A ctx) →
           Γ1 ## Γ2 →
           (Γ1 ∪ Γ2) == (Γ2 ∪ Γ1)
  ∪-comm Γ1 Γ2 (disj1 , disj2) = funext eq
    where
      eq : (x : Nat) → (Γ1 ∪ Γ2) x == (Γ2 ∪ Γ1) x
      eq x with Γ1 x in Γ1x | Γ2 x in Γ2x
      ... | Some τ1 | Some τ2 =
        abort (some-not-none (! Γ2x · disj1 x (τ1 , Γ1x)))
      ... | Some τ1 | None = ! Γ1x
      ... | None | Some τ2 = Γ2x
      ... | None | None = Γ2x · ! Γ1x

  -- union and extension satisfy some associative-like relation
  union-extend-assoc : {A : Set} (Γ1 Γ2 : A ctx) (x : Nat) (τ : A) →
                       (Γ1 ∪ Γ2) ,, (x , τ) == (Γ1 ,, (x , τ)) ∪ Γ2
  union-extend-assoc Γ1 Γ2 x τ = ! (∪-assoc (■ (x , τ)) Γ1 Γ2)

  -- union with yourself is yourself
  union-with-self : {A : Set} (Γ : A ctx) →
                    Γ ∪ Γ == Γ
  union-with-self Γ = funext eq
    where
      eq : (x : Nat) →
           (Γ ∪ Γ) x == Γ x
      eq x with Γ x in Γx
      ... | Some τ = refl
      ... | None = Γx

  -- an element in the left of a union is in the union
  dom-l-union : {A : Set} →
                (Γ1 Γ2 : A ctx) (x : Nat) (τ : A) →
                (x , τ) ∈ Γ1 →
                (x , τ) ∈ (Γ1 ∪ Γ2)
  dom-l-union Γ1 Γ2 x τ x∈Γ1 with Γ1 x
  dom-l-union Γ1 Γ2 x τ x∈Γ1 | Some τ1 = x∈Γ1
  dom-l-union Γ1 Γ2 x τ () | None

  -- an element in the right of a union is in the union,
  -- so long as it is not in the left of the union.
  -- this asymmetry reflects the asymmetry in the definition of union
  dom-r-union : {A : Set} →
                (Γ1 Γ2 : A ctx) (x : Nat) (τ : A) →
                (x , τ) ∈ Γ2 →
                x # Γ1 →
                (x , τ) ∈ (Γ1 ∪ Γ2)
  dom-r-union Γ1 Γ2 x τ x∈Γ2 x#Γ with Γ1 x
  ... | None = x∈Γ2

  -- if an index is in the union, it is in one of the parts
  dom-union-part : {A : Set} →
                   (Γ1 Γ2 : A ctx) (x : Nat) (τ : A) →
                   (x , τ) ∈ (Γ1 ∪ Γ2) →
                   ((x , τ) ∈ Γ1) + ((x , τ) ∈ Γ2)
  dom-union-part Γ1 Γ2 x τ x∈Γ1∪Γ2 with Γ1 x
  ... | Some τ1 = Inl x∈Γ1∪Γ2
  ... | None = Inr x∈Γ1∪Γ2
  
  -- since unions prefer the left hand side context for overlaps,
  -- removing the overlap from the right hand side produces
  -- the same context
  union-with-diff : {A : Set} →
                    (Γ1 Γ2 : A ctx) →
                    (Γ1 ∪ Γ2) == Γ1 ∪ (Γ2 ∖ Γ1)
  union-with-diff Γ1 Γ2 = funext eq
    where
      eq : (x : Nat) → (Γ1 ∪ Γ2) x == (Γ1 ∪ (Γ2 ∖ Γ1)) x
      eq x with Γ1 x in Γ1x
      ... | Some τ1 = refl
      ... | None
        with Γ1 x
      ... | Some _ = abort (some-not-none Γ1x)
      ... | None = refl

  -- if an index is in the difference,
  -- then it is in the left of the difference
  dom-diff-dom-l : {A : Set} {Γ1 Γ2 : A ctx} {x : Nat} {τ : A} →
                   (x , τ) ∈ (Γ1 ∖ Γ2) →
                   (x , τ) ∈ Γ1
  dom-diff-dom-l {Γ2 = Γ2} {x = x} x∈Γ1∖Γ2
    with Γ2 x
  ... | Some τ' = abort (some-not-none (! x∈Γ1∖Γ2))
  ... | None = x∈Γ1∖Γ2

  -- if and index is in the difference,
  -- then it is apart from the right of the difference
  dom-diff-apart-r : {A : Set} {Γ1 Γ2 : A ctx} {x : Nat} {τ : A} →
                     (x , τ) ∈ (Γ1 ∖ Γ2) →
                     x # Γ2
  dom-diff-apart-r {Γ2 = Γ2} {x = x} x∈Γ1∖Γ2 
    with Γ2 x
  ... | None = refl
  
  -- the right hand side of a difference is
  -- disjoint with that difference
  r-disjoint-diff-r : {A : Set} (Γ1 Γ2 : A ctx) →
                      Γ2 ## (Γ1 ∖ Γ2)
  r-disjoint-diff-r Γ1 Γ2 = disj1 , disj2
    where
      disj1 : (x : Nat) →
              dom Γ2 x →
              x # (Γ1 ∖ Γ2)
      disj1 x x∈Γ2
        with Γ2 x
      ... | Some _ = refl
      
      disj2 : (x : Nat) →
              dom (Γ1 ∖ Γ2) x →
              x # Γ2
      disj2 x x∈Γ1∖Γ2
        with Γ2 x
      ... | None = refl

  -- extending with a distinct index preserves apartness
  neq-apart-extend : {A : Set} {x y : Nat} {τ : A} →
                     (Γ : A ctx) →
                     x ≠ y →
                     x # Γ →
                     x # (Γ ,, (y , τ))
  neq-apart-extend {x = x} {y = y} Γ x≠y x#Γ with nat-dec y x
  ... | Inl refl = abort (x≠y refl)
  ... | Inr y≠x = x#Γ
  
  -- if an index is apart from a union,
  -- then it is apart from the left unand
  apart-union-l : {A : Set} (Γ1 Γ2 : A ctx) (x : Nat) →
                  x # (Γ1 ∪ Γ2) →
                  x # Γ1
  apart-union-l Γ1 Γ2 n aprt with Γ1 n
  apart-union-l Γ1 Γ2 n () | Some x
  apart-union-l Γ1 Γ2 n aprt | None = refl

  -- if an index is apart from a union,
  -- then it is apart from the right unand
  apart-union-r : {A : Set} (Γ1 Γ2 : A ctx) (n : Nat) →
                  n # (Γ1 ∪ Γ2) →
                  n # Γ2
  apart-union-r Γ1 Γ2 n aprt with Γ1 n
  apart-union-r Γ3 Γ4 n () | Some x
  apart-union-r Γ3 Γ4 n aprt | None = aprt


  -- if an index is apart from two contexts, it's apart from their union
  apart-parts : {A : Set} (Γ1 Γ2 : A ctx) (x : Nat) →
                x # Γ1 →
                x # Γ2 →
                x # (Γ1 ∪ Γ2)
  apart-parts Γ1 Γ2 x apt1 apt2 with Γ1 x
  apart-parts Γ1 Γ2 x refl apt2 | .None = apt2

  -- disjointness is commutative
  ##-sym : {A : Set} {Γ1 Γ2 : A ctx} →
           Γ1 ## Γ2 →
           Γ2 ## Γ1
  ##-sym (disj1 , disj2) = disj2 , disj1

  
  disj-union-unicity-l : {A : Set} {Γ1 Γ1' Γ2 : A ctx} →
                         Γ1 ## Γ2 →
                         Γ1' ## Γ2 →
                         (Γ1 ∪ Γ2) == (Γ1' ∪ Γ2) →
                         Γ1 == Γ1'
  disj-union-unicity-l {Γ1 = Γ1} {Γ1' = Γ1'} {Γ2 = Γ2}
                       Γ1##Γ2 Γ1'##Γ2 eq∪ =
    funext eq 
    where
      eq : (x : Nat) → Γ1 x == Γ1' x
      eq x with Γ2 x in Γ2x
      ... | Some τ2 =
        π2 Γ1##Γ2 x (τ2 , Γ2x) ·
          ! (π2 Γ1'##Γ2 x (τ2 , Γ2x))
      ... | None
         with Γ1 x in Γ1x | Γ1' x in Γ1'x
      eq x | None | Some τ1 | Some τ1'
        with dom-union-part Γ1 Γ2 x τ1'
                            (tr (λ qq → (x , τ1') ∈ qq )
                                (! eq∪)
                                (dom-l-union Γ1' Γ2 x τ1' Γ1'x))
      ... | Inl x∈Γ1 = ! Γ1x · x∈Γ1
      ... | Inr x∈Γ2 = abort (some-not-none (! x∈Γ2 · Γ2x))
      eq x | None | None | Some τ1'
        with dom-union-part Γ1 Γ2 x τ1'
                            (tr (λ qq → (x , τ1') ∈ qq )
                                (! eq∪)
                                (dom-l-union Γ1' Γ2 x τ1' Γ1'x))
      ... | Inl x∈Γ1 = abort (some-not-none (! x∈Γ1 · Γ1x))
      ... | Inr x∈Γ2 = abort (some-not-none (! x∈Γ2 · Γ2x))
      eq x | None | Some τ1 | None
        with dom-union-part Γ1' Γ2 x τ1
                            (tr (λ qq → (x , τ1) ∈ qq )
                                eq∪
                                (dom-l-union Γ1 Γ2 x τ1 Γ1x))
      ... | Inl x∈Γ1' = abort (some-not-none (! x∈Γ1' · Γ1'x))
      ... | Inr x∈Γ2 = abort (some-not-none (! x∈Γ2 · Γ2x))
      eq x | None | None | None = refl

  disj-union-unicity-r : {A : Set} {Γ1 Γ2 Γ2' : A ctx} →
                         Γ1 ## Γ2 →
                         Γ1 ## Γ2' →
                         (Γ1 ∪ Γ2) == (Γ1 ∪ Γ2') →
                         Γ2 == Γ2'
  disj-union-unicity-r {Γ1 = Γ1} {Γ2 = Γ2} {Γ2' = Γ2'}
                       Γ1##Γ2 Γ1##Γ2' eq∪ =
    disj-union-unicity-l (##-sym Γ1##Γ2)
                         (##-sym Γ1##Γ2')
                         (∪-comm Γ2 Γ1 (##-sym Γ1##Γ2) ·
                           (eq∪ · ∪-comm Γ1 Γ2' Γ1##Γ2'))
  
  -- if a union is disjoint with a target, so is the left unand
  union-disjoint-l : {A : Set} {Γ1 Γ2 Γ3 : A ctx} →
                     (Γ1 ∪ Γ2) ## Γ3 →
                     Γ1 ## Γ3
  union-disjoint-l {Γ1 = Γ1} {Γ2 = Γ2} {Γ3 = Γ3} (ud1 , ud2) = du11 , du12
    where
      dom-union1 : {A : Set} (Γ1 Γ2 : A ctx) (n : Nat) →
                   dom Γ1 n →
                   dom (Γ1 ∪ Γ2) n
      dom-union1 Γ1 Γ2 n (π1 , π2) with Γ1 n
      dom-union1 Γ1 Γ2 n (π1 , π2) | Some x = x , refl
      dom-union1 Γ1 Γ2 n (π1 , ()) | None

      du11 : (n : Nat) → dom Γ1 n → n # Γ3
      du11 n dom = ud1 n (dom-union1 Γ1 Γ2 n dom)

      du12 : (n : Nat) → dom Γ3 n → n # Γ1
      du12 n dom = apart-union-l Γ1 Γ2 n (ud2 n dom)

  -- if a union is disjoint with a target, so is the right unand
  union-disjoint-r : {A : Set} {Γ1 Γ2 Δ : A ctx} →
                     (Γ1 ∪ Γ2) ## Δ →
                     Γ2 ## Δ
  union-disjoint-r {Γ1 = Γ1} {Γ2 = Γ2} {Δ = Δ} (ud1 , ud2) = du21 , du22
    where
      dom-union2 : {A : Set} (Γ1 Γ2 : A ctx) (x : Nat) →
                   dom Γ2 x →
                   dom (Γ1 ∪ Γ2) x
      dom-union2 Γ1 Γ2 n (π1 , π2) with Γ1 n
      dom-union2 Γ3 Γ4 n (π1 , π2) | Some x = x , refl
      dom-union2 Γ3 Γ4 n (π1 , π2) | None = π1 , π2

      du21 : (n : Nat) → dom Γ2 n → n # Δ
      du21 n dom = ud1 n (dom-union2 Γ1  Γ2 n dom)

      du22 : (n : Nat) → dom Δ n → n # Γ2
      du22 n dom = apart-union-r Γ1 Γ2 n (ud2 n dom)

  
  -- if both parts of a union are disjoint with a target, so is the union
  disjoint-parts : {A : Set} {Γ1 Γ2 Γ3 : A ctx} →
                   Γ1 ## Γ3 →
                   Γ2 ## Γ3 →
                   (Γ1 ∪ Γ2) ## Γ3
  disjoint-parts {Γ1 = Γ1} {Γ2 = Γ2} {Γ3 = Γ3}
                 (disj13 , disj31) (disj23 , disj32) = disj∪3 , disj3∪
    where
      disj∪3 : (x : Nat) → dom (Γ1 ∪ Γ2) x → x # Γ3
      disj∪3 x (τ , x∈Γ1∪Γ2) with dom-union-part Γ1 Γ2 x τ x∈Γ1∪Γ2
      ... | Inl x∈Γ1 = disj13 x (τ , x∈Γ1)
      ... | Inr x∈Γ2 = disj23 x (τ , x∈Γ2)

      disj3∪ : (x : Nat) → dom Γ3 x → x # (Γ1 ∪ Γ2)
      disj3∪ x x∈Γ3 = apart-parts Γ1 Γ2 x (disj31 x x∈Γ3) (disj32 x x∈Γ3)
  

  disjoint-empty : {A : Set} {Γ : A ctx} →
                   Γ ## ∅
  disjoint-empty = (λ _ _ → refl) , (λ _ ())
