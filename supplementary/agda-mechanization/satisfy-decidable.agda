open import Bool
open import Nat
open import Prelude
open import constraints-core
open import core
open import notintro-decidable
open import possible-decidable
open import value-judgements
open import xrefutable-decidable

module satisfy-decidable where
  -- satisfy function as in the paper
  satisfy-bool : ihexp → constr → Bool
  satisfy-bool e ·⊤ = true
  satisfy-bool e ·⊥ = false
  satisfy-bool (N n1) (N n2) with nat-dec n1 n2
  ... | Inl _ = true
  ... | Inr _ = false
  satisfy-bool (inl τ e) (inl ξ) = satisfy-bool e ξ
  satisfy-bool (inr τ e) (inr ξ) = satisfy-bool e ξ
  satisfy-bool (e1 ∘ e2) ⟨ ξ1 , ξ2 ⟩ =
    satisfy-bool (fst (e1 ∘ e2)) ξ1 and
      satisfy-bool (snd (e1 ∘ e2)) ξ2
  satisfy-bool ⟨ e1 , e2 ⟩ ⟨ ξ1 , ξ2 ⟩ =
    satisfy-bool e1 ξ1 and satisfy-bool e2 ξ2
  satisfy-bool (fst e) ⟨ ξ1 , ξ2 ⟩ =
    satisfy-bool (fst (fst e)) ξ1 and
      satisfy-bool (snd (fst e)) ξ2
  satisfy-bool (snd e) ⟨ ξ1 , ξ2 ⟩ =
    satisfy-bool (fst (snd e)) ξ1 and
      satisfy-bool (snd (snd e)) ξ2
  satisfy-bool (match e ·: τ of rs) ⟨ ξ1 , ξ2 ⟩ =
    satisfy-bool (fst (match e ·: τ of rs)) ξ1 and
      satisfy-bool (snd (match e ·: τ of rs)) ξ2
  satisfy-bool ⦇-⦈⟨ u , σ ⟩ ⟨ ξ1 , ξ2 ⟩ =
    satisfy-bool (fst ⦇-⦈⟨ u , σ ⟩) ξ1 and
      satisfy-bool (snd ⦇-⦈⟨ u , σ ⟩) ξ2
  satisfy-bool ⦇⌜ e ⌟⦈⟨ u , σ ⟩ ⟨ ξ1 , ξ2 ⟩ =
    satisfy-bool (fst ⦇⌜ e ⌟⦈⟨ u , σ ⟩) ξ1 and
      satisfy-bool (snd ⦇⌜ e ⌟⦈⟨ u , σ ⟩) ξ2
  satisfy-bool e (ξ1 ∨ ξ2) =
    satisfy-bool e ξ1 or satisfy-bool e ξ2
  -- otherwise,
  -- satisfy-bool e ξ = false.
  -- we expand things out so that all clauses hold definitionally
  satisfy-bool e ·? = false
  satisfy-bool unit (N n) = false
  satisfy-bool (X x) (N n) = false
  satisfy-bool (·λ x ·[ τ ] e) (N n) = false
  satisfy-bool (e1 ∘ e2) (N n) = false
  satisfy-bool (inl τ e) (N n) = false
  satisfy-bool (inr τ e) (N n) = false
  satisfy-bool ⟨ e1 , e2 ⟩ (N n) = false
  satisfy-bool (fst e) (N n) = false
  satisfy-bool (snd e) (N n) = false
  satisfy-bool (match e ·: τ of rs) (N n) = false
  satisfy-bool ⦇-⦈⟨ u , σ ⟩ (N n) = false
  satisfy-bool ⦇⌜ e ⌟⦈⟨ u , σ ⟩ (N n) = false
  satisfy-bool unit (inl ξ) = false
  satisfy-bool (N n) (inl ξ) = false
  satisfy-bool (X x) (inl ξ) = false
  satisfy-bool (·λ x ·[ τ ] e) (inl ξ) = false
  satisfy-bool (e1 ∘ e2) (inl ξ) = false
  satisfy-bool (inr τ e) (inl ξ) = false
  satisfy-bool ⟨ e1 , e2 ⟩ (inl ξ) = false
  satisfy-bool (fst e) (inl ξ) = false
  satisfy-bool (snd e) (inl ξ) = false
  satisfy-bool (match e ·: τ of x) (inl ξ) = false
  satisfy-bool ⦇-⦈⟨ u , σ ⟩ (inl ξ) = false
  satisfy-bool ⦇⌜ e ⌟⦈⟨ u , σ ⟩ (inl ξ) = false
  satisfy-bool unit (inr ξ) = false
  satisfy-bool (N n) (inr ξ) = false
  satisfy-bool (X x) (inr ξ) = false
  satisfy-bool (·λ x ·[ τ ] e) (inr ξ) = false
  satisfy-bool (e1 ∘ e2) (inr ξ) = false
  satisfy-bool (inl τ e) (inr ξ) = false
  satisfy-bool ⟨ e1 , e2 ⟩ (inr ξ) = false
  satisfy-bool (fst e) (inr ξ) = false
  satisfy-bool (snd e) (inr ξ) = false
  satisfy-bool (match e ·: τ of rs) (inr ξ) = false
  satisfy-bool ⦇-⦈⟨ u , σ ⟩ (inr ξ) = false
  satisfy-bool ⦇⌜ e ⌟⦈⟨ u , σ ⟩ (inr ξ) = false
  satisfy-bool unit ⟨ ξ1 , ξ2 ⟩ = false
  satisfy-bool (N n) ⟨ ξ1 , ξ2 ⟩ = false
  satisfy-bool (X x) ⟨ ξ1 , ξ2 ⟩ = false
  satisfy-bool (·λ x ·[ τ ] e) ⟨ ξ1 , ξ2 ⟩ = false
  satisfy-bool (inl τ e) ⟨ ξ1 , ξ2 ⟩ = false
  satisfy-bool (inr τ e) ⟨ ξ1 , ξ2 ⟩ = false

  -- soundness of satisfy function
  satisfy-sound : ∀{e ξ} →
                  e ⊧̇ ξ →
                  satisfy-bool e ξ == true
  satisfy-sound CSTruth = refl
  satisfy-sound (CSNum {n = n}) with nat-dec n n
  ... | Inl refl = refl
  ... | Inr neq = abort (neq refl)
  satisfy-sound (CSInl sat) = satisfy-sound sat
  satisfy-sound (CSInr sat) = satisfy-sound sat
  satisfy-sound (CSPair sat1 sat2) =
    and-true (satisfy-sound sat1) (satisfy-sound sat2)
  satisfy-sound {e = e1 ∘ e2} (CSNotIntroPair ni sat1 sat2) =
    and-true (satisfy-sound sat1) (satisfy-sound sat2)
  satisfy-sound {e = match e ·: τ of rs} (CSNotIntroPair ni sat1 sat2) =
    and-true (satisfy-sound sat1) (satisfy-sound sat2)
  satisfy-sound {e = fst e} (CSNotIntroPair ni sat1 sat2) =
    and-true (satisfy-sound sat1) (satisfy-sound sat2)
  satisfy-sound {e = snd e} (CSNotIntroPair ni sat1 sat2) =
    and-true (satisfy-sound sat1) (satisfy-sound sat2)
  satisfy-sound {e = ⦇-⦈⟨ u , σ ⟩} (CSNotIntroPair ni sat1 sat2) =
    and-true (satisfy-sound sat1) (satisfy-sound sat2)
  satisfy-sound {e = ⦇⌜ e ⌟⦈⟨ u , σ ⟩} (CSNotIntroPair ni sat1 sat2) =
    and-true (satisfy-sound sat1) (satisfy-sound sat2)
  satisfy-sound {e = e} {ξ = ξ1 ∨ ξ2} (CSOrL sat) =
    or-true-l {Q = satisfy-bool e ξ2} (satisfy-sound sat)
  satisfy-sound {e = e} {ξ = ξ1 ∨ ξ2} (CSOrR sat) =
    or-true-r {P = satisfy-bool e ξ1} (satisfy-sound sat)

  -- completeness of satisfy function
  satisfy-complete : ∀{e ξ} →
                     satisfy-bool e ξ == true →
                     e ⊧̇ ξ
  satisfy-complete {ξ = ·⊤} sateq = CSTruth
  satisfy-complete {e = N n1} {ξ = N n2} sateq
    with nat-dec n1 n2
  ... | Inl refl = CSNum
  ... | Inr neq with sateq
  ... | ()
  satisfy-complete {e = inl τ e} {ξ = inl ξ} sateq =
    CSInl (satisfy-complete sateq)
  satisfy-complete {e = inr τ e} {ξ = inr ξ} sateq =
    CSInr (satisfy-complete sateq)
  satisfy-complete {e = e1 ∘ e2} {ξ = ⟨ ξ1 , ξ2 ⟩} sateq
    with true-and sateq
  ... | sat1 , sat2 =
    CSNotIntroPair NVAp (satisfy-complete sat1)
                   (satisfy-complete sat2)
  satisfy-complete {e = match e ·: τ of rs} {ξ = ⟨ ξ1 , ξ2 ⟩} sateq
    with true-and sateq
  ... | sat1 , sat2 =
    CSNotIntroPair NVMatch (satisfy-complete sat1)
                   (satisfy-complete sat2)
  satisfy-complete {e = ⟨ e1 , e2 ⟩} {ξ = ⟨ ξ1 , ξ2 ⟩} sateq
    with true-and sateq
  ... | sat1 , sat2 =
    CSPair (satisfy-complete sat1) (satisfy-complete sat2)
  satisfy-complete {e = fst e} {ξ = ⟨ ξ1 , ξ2 ⟩} sateq
    with true-and sateq
  ... | sat1 , sat2 =
    CSNotIntroPair NVFst (satisfy-complete sat1)
                   (satisfy-complete sat2)
  satisfy-complete {e = snd e} {ξ = ⟨ ξ1 , ξ2 ⟩} sateq
    with true-and sateq
  ... | sat1 , sat2 =
    CSNotIntroPair NVSnd (satisfy-complete sat1)
                   (satisfy-complete sat2)
  satisfy-complete {e = ⦇-⦈⟨ u , σ ⟩} {ξ = ⟨ ξ1 , ξ2 ⟩} sateq
    with true-and sateq
  ... | sat1 , sat2 =
    CSNotIntroPair NVEHole (satisfy-complete sat1) (satisfy-complete sat2)
  satisfy-complete {e = ⦇⌜ e ⌟⦈⟨ u , σ ⟩} {ξ = ⟨ ξ1 , ξ2 ⟩} sateq
    with true-and sateq
  ... | sat1 , sat2 =
    CSNotIntroPair NVHole (satisfy-complete sat1)
                   (satisfy-complete sat2)
  satisfy-complete {ξ = ξ1 ∨ ξ2} sateq
    with true-or sateq
  ... | Inl sat1 = CSOrL (satisfy-complete sat1)
  ... | Inr sat2 = CSOrR (satisfy-complete sat2)

  -- combination of the above to explicitly show
  -- that the satisfy judgement is decidable
  satisfy-dec : (e : ihexp) →
                (ξ : constr) →
                (e ⊧̇ ξ) + (e ⊧̇ ξ → ⊥)
  satisfy-dec e ξ with satisfy-bool e ξ in eq
  ... | false = Inr (λ sat → false-neq-true eq (satisfy-sound sat))
  ... | true = Inl (satisfy-complete eq)
  
  -- maysatisfy function as in the paper
  maysatisfy-bool : (e : ihexp) → (ξ : constr) → Bool
  maysatisfy-bool e ·? = true
  maysatisfy-bool e ·⊥ = false
  maysatisfy-bool (inl τ e) (inl ξ) = maysatisfy-bool e ξ
  maysatisfy-bool (inr τ e) (inr ξ) = maysatisfy-bool e ξ
  maysatisfy-bool ⟨ e1 , e2 ⟩ ⟨ ξ1 , ξ2 ⟩ =
    (maysatisfy-bool e1 ξ1 and satisfy-bool e2 ξ2) or
    (satisfy-bool e1 ξ1 and maysatisfy-bool e2 ξ2) or
    (maysatisfy-bool e1 ξ1 and maysatisfy-bool e2 ξ2)
  maysatisfy-bool e (ξ1 ∨ ξ2) =
    (maysatisfy-bool e ξ1 and not (satisfy-bool e ξ2)) or
    (not (satisfy-bool e ξ1) and (maysatisfy-bool e ξ2))
  -- otherwise,
  -- maysatisfy-bool e ξ = notintro-bool e and
  --                         possible-bool ξ and xrefutable-bool ξ
  -- we expand things out so that all clasues hold definitionally
  maysatisfy-bool e ·⊤ =
    notintro-bool e and
      possible-bool ·⊤ and xrefutable-bool ·⊤
  maysatisfy-bool e (N n) =
    notintro-bool e and
      possible-bool (N n) and xrefutable-bool (N n)
  maysatisfy-bool unit (inl ξ) =
    notintro-bool unit and
      possible-bool (inl ξ) and xrefutable-bool (inl ξ)
  maysatisfy-bool (N n) (inl ξ) =
    notintro-bool (N n) and
      possible-bool (inl ξ) and xrefutable-bool (inl ξ)
  maysatisfy-bool (X x) (inl ξ) =
    notintro-bool (X x) and
      possible-bool (inl ξ) and xrefutable-bool (inl ξ)
  maysatisfy-bool (·λ x ·[ τ ] e) (inl ξ) =
    notintro-bool ((·λ x ·[ τ ] e)) and
      possible-bool (inl ξ) and xrefutable-bool (inl ξ)
  maysatisfy-bool (e1 ∘ e2) (inl ξ) =
    notintro-bool (e1 ∘ e2) and
      possible-bool (inl ξ) and xrefutable-bool (inl ξ)
  maysatisfy-bool (inr τ e) (inl ξ) =
    notintro-bool (inr τ e) and
      possible-bool (inl ξ) and xrefutable-bool (inl ξ)
  maysatisfy-bool ⟨ e1 , e2 ⟩ (inl ξ) =
    notintro-bool ⟨ e1 , e2 ⟩ and
      possible-bool (inl ξ) and xrefutable-bool (inl ξ)
  maysatisfy-bool (fst e) (inl ξ) =
    notintro-bool (fst e) and
      possible-bool (inl ξ) and xrefutable-bool (inl ξ)
  maysatisfy-bool (snd e) (inl ξ) =
    notintro-bool (snd e) and
      possible-bool (inl ξ) and xrefutable-bool (inl ξ)
  maysatisfy-bool (match e ·: τ of rs) (inl ξ) =
    notintro-bool (match e ·: τ of rs) and
      possible-bool (inl ξ) and xrefutable-bool (inl ξ)
  maysatisfy-bool ⦇-⦈⟨ u , σ ⟩ (inl ξ) =
    notintro-bool ⦇-⦈⟨ u , σ ⟩ and
      possible-bool (inl ξ) and xrefutable-bool (inl ξ)
  maysatisfy-bool ⦇⌜ e ⌟⦈⟨ u , σ ⟩ (inl ξ) =
    notintro-bool ⦇⌜ e ⌟⦈⟨ u , σ ⟩ and
      possible-bool (inl ξ) and xrefutable-bool (inl ξ)
  maysatisfy-bool unit (inr ξ) =
    notintro-bool unit and
      possible-bool (inr ξ) and xrefutable-bool (inr ξ)
  maysatisfy-bool (N n) (inr ξ) =
    notintro-bool (N n) and
      possible-bool (inr ξ) and xrefutable-bool (inr ξ)
  maysatisfy-bool (X x) (inr ξ) =
    notintro-bool (X x) and
      possible-bool (inr ξ) and xrefutable-bool (inr ξ)
  maysatisfy-bool (·λ x ·[ τ ] e) (inr ξ) =
    notintro-bool (·λ x ·[ τ ] e) and
      possible-bool (inr ξ) and xrefutable-bool (inr ξ)
  maysatisfy-bool (e1 ∘ e2) (inr ξ) =
    notintro-bool (e1 ∘ e2) and
      possible-bool (inr ξ) and xrefutable-bool (inr ξ)
  maysatisfy-bool (inl τ e) (inr ξ) =
    notintro-bool (inl τ e) and
      possible-bool (inr ξ) and xrefutable-bool (inr ξ)
  maysatisfy-bool ⟨ e1 , e2 ⟩ (inr ξ) =
    notintro-bool ⟨ e1 , e2 ⟩ and
      possible-bool (inr ξ) and xrefutable-bool (inr ξ)
  maysatisfy-bool (fst e) (inr ξ) =
    notintro-bool (fst e) and
      possible-bool (inr ξ) and xrefutable-bool (inr ξ)
  maysatisfy-bool (snd e) (inr ξ) =
    notintro-bool (snd e) and
      possible-bool (inr ξ) and xrefutable-bool (inr ξ)
  maysatisfy-bool (match e ·: τ of rs) (inr ξ) =
    notintro-bool (match e ·: τ of rs) and
      possible-bool (inr ξ) and xrefutable-bool (inr ξ)
  maysatisfy-bool ⦇-⦈⟨ u , σ ⟩ (inr ξ) =
    notintro-bool ⦇-⦈⟨ u , σ ⟩ and
      possible-bool (inr ξ) and xrefutable-bool (inr ξ)
  maysatisfy-bool ⦇⌜ e ⌟⦈⟨ u , σ ⟩ (inr ξ) =
    notintro-bool ⦇⌜ e ⌟⦈⟨ u , σ ⟩ and
      possible-bool (inr ξ) and xrefutable-bool (inr ξ)
  maysatisfy-bool unit ⟨ ξ1 , ξ2 ⟩ =
    notintro-bool unit and
      possible-bool ⟨ ξ1 , ξ2 ⟩ and xrefutable-bool ⟨ ξ1 , ξ2 ⟩
  maysatisfy-bool (N n) ⟨ ξ1 , ξ2 ⟩ =
    notintro-bool (N n) and
      possible-bool ⟨ ξ1 , ξ2 ⟩ and xrefutable-bool ⟨ ξ1 , ξ2 ⟩
  maysatisfy-bool (X x) ⟨ ξ1 , ξ2 ⟩ =
    notintro-bool (X x) and
      possible-bool ⟨ ξ1 , ξ2 ⟩ and xrefutable-bool ⟨ ξ1 , ξ2 ⟩
  maysatisfy-bool (·λ x ·[ τ ] e) ⟨ ξ1 , ξ2 ⟩ =
    notintro-bool (·λ x ·[ τ ] e) and
      possible-bool ⟨ ξ1 , ξ2 ⟩ and xrefutable-bool ⟨ ξ1 , ξ2 ⟩
  maysatisfy-bool (e1 ∘ e2) ⟨ ξ1 , ξ2 ⟩ =
    notintro-bool (e1 ∘ e2) and
      possible-bool ⟨ ξ1 , ξ2 ⟩ and xrefutable-bool ⟨ ξ1 , ξ2 ⟩
  maysatisfy-bool (inl τ e) ⟨ ξ1 , ξ2 ⟩ =
    notintro-bool (inl τ e) and
      possible-bool ⟨ ξ1 , ξ2 ⟩ and xrefutable-bool ⟨ ξ1 , ξ2 ⟩
  maysatisfy-bool (inr τ e) ⟨ ξ1 , ξ2 ⟩ =
    notintro-bool (inr τ e) and
      possible-bool ⟨ ξ1 , ξ2 ⟩ and xrefutable-bool ⟨ ξ1 , ξ2 ⟩
  maysatisfy-bool (fst e) ⟨ ξ1 , ξ2 ⟩ =
    notintro-bool (fst e) and
      possible-bool ⟨ ξ1 , ξ2 ⟩ and xrefutable-bool ⟨ ξ1 , ξ2 ⟩
  maysatisfy-bool (snd e) ⟨ ξ1 , ξ2 ⟩ =
    notintro-bool (snd e) and
      possible-bool ⟨ ξ1 , ξ2 ⟩ and xrefutable-bool ⟨ ξ1 , ξ2 ⟩
  maysatisfy-bool (match e ·: τ of rs) ⟨ ξ1 , ξ2 ⟩ =
    notintro-bool (match e ·: τ of rs) and
      possible-bool ⟨ ξ1 , ξ2 ⟩ and xrefutable-bool ⟨ ξ1 , ξ2 ⟩
  maysatisfy-bool ⦇-⦈⟨ u , σ ⟩ ⟨ ξ1 , ξ2 ⟩ =
    notintro-bool ⦇-⦈⟨ u , σ ⟩ and
      possible-bool ⟨ ξ1 , ξ2 ⟩ and xrefutable-bool ⟨ ξ1 , ξ2 ⟩
  maysatisfy-bool ⦇⌜ e ⌟⦈⟨ u , σ ⟩ ⟨ ξ1 , ξ2 ⟩ =
    notintro-bool ⦇⌜ e ⌟⦈⟨ u , σ ⟩ and
      possible-bool ⟨ ξ1 , ξ2 ⟩ and xrefutable-bool ⟨ ξ1 , ξ2 ⟩
  
  -- lemma needed for a few cases
  not-ref-lem : ∀{e ξ} →
                e notintro →
                e ⊧̇ ξ →
                ξ xrefutable →
                ⊥
  not-ref-lem ni (CSNotIntroPair ni' sat1 sat2) (RXPairL ref1) =
    not-ref-lem NVFst sat1 ref1
  not-ref-lem ni (CSNotIntroPair ni' sat1 sat2) (RXPairR ref2) =
    not-ref-lem NVSnd sat2 ref2
  not-ref-lem ni (CSOrL sat1) (RXOr ref1 ref2) =
    not-ref-lem ni sat1 ref1
  not-ref-lem ni (CSOrR sat2) (RXOr ref1 ref2) =
    not-ref-lem ni sat2 ref2
    
  -- soundness of maysatisfy function
  maysatisfy-sound : ∀{e ξ} →
                     e ⊧̇? ξ →
                     maysatisfy-bool e ξ == true
  maysatisfy-sound CMSUnknown = refl
  maysatisfy-sound (CMSInl msat) = maysatisfy-sound msat
  maysatisfy-sound (CMSInr msat) = maysatisfy-sound msat
  maysatisfy-sound {e = ⟨ e1 , e2 ⟩} {ξ = ⟨ ξ1 , ξ2 ⟩}
                   (CMSPairL msat1 sat2) = 
    or-true-l {Q = (satisfy-bool e1 ξ1 and maysatisfy-bool e2 ξ2) or
                   (maysatisfy-bool e1 ξ1 and maysatisfy-bool e2 ξ2)}
              (and-true (maysatisfy-sound msat1) (satisfy-sound sat2))
  maysatisfy-sound {e = ⟨ e1 , e2 ⟩} {ξ = ⟨ ξ1 , ξ2 ⟩}
                   (CMSPairR sat1 msat2) =
    or-true-r {P = maysatisfy-bool e1 ξ1 and satisfy-bool e2 ξ2}
              (or-true-l {Q = maysatisfy-bool e1 ξ1 and
                              maysatisfy-bool e2 ξ2}
                         (and-true (satisfy-sound sat1)
                                   (maysatisfy-sound msat2)))
  maysatisfy-sound {e = ⟨ e1 , e2 ⟩} {ξ = ⟨ ξ1 , ξ2 ⟩}
                   (CMSPair msat1 msat2) =
    or-true-r {P = maysatisfy-bool e1 ξ1 and satisfy-bool e2 ξ2}
              (or-true-r {P = satisfy-bool e1 ξ1 and maysatisfy-bool e2 ξ2}
                         (and-true (maysatisfy-sound msat1)
                                   (maysatisfy-sound msat2)))
  maysatisfy-sound (CMSOrL msat1 ¬sat2) =
    or-true-l (and-true
                (maysatisfy-sound msat1)
                (false-not-true
                  (neq-true-false
                    (λ sat2 → ¬sat2 (satisfy-complete sat2)))))
  maysatisfy-sound (CMSOrR ¬sat1 msat2) =
    or-true-r (and-true
                (false-not-true
                  (neq-true-false
                    (λ sat1 → ¬sat1 (satisfy-complete sat1))))
                (maysatisfy-sound msat2))
  maysatisfy-sound {ξ = ·?} (CMSNotIntro ni ref pos) = refl
  maysatisfy-sound {e = e} {ξ = N n}
                   (CMSNotIntro ni ref pos) =
    and-true (notintro-sound ni) refl
  maysatisfy-sound {e = e1 ∘ e2} {ξ = inl ξ}
                   (CMSNotIntro ni ref (PInl pos)) =
    and-true (possible-sound pos) refl
  maysatisfy-sound {e = match e ·: τ of rs} {ξ = inl ξ}
                   (CMSNotIntro ni ref (PInl pos)) =
    and-true (possible-sound pos) refl
  maysatisfy-sound {e = fst e} {ξ = inl ξ}
                   (CMSNotIntro ni ref (PInl pos)) =
    and-true (possible-sound pos) refl
  maysatisfy-sound {e = snd e} {ξ = inl ξ}
                   (CMSNotIntro ni ref (PInl pos)) =
    and-true (possible-sound pos) refl
  maysatisfy-sound {e = ⦇-⦈⟨ u , σ ⟩} {ξ = inl ξ}
                   (CMSNotIntro ni ref (PInl pos)) =
    and-true (possible-sound pos) refl
  maysatisfy-sound {e = ⦇⌜ e ⌟⦈⟨ u , σ ⟩} {ξ = inl ξ}
                   (CMSNotIntro ni ref (PInl pos)) =
    and-true (possible-sound pos) refl
  maysatisfy-sound {e = e1 ∘ e2} {ξ = inr ξ}
                   (CMSNotIntro ni ref (PInr pos)) =
    and-true (possible-sound pos) refl
  maysatisfy-sound {e = match e ·: τ of rs} {ξ = inr ξ}
                   (CMSNotIntro ni ref (PInr pos)) =
    and-true (possible-sound pos) refl
  maysatisfy-sound {e = fst e} {ξ = inr ξ}
                   (CMSNotIntro ni ref (PInr pos)) =
    and-true (possible-sound pos) refl
  maysatisfy-sound {e = snd e} {ξ = inr ξ}
                   (CMSNotIntro ni ref (PInr pos)) =
    and-true (possible-sound pos) refl
  maysatisfy-sound {e = ⦇-⦈⟨ u , σ ⟩} {ξ = inr ξ}
                   (CMSNotIntro ni ref (PInr pos)) =
    and-true (possible-sound pos) refl
  maysatisfy-sound {e = ⦇⌜ e ⌟⦈⟨ u , σ ⟩} {ξ = inr ξ}
                   (CMSNotIntro ni ref (PInr pos)) =
    and-true (possible-sound pos) refl
  maysatisfy-sound {e = e1 ∘ e2} {ξ = ⟨ ξ1 , ξ2 ⟩}
                   (CMSNotIntro ni (RXPairL ref1) (PPair pos1 pos2)) =
    and-true (and-true (possible-sound pos1) (possible-sound pos2))
             (or-true-l (xrefutable-sound ref1))
  maysatisfy-sound {e = match e ·: τ of rs} {ξ = ⟨ ξ1 , ξ2 ⟩}
                   (CMSNotIntro ni (RXPairL ref1) (PPair pos1 pos2)) =
    and-true (and-true (possible-sound pos1) (possible-sound pos2))
             (or-true-l (xrefutable-sound ref1))
  maysatisfy-sound {e = fst e} {ξ = ⟨ ξ1 , ξ2 ⟩}
                   (CMSNotIntro ni (RXPairL ref1) (PPair pos1 pos2)) =
    and-true (and-true (possible-sound pos1) (possible-sound pos2))
             (or-true-l (xrefutable-sound ref1))
  maysatisfy-sound {e = snd e} {ξ = ⟨ ξ1 , ξ2 ⟩}
                   (CMSNotIntro ni (RXPairL ref1) (PPair pos1 pos2)) =
    and-true (and-true (possible-sound pos1) (possible-sound pos2))
             (or-true-l (xrefutable-sound ref1))
  maysatisfy-sound {e = ⦇-⦈⟨ u , σ ⟩} {ξ = ⟨ ξ1 , ξ2 ⟩}
                   (CMSNotIntro ni (RXPairL ref1) (PPair pos1 pos2)) =
    and-true (and-true (possible-sound pos1) (possible-sound pos2))
             (or-true-l (xrefutable-sound ref1))
  maysatisfy-sound {e = ⦇⌜ e ⌟⦈⟨ u , σ ⟩} {ξ = ⟨ ξ1 , ξ2 ⟩}
                   (CMSNotIntro ni (RXPairL ref1) (PPair pos1 pos2)) =
    and-true (and-true (possible-sound pos1) (possible-sound pos2))
             (or-true-l (xrefutable-sound ref1))
  maysatisfy-sound {e = e1 ∘ e2} {ξ = ⟨ ξ1 , ξ2 ⟩}
                   (CMSNotIntro ni (RXPairR ref2) (PPair pos1 pos2)) =
    and-true (and-true (possible-sound pos1) (possible-sound pos2))
             (or-true-r (xrefutable-sound ref2))
  maysatisfy-sound {e = match e ·: τ of rs} {ξ = ⟨ ξ1 , ξ2 ⟩}
                   (CMSNotIntro ni (RXPairR ref2) (PPair pos1 pos2)) =
    and-true (and-true (possible-sound pos1) (possible-sound pos2))
             (or-true-r (xrefutable-sound ref2))
  maysatisfy-sound {e = fst e} {ξ = ⟨ ξ1 , ξ2 ⟩}
                   (CMSNotIntro ni (RXPairR ref2) (PPair pos1 pos2)) =
    and-true (and-true (possible-sound pos1) (possible-sound pos2))
             (or-true-r (xrefutable-sound ref2))
  maysatisfy-sound {e = snd e} {ξ = ⟨ ξ1 , ξ2 ⟩}
                   (CMSNotIntro ni (RXPairR ref2) (PPair pos1 pos2)) =
    and-true (and-true (possible-sound pos1) (possible-sound pos2))
             (or-true-r (xrefutable-sound ref2))
  maysatisfy-sound {e = ⦇-⦈⟨ u , σ ⟩} {ξ = ⟨ ξ1 , ξ2 ⟩}
                   (CMSNotIntro ni (RXPairR ref2) (PPair pos1 pos2)) =
    and-true (and-true (possible-sound pos1) (possible-sound pos2))
             (or-true-r (xrefutable-sound ref2))
  maysatisfy-sound {e = ⦇⌜ e ⌟⦈⟨ u , σ ⟩} {ξ = ⟨ ξ1 , ξ2 ⟩}
                   (CMSNotIntro ni (RXPairR ref2) (PPair pos1 pos2)) =
    and-true (and-true (possible-sound pos1) (possible-sound pos2))
             (or-true-r (xrefutable-sound ref2))
  maysatisfy-sound {e = e} {ξ = ξ1 ∨ ξ2}
                   (CMSNotIntro ni (RXOr ref1 ref2) (POrL pos1)) =
    or-true-l
      (and-true (maysatisfy-sound msat1)
                (false-not-true
                  (neq-true-false
                    λ sat2 → ¬sat2 (satisfy-complete sat2))))
    where
      msat1 : e ⊧̇? ξ1
      msat1 = CMSNotIntro ni ref1 pos1
      ¬sat2 : e ⊧̇ ξ2 → ⊥
      ¬sat2 sat2 = not-ref-lem ni sat2 ref2
  maysatisfy-sound {e = e} {ξ = ξ1 ∨ ξ2}
    (CMSNotIntro ni (RXOr ref1 ref2) (POrR pos2)) =
    or-true-r
      (and-true (false-not-true
                  (neq-true-false
                    λ sat1 → ¬sat1 (satisfy-complete sat1)))
                (maysatisfy-sound msat2))
     where
      ¬sat1 : e ⊧̇ ξ1 → ⊥
      ¬sat1 sat1 = not-ref-lem ni sat1 ref1
      msat2 : e ⊧̇? ξ2
      msat2 = CMSNotIntro ni ref2 pos2
      
  -- completeness of satisfy function
  maysatisfy-complete : ∀{e ξ} →
                        maysatisfy-bool e ξ == true →
                        e ⊧̇? ξ
  maysatisfy-complete {e = e} {ξ = ·⊤} msateq
    with true-and {P = notintro-bool e} msateq
  ... | ni , ()
  maysatisfy-complete {ξ = ·?} msateq = CMSUnknown
  maysatisfy-complete {e = e} {ξ = N n} msateq
    with true-and {P = notintro-bool e} msateq
  ... | ni , refl = CMSNotIntro (notintro-complete ni) RXNum PNum
  maysatisfy-complete {e = e1 ∘ e2} {ξ = inl ξ} msateq
    with true-and {P = possible-bool ξ} msateq
  ... | pos , refl =
    CMSNotIntro NVAp RXInl (PInl (possible-complete pos))
  maysatisfy-complete {e = inl τ e} {ξ = inl ξ} msateq =
    CMSInl (maysatisfy-complete msateq)
  maysatisfy-complete {e = match e ·: τ of rs} {ξ = inl ξ} msateq
    with true-and {P = possible-bool ξ} msateq
  ... | pos , refl =
    CMSNotIntro NVMatch RXInl (PInl (possible-complete pos))
  maysatisfy-complete {e = fst e} {ξ = inl ξ} msateq
    with true-and {P = possible-bool ξ} msateq
  ... | pos , refl =
    CMSNotIntro NVFst RXInl (PInl (possible-complete pos))
  maysatisfy-complete {e = snd e} {ξ = inl ξ} msateq
    with true-and {P = possible-bool ξ} msateq
  ... | pos , refl =
    CMSNotIntro NVSnd RXInl (PInl (possible-complete pos))
  maysatisfy-complete {e = ⦇-⦈⟨ u , σ ⟩} {ξ = inl ξ} msateq
    with true-and {P = possible-bool ξ} msateq
  ... | pos , refl =
    CMSNotIntro NVEHole RXInl (PInl (possible-complete pos))
  maysatisfy-complete {e = ⦇⌜ e ⌟⦈⟨ u , σ ⟩} {ξ = inl ξ} msateq
    with true-and {P = possible-bool ξ} msateq
  ... | pos , refl =
    CMSNotIntro NVHole RXInl (PInl (possible-complete pos))
  maysatisfy-complete {e = e1 ∘ e2} {ξ = inr ξ} msateq
    with true-and {P = possible-bool ξ} msateq
  ... | pos , refl =
    CMSNotIntro NVAp RXInr (PInr (possible-complete pos))
  maysatisfy-complete {e = inr τ e} {ξ = inr ξ} msateq =
    CMSInr (maysatisfy-complete msateq)
  maysatisfy-complete {e = match e ·: τ of rs} {ξ = inr ξ} msateq
    with true-and {P = possible-bool ξ} msateq
  ... | pos , refl =
    CMSNotIntro NVMatch RXInr (PInr (possible-complete pos))
  maysatisfy-complete {e = fst e} {ξ = inr ξ} msateq
    with true-and {P = possible-bool ξ} msateq
  ... | pos , refl =
    CMSNotIntro NVFst RXInr (PInr (possible-complete pos))
  maysatisfy-complete {e = snd e} {ξ = inr ξ} msateq
    with true-and {P = possible-bool ξ} msateq
  ... | pos , refl =
    CMSNotIntro NVSnd RXInr (PInr (possible-complete pos))
  maysatisfy-complete {e = ⦇-⦈⟨ u , σ ⟩} {ξ = inr ξ} msateq
    with true-and {P = possible-bool ξ} msateq
  ... | pos , refl =
    CMSNotIntro NVEHole RXInr (PInr (possible-complete pos))
  maysatisfy-complete {e = ⦇⌜ e ⌟⦈⟨ u , σ ⟩} {ξ = inr ξ} msateq
    with true-and {P = possible-bool ξ} msateq
  ... | pos , refl =
    CMSNotIntro NVHole RXInr (PInr (possible-complete pos))
  maysatisfy-complete {e = e1 ∘ e2} {ξ = ⟨ ξ1 , ξ2 ⟩} msateq
    with true-and {P = possible-bool ξ1 and possible-bool ξ2}
                  {Q = xrefutable-bool ξ1 or xrefutable-bool ξ2} msateq
  ... | pos , ref with true-and {P = possible-bool ξ1} {Q = possible-bool ξ2} pos
  ... | pos1 , pos2 with true-or ref 
  ... | Inl ref1 =
    CMSNotIntro NVAp (RXPairL (xrefutable-complete ref1))
                (PPair (possible-complete pos1) (possible-complete pos2))
  ... | Inr ref2 =
    CMSNotIntro NVAp (RXPairR (xrefutable-complete ref2))
                (PPair (possible-complete pos1) (possible-complete pos2))
  maysatisfy-complete {e = match e ·: τ of rs} {ξ = ⟨ ξ1 , ξ2 ⟩} msateq
    with true-and {P = possible-bool ξ1 and possible-bool ξ2}
                  {Q = xrefutable-bool ξ1 or xrefutable-bool ξ2} msateq
  ... | pos , ref
    with true-and {P = possible-bool ξ1} {Q = possible-bool ξ2} pos
  ... | pos1 , pos2 with true-or ref 
  ... | Inl ref1 =
    CMSNotIntro NVMatch (RXPairL (xrefutable-complete ref1))
                (PPair (possible-complete pos1) (possible-complete pos2))
  ... | Inr ref2 =
    CMSNotIntro NVMatch (RXPairR (xrefutable-complete ref2))
                (PPair (possible-complete pos1) (possible-complete pos2))
  maysatisfy-complete {e = ⟨ e1 , e2 ⟩} {ξ = ⟨ ξ1 , ξ2 ⟩} msateq
    with true-or {P = maysatisfy-bool e1 ξ1 and satisfy-bool e2 ξ2}
                 {Q = satisfy-bool e1 ξ1 and maysatisfy-bool e2 ξ2 or
                      maysatisfy-bool e1 ξ1 and maysatisfy-bool e2 ξ2}
                 msateq
  ... | Inl tand
    with true-and {P = maysatisfy-bool e1 ξ1} {Q = satisfy-bool e2 ξ2} tand
  ... | msat1 , sat2 =
    CMSPairL (maysatisfy-complete msat1) (satisfy-complete sat2)
  maysatisfy-complete {e = ⟨ e1 , e2 ⟩} {ξ = ⟨ ξ1 , ξ2 ⟩} msateq |
    Inr tor
    with true-or {P = satisfy-bool e1 ξ1 and maysatisfy-bool e2 ξ2}
                 {Q = maysatisfy-bool e1 ξ1 and maysatisfy-bool e2 ξ2}
                 tor
  ... | Inl tand
    with true-and {P = satisfy-bool e1 ξ1} {Q = maysatisfy-bool e2 ξ2} tand
  ... | sat1 , msat2 =
    CMSPairR (satisfy-complete sat1) (maysatisfy-complete msat2)
  maysatisfy-complete {e = ⟨ e1 , e2 ⟩} {ξ = ⟨ ξ1 , ξ2 ⟩} msateq
      | Inr tor | Inr tand
    with true-and {P = maysatisfy-bool e1 ξ1}
                  {Q = maysatisfy-bool e2 ξ2} tand
  ... | msat1 , msat2 =
    CMSPair (maysatisfy-complete msat1) (maysatisfy-complete msat2) 
  maysatisfy-complete {e = fst e} {ξ = ⟨ ξ1 , ξ2 ⟩} msateq
    with true-and {P = possible-bool ξ1 and possible-bool ξ2}
                  {Q = xrefutable-bool ξ1 or xrefutable-bool ξ2} msateq
  ... | pos , ref
    with true-and {P = possible-bool ξ1} {Q = possible-bool ξ2} pos
  ... | pos1 , pos2 with true-or ref 
  ... | Inl ref1 =
    CMSNotIntro NVFst (RXPairL (xrefutable-complete ref1))
                (PPair (possible-complete pos1) (possible-complete pos2))
  ... | Inr ref2 =
    CMSNotIntro NVFst (RXPairR (xrefutable-complete ref2))
                (PPair (possible-complete pos1) (possible-complete pos2))
  maysatisfy-complete {e = snd e} {ξ = ⟨ ξ1 , ξ2 ⟩} msateq
    with true-and {P = possible-bool ξ1 and possible-bool ξ2}
                  {Q = xrefutable-bool ξ1 or xrefutable-bool ξ2} msateq
  ... | pos , ref
    with true-and {P = possible-bool ξ1} {Q = possible-bool ξ2} pos
  ... | pos1 , pos2
    with true-or ref 
  ... | Inl ref1 =
    CMSNotIntro NVSnd (RXPairL (xrefutable-complete ref1))
                (PPair (possible-complete pos1) (possible-complete pos2))
  ... | Inr ref2 =
    CMSNotIntro NVSnd (RXPairR (xrefutable-complete ref2))
                (PPair (possible-complete pos1) (possible-complete pos2))
  maysatisfy-complete {e = ⦇-⦈⟨ u , σ ⟩} {ξ = ⟨ ξ1 , ξ2 ⟩} msateq
    with true-and {P = possible-bool ξ1 and possible-bool ξ2}
                  {Q = xrefutable-bool ξ1 or xrefutable-bool ξ2} msateq
  ... | pos , ref
    with true-and {P = possible-bool ξ1} {Q = possible-bool ξ2} pos
  ... | pos1 , pos2 with true-or ref 
  ... | Inl ref1 =
    CMSNotIntro NVEHole (RXPairL (xrefutable-complete ref1))
                (PPair (possible-complete pos1) (possible-complete pos2))
  ... | Inr ref2 =
    CMSNotIntro NVEHole (RXPairR (xrefutable-complete ref2))
                (PPair (possible-complete pos1) (possible-complete pos2))
  maysatisfy-complete {e = ⦇⌜ e ⌟⦈⟨ u , σ ⟩} {ξ = ⟨ ξ1 , ξ2 ⟩} msateq
    with true-and {P = possible-bool ξ1 and possible-bool ξ2}
                  {Q = xrefutable-bool ξ1 or xrefutable-bool ξ2} msateq
  ... | pos , ref
    with true-and {P = possible-bool ξ1} {Q = possible-bool ξ2} pos
  ... | pos1 , pos2 with true-or ref 
  ... | Inl ref1 =
    CMSNotIntro NVHole (RXPairL (xrefutable-complete ref1))
                (PPair (possible-complete pos1) (possible-complete pos2))
  ... | Inr ref2 =
    CMSNotIntro NVHole (RXPairR (xrefutable-complete ref2))
                (PPair (possible-complete pos1) (possible-complete pos2))
  maysatisfy-complete {e = e} {ξ = ξ1 ∨ ξ2} msateq
    with true-or {P = maysatisfy-bool e ξ1 and not (satisfy-bool e ξ2)}
                 {Q = not (satisfy-bool e ξ1) and maysatisfy-bool e ξ2}
                 msateq
  ... | Inl tand with true-and {P = maysatisfy-bool e ξ1}
                               {Q = not (satisfy-bool e ξ2)} tand
  ... | msat1 , ¬sat2 =
    CMSOrL (maysatisfy-complete msat1)
           (λ sat2 → false-neq-true (not-true-false ¬sat2)
                                    (satisfy-sound sat2))
  maysatisfy-complete {e = e} {ξ = ξ1 ∨ ξ2} msateq | Inr tand
    with true-and {P = not (satisfy-bool e ξ1)}
                  {Q = maysatisfy-bool e ξ2} tand
  ... | ¬sat1 , msat2 =
    CMSOrR (λ sat1 → false-neq-true (not-true-false ¬sat1)
                                    (satisfy-sound sat1))
           (maysatisfy-complete msat2)
  
  -- combination of the above to explicitly show
  -- that the maysatisfy judgement is decidable
  maysatisfy-dec : (e : ihexp) →
                   (ξ : constr) →
                   (e ⊧̇? ξ) + (e ⊧̇? ξ → ⊥)
  maysatisfy-dec e ξ with maysatisfy-bool e ξ in eq
  ... | false = Inr (λ msat → false-neq-true eq (maysatisfy-sound msat))
  ... | true = Inl (maysatisfy-complete eq)

  -- satisfyormay function as in the paper
  satisfyormay-bool : ihexp → constr → Bool
  satisfyormay-bool e ξ = satisfy-bool e ξ or maysatisfy-bool e ξ
  
  -- soundness of satisfyormay function
  satisfyormay-sound : ∀{e ξ} →
                       e ⊧̇†? ξ →
                       satisfyormay-bool e ξ == true
  satisfyormay-sound (CSMSSat sat) = or-true-l (satisfy-sound sat)
  satisfyormay-sound (CSMSMay msat) = or-true-r (maysatisfy-sound msat)
  
  -- completeness of satisfyormay function
  satisfyormay-complete : ∀{e ξ} →
                          satisfyormay-bool e ξ == true →
                          e ⊧̇†? ξ
  satisfyormay-complete {e = e} {ξ = ξ} eq
    with true-or {P = satisfy-bool e ξ} {Q = maysatisfy-bool e ξ} eq
  ... | Inl sat = CSMSSat (satisfy-complete sat)
  ... | Inr msat = CSMSMay (maysatisfy-complete msat)
  
  -- combination of the above to explicitly show
  -- that the satisfyormay judgement is decidable
  satisfyormay-dec : (e : ihexp) →
                   (ξ : constr) →
                   (e ⊧̇†? ξ) + (e ⊧̇†? ξ → ⊥)
  satisfyormay-dec e ξ with satisfyormay-bool e ξ in eq
  ... | false = Inr (λ satm → false-neq-true eq (satisfyormay-sound satm))
  ... | true = Inl (satisfyormay-complete eq)
