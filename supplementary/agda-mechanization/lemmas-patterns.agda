open import List
open import Prelude
open import constraints-core
open import contexts
open import core
open import dynamics-core
open import htyp-decidable
open import lemmas-contexts
open import lemmas-satisfy
open import patterns-core
open import result-judgements
open import statics-core

-- miscellaneous lemmas about patterns and rules
module lemmas-patterns where
  -- judgemental and functional pointer erasure align
  rel◆er : (rs : zrules) →
           erase-r rs (rs ◆er)
  rel◆er (nil / r / rs) = ERZPre
  rel◆er ((r' / rs') / r / rs) = ERNZPre (rel◆er (rs' / r / rs))

  -- rule erasure is unique
  erase-unicity : ∀{zrs rss rss'} →
                  erase-r zrs rss →
                  erase-r zrs rss' →
                  rss == rss'
  erase-unicity ERZPre ERZPre = refl
  erase-unicity (ERNZPre er) (ERNZPre er')
    with erase-unicity er er'
  ... | refl = refl
  
  -- the constraint emitted by a pattern has the same type
  pattern-constr-same-type : ∀{Δp p τ ξ Γ} →
                             Δp ⊢ p :: τ [ ξ ]⊣ Γ →
                             ξ :c: τ
  pattern-constr-same-type PTUnit = CTTruth
  pattern-constr-same-type PTVar = CTTruth
  pattern-constr-same-type PTNum = CTNum
  pattern-constr-same-type (PTInl pt) =
    CTInl (pattern-constr-same-type pt)
  pattern-constr-same-type (PTInr pt) =
    CTInr (pattern-constr-same-type pt)
  pattern-constr-same-type (PTPair disj pt1 pt2) =
    CTPair (pattern-constr-same-type pt1)
           (pattern-constr-same-type pt2)
  pattern-constr-same-type (PTEHole w∈Δp) = CTUnknown
  pattern-constr-same-type (PTHole w∈Δp pt) = CTUnknown
  pattern-constr-same-type PTWild = CTTruth

  -- the constraint emitted by a series of rules has the
  -- same type
  rules-constr-same-type : ∀{Δp rs τ ξ} →
                           Δp ⊢ rs ::s τ [ ξ ] →
                           ξ :c: τ
  rules-constr-same-type (RTOneRule pt) =
    pattern-constr-same-type pt
  rules-constr-same-type (RTRules pt rst) =
    CTOr (pattern-constr-same-type pt)
         (rules-constr-same-type rst)

  -- the constraint emitted by a series of rules has the
  -- same type, also tracking non-redundancy
  rules-constr-same-type-nonredundant : ∀{Δp rs τ ξpre ξ} →
                                        Δp ⊢ rs ::s τ [ ξpre nr/ ξ ] →
                                        ξ :c: τ
  rules-constr-same-type-nonredundant
    (RTOneRule pt ¬red) = pattern-constr-same-type pt
  rules-constr-same-type-nonredundant
    (RTRules pt ¬red rst) =
      CTOr (pattern-constr-same-type pt)
           (rules-constr-same-type-nonredundant rst)

  -- the contraint emitted by any pattern is possible, i.e.,
  -- every pattern is matchable by some expression
  pattern-constr-pos : ∀{Δp p τ ξ Γ} →
                       Δp ⊢ p :: τ [ ξ ]⊣ Γ →
                       ξ possible
  pattern-constr-pos PTUnit = PTruth
  pattern-constr-pos PTVar = PTruth
  pattern-constr-pos PTNum = PNum
  pattern-constr-pos (PTInl pt) =
    PInl (pattern-constr-pos pt)
  pattern-constr-pos (PTInr pt) =
    PInr (pattern-constr-pos pt)
  pattern-constr-pos (PTPair disj pt1 pt2) =
    PPair (pattern-constr-pos pt1)
          (pattern-constr-pos pt2)
  pattern-constr-pos (PTEHole w∈Δp) = PUnknown
  pattern-constr-pos (PTHole w∈Δp pt) = PUnknown
  pattern-constr-pos PTWild = PTruth

  -- refutable constraints are only emitted by refutable patterns
  constr-ref-pattern-ref : ∀{Δp p τ ξ Γ} →
                           Δp ⊢ p :: τ [ ξ ]⊣ Γ →
                           ξ xrefutable →
                           p refutable
  constr-ref-pattern-ref PTNum xref = RNum
  constr-ref-pattern-ref (PTInl pt) xref = RInl
  constr-ref-pattern-ref (PTInr pt) xref = RInr
  constr-ref-pattern-ref (PTPair disj pt1 pt2) (RXPairL xref1) =
    RPairL (constr-ref-pattern-ref pt1 xref1)
  constr-ref-pattern-ref (PTPair disj pt1 pt2) (RXPairR xref2) =
    RPairR (constr-ref-pattern-ref pt2 xref2)
  constr-ref-pattern-ref (PTEHole w∈Δp) xref = REHole
  constr-ref-pattern-ref (PTHole w∈Δp pt) xref = RHole

  -- refutable patterns emit refutable constraints
  pattern-ref-constr-ref : ∀{Δp p τ ξ Γ} →
                           Δp ⊢ p :: τ [ ξ ]⊣ Γ →
                           p refutable →
                           ξ xrefutable
  pattern-ref-constr-ref PTNum ref = RXNum
  pattern-ref-constr-ref (PTInl pt) ref = RXInl
  pattern-ref-constr-ref (PTInr pt) ref = RXInr
  pattern-ref-constr-ref (PTPair disj pt1 pt2) (RPairL ref1) =
    RXPairL (pattern-ref-constr-ref pt1 ref1)
  pattern-ref-constr-ref (PTPair disj pt1 pt2) (RPairR ref2) =
    RXPairR (pattern-ref-constr-ref pt2 ref2)
  pattern-ref-constr-ref (PTEHole w∈Δp) ref = RXUnknown
  pattern-ref-constr-ref (PTHole w∈Δp pt) ref = RXUnknown

  -- the different rule typing judgement behave as expected
  rules-type-no-target : ∀{Γ Δ Δp rs τ ξ τ'} →
                         Γ , Δ , Δp ⊢ rs ::s τ [ ξ ]=> τ' →
                         Δp ⊢ rs ::s τ [ ξ ]
  rules-type-no-target {rs = (p => e) / nil}
                       (RTOneRule (RTRule pt Γ##Γp wt')) =
    RTOneRule pt
  rules-type-no-target (RTRules (RTRule pt Γ##Γp wt') rst) =
    RTRules pt (rules-type-no-target rst)

  -- we can weaken the non-redundancy assumption
  -- to something which strictly entails ξpre
  weaken-nonredundant : ∀{Δp rs τ ξpre ξpre' ξ} →
                        ξpre :c: τ →
                        Δp ⊢ rs ::s τ [ ξpre nr/ ξ ] →
                        (∀{Δ Δp e} →
                         ∅ , Δ , Δp ⊢ e :: τ →
                         e val →
                         e ⊧̇ ξpre' →
                         e ⊧̇ ξpre) →
                        Δp ⊢ rs ::s τ [ ξpre' nr/ ξ ]
  weaken-nonredundant ctpre (RTOneRule pt ¬ent) ent' =
    RTOneRule pt (λ ent → ¬ent (entails-trans ent ctpre ent'))
  weaken-nonredundant {τ = τ} {ξpre = ξpre} {ξpre' = ξpre'}
                      ctpre (RTRules {ξr = ξr} pt ¬ent rst) ent' =
    RTRules pt (λ ent → ¬ent (entails-trans ent ctpre ent'))
            (weaken-nonredundant
              (CTOr ctpre (pattern-constr-same-type pt))
              rst
              entor)
    where
      entor : ∀{Δ Δp e} →
              ∅ , Δ , Δp ⊢ e :: τ →
              e val →
              e ⊧̇ (ξpre' ∨ ξr) →
              e ⊧̇ (ξpre ∨ ξr)
      entor wt val (CSOrL satpre') =
        CSOrL (ent' wt val satpre')
      entor wt val (CSOrR satr) = CSOrR satr
      
  notintro-mat-ref-not : ∀{e τ p θ} →
                         e notintro →
                         e ·: τ ▹ p ⊣ θ →
                         p refutable →
                         ⊥
  notintro-mat-ref-not NVAp (MNotIntroPair ni mat1 mat2)
                       (RPairL ref) =
    notintro-mat-ref-not NVFst mat1 ref
  notintro-mat-ref-not NVAp (MNotIntroPair ni mat1 mat2)
                       (RPairR ref) =
    notintro-mat-ref-not NVSnd mat2 ref
  notintro-mat-ref-not NVMatch (MNotIntroPair ni mat1 mat2)
                       (RPairL ref) =
    notintro-mat-ref-not NVFst mat1 ref
  notintro-mat-ref-not NVMatch (MNotIntroPair ni mat1 mat2)
                       (RPairR ref) =
    notintro-mat-ref-not NVSnd mat2 ref
  notintro-mat-ref-not NVFst (MNotIntroPair ni mat1 mat2)
                       (RPairL ref) =
    notintro-mat-ref-not NVFst mat1 ref
  notintro-mat-ref-not NVFst (MNotIntroPair ni mat1 mat2)
                       (RPairR ref) =
    notintro-mat-ref-not NVSnd mat2 ref
  notintro-mat-ref-not NVSnd (MNotIntroPair ni mat1 mat2)
                       (RPairL ref) =
    notintro-mat-ref-not NVFst mat1 ref
  notintro-mat-ref-not NVSnd (MNotIntroPair ni mat1 mat2)
                       (RPairR ref) =
    notintro-mat-ref-not NVSnd mat2 ref
  notintro-mat-ref-not NVEHole (MNotIntroPair ni mat1 mat2)
                       (RPairL ref) =
    notintro-mat-ref-not NVFst mat1 ref
  notintro-mat-ref-not NVEHole (MNotIntroPair ni mat1 mat2)
                       (RPairR ref) =
    notintro-mat-ref-not NVSnd mat2 ref
  notintro-mat-ref-not NVHole (MNotIntroPair ni mat1 mat2)
                       (RPairL ref) =
    notintro-mat-ref-not NVFst mat1 ref
  notintro-mat-ref-not NVHole (MNotIntroPair ni mat1 mat2)
                       (RPairR ref) =
    notintro-mat-ref-not NVSnd mat2 ref
                        
  
