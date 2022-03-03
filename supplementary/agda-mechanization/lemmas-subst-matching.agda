open import List
open import Nat
open import Prelude
open import constraints-core
open import contexts
open import core
open import dynamics-core
open import lemmas-satisfy
open import lemmas-subst-value
open import patterns-core
open import result-judgements
open import satisfy-decidable
open import statics-core

-- a given matching judgement still holds
-- after substituting a variable in the expression
module lemmas-subst-matching where
  subst-mat : ∀{x e1 e2 τ p θ1} →
              e1 ·: τ ▹ p ⊣ θ1 →
              Σ[ θ2 ∈ subst-list ] (([ e2 / x ] e1) ·: τ ▹ p ⊣ θ2)
  subst-mat MUnit = [] , MUnit
  subst-mat MNum = [] , MNum
  subst-mat {x = x} {e1 = e1} {e2 = e2} {τ = τ}
            (MVar {x = y}) =
    ([ e2 / x ] e1 , τ , y) :: [] , MVar
  subst-mat (MInl mat)
    with subst-mat mat
  ... | θ1 , smat = θ1 , MInl smat
  subst-mat (MInr mat)
    with subst-mat mat
  ... | θ1 , smat = θ1 , MInr smat
  subst-mat (MPair mat1 mat2)
    with subst-mat mat1 | subst-mat mat2
  ... | θ1 , smat1 | θ2 , smat2 =
    θ1 ++ θ2 , MPair smat1 smat2
  subst-mat (MNotIntroPair ni mat1 mat2)
    with subst-mat mat1 | subst-mat mat2
  ... | θ1 , smat1 | θ2 , smat2 =
    θ1 ++ θ2 ,
    MNotIntroPair (subst-notintro ni) smat1 smat2
  subst-mat MWild = [] , MWild
  
  subst-maymat : ∀{x e1 e2 τ p} →
                 e1 ·: τ ?▹ p →
                 ([ e2 / x ] e1) ·: τ ?▹ p
  subst-maymat (MMNotIntro ni ref) =
    MMNotIntro (subst-notintro ni) ref
  subst-maymat (MMInl mmat) =
    MMInl (subst-maymat mmat)
  subst-maymat (MMInr mmat) =
    MMInr (subst-maymat mmat)
  subst-maymat (MMPairL mmat1 mat2)
    with subst-mat mat2
  ... | θ2 , smat2 =
    MMPairL (subst-maymat mmat1) smat2
  subst-maymat (MMPairR mat1 mmat2)
    with subst-mat mat1
  ... | θ1 , smat1 =
    MMPairR smat1 (subst-maymat mmat2)
  subst-maymat (MMPair mmat1 mmat2) =
    MMPair (subst-maymat mmat1) (subst-maymat mmat2)
  subst-maymat MMEHole = MMEHole
  subst-maymat MMHole = MMHole
