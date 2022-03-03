open import Nat
open import Prelude
open import contexts
open import core
open import dynamics-core
open import matching-determinism
open import patterns-core
open import result-judgements
open import statics-core

-- final expressions are actually final, i.e.,
-- they cannot be evaluated further
module finality where
  final-step-not : ∀{e e'} →
                   e final →
                   e ↦ e' →
                   ⊥
  final-step-not (FVal (VInl eval)) (ITInl stp) =
    final-step-not (FVal eval) stp
  final-step-not (FVal (VInr eval)) (ITInr stp) =
    final-step-not (FVal eval) stp
  final-step-not (FVal (VPair eval1 eval2))
                 (ITPairL stp) =
    final-step-not (FVal eval1) stp
  final-step-not (FVal (VPair eval1 eval2))
                 (ITPairR eval1₁ stp) =
    final-step-not (FVal eval2) stp
  final-step-not (FIndet (IAp ind1 fin2))
                 (ITpFun stp) =
    final-step-not (FIndet ind1) stp
  final-step-not (FIndet (IAp ind1 fin2))
                 (ITpArg eval1 stp) =
    final-step-not fin2 stp
  final-step-not (FIndet (IAp () fin2))
                 (ITp fin)
  final-step-not (FIndet (IInl ind)) (ITInl stp) =
    final-step-not (FIndet ind) stp
  final-step-not (FIndet (IInr ind)) (ITInr stp) =
    final-step-not (FIndet ind) stp
  final-step-not (FIndet (IMatch fin mmat))
                 (ITExpMatch stp) =
    final-step-not fin stp
  final-step-not (FIndet (IMatch fin mmat))
                 (ITSuccMatch fin₁ mat) =
    mat-maymat-not mat mmat
  final-step-not (FIndet (IMatch fin mmat))
                 (ITFailMatch fin₁ nmat er) =
    maymat-notmat-not mmat nmat
  final-step-not (FIndet (IPairL ind1 val2))
                 (ITPairL stp) =
    final-step-not (FIndet ind1) stp
  final-step-not (FIndet (IPairL ind1 val2))
                 (ITPairR eval1 stp) =
    final-step-not (FVal val2) stp
  final-step-not (FIndet (IPairR val1 ind2))
                 (ITPairL stp) =
    final-step-not (FVal val1) stp
  final-step-not (FIndet (IPairR val1 ind2))
                 (ITPairR eval1 stp) =
    final-step-not (FIndet ind2) stp
  final-step-not (FIndet (IPair ind1 ind2))
                 (ITPairL stp) =
    final-step-not (FIndet ind1) stp
  final-step-not (FIndet (IPair ind1 ind2))
                 (ITPairR eval1 stp) =
    final-step-not (FIndet ind2) stp
  final-step-not (FIndet (IFst npr ind))
                 (ITFstPair fin) =
    npr _ _ refl
  final-step-not (FIndet (ISnd npr ind))
                 (ITSndPair fin) =
    npr _ _ refl
  final-step-not (FIndet (IHole fin))
                 (ITHole stp) =
    final-step-not fin stp
  final-step-not (FIndet (IFst npr ind1))
                 (ITFst stp) =
    final-step-not (FIndet ind1) stp
  final-step-not (FIndet (ISnd npr ind1))
                 (ITSnd stp) =
    final-step-not (FIndet ind1) stp
  
