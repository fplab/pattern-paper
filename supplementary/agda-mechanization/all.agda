-- standard definitions of basic datatypes
-- and some quick lemmas about them
open import Bool
open import List
open import Nat
open import Prelude

-- definitions and lemmas about contexts
-- and variables
open import contexts
open import lemmas-contexts
open import exchange
open import weakening
open import freshness
open import lemmas-freshness
open import freshness-decidable
open import binders-disjointness
open import binders-disjoint-symmetric
open import hole-binders-disjoint-symmetric
open import binders-uniqueness

-- syntax and judgements from the paper
open import core
open import result-judgements
open import value-judgements
open import constraints-core
open import complete-constraints-core
open import patterns-core
open import dynamics-core
open import statics-core

-- decidability theorems 
open import htyp-decidable
open import satisfy-decidable
open import complete-satisfy-decidable
open import notintro-decidable
open import possible-decidable
open import xrefutable-decidable

-- some miscellaneous lemmas used throughout
open import lemmas-values
open import lemmas-patterns
open import lemmas-satisfy
open import lemmas-or-append
open import type-assignment-unicity

-- exclusivity theorems
open import satisfy-exclusive
open import complete-satisfy-exclusive

-- relationship between the complete
-- and incomplete constraint languages
open import complete-relationship
open import material-entailment

-- matching
open import matching-determinism
open import matching-coherence

-- various lemmas showing that our judgements
-- are well-behaved withrespect to
-- substitution
open import lemmas-subst-disjointness
open import lemmas-subst-value
open import lemmas-subst-result
open import lemmas-subst-matching
open import lemmas-subst-satisfy
open import lemmas-subst-list
open import lemmas-subst-type
open import lemmas-subst-exhaustive
open import lemmas-subst-nonredundant

-- type safety theorems
open import preservation
open import finality
open import determinism
