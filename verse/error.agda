module verse.error where

open import Data.Maybe as Maybe public
                                using    (functor)
                                renaming ( Maybe to Error
                                         ; just  to error:
                                         ; nothing to ✓
                                         )
open import Data.Product
open import Relation.Nullary
open import Relation.Nullary.Negation

data Expect (K : Set) : Set where
  expected   : K → Expect K
  unexpected : K → Expect K


when_raise_ : {C E : Set} → Dec C → E → Error E
when c raise e with c
...            |    yes _ = error: e
...            |    no  _ = ✓

unless_raise_ : {C E : Set} → Dec C → E → Error E
unless c raise e = when ¬? c raise e


_∧_ : {A B : Set} → Error A → Error B → Error (Error A × Error B)
✓ ∧ ✓  = ✓
a ∧ b  = error: (a , b)
