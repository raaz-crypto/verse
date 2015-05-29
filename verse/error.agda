module verse.error where

open import Data.Bool
open import Data.Maybe as Maybe public
                                using    ()
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


_∧ₑ_ : {A B : Set} → Error A → Error B → Error (Error A × Error B)
✓ ∧ₑ ✓  = ✓
a ∧ₑ b  = error: (a , b)


------------ Functions to handle boolean predicates --------------

is_Provable : {D : Set} → Dec D → Bool
is_Provable d with d
...           |    yes _ = true
...           |    no  _ = false


ifProvable_Then_ : {D : Set} → Dec D → Bool → Bool
ifProvable d Then b = is d Provable ∧ b


check_orRaise_ : {E : Set} → Bool → E → Error E
check_orRaise_ b e with b
...                |    true  = ✓
...                |    false = error: e
