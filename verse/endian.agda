module verse.endian where

open import Relation.Binary
open import Relation.Binary.PropositionalEquality using ( refl ; _≡_ )
open import Relation.Nullary


-- Type capturing endianness.
data endian : Set where
  little    : endian  -- captures little endian
  big       : endian  -- big endian
  host      : endian  -- captures the endian of the host. If the
                      -- endianness is host that means no assumption
                      -- is to be made on the endianness of the data.


-- To decide if two endians are equal
endianEq? : Decidable {A = endian}{B = endian} _≡_
endianEq? = helper
  where helper : (x : endian) → (y : endian) → Dec (x ≡ y)
        helper little little = yes refl
        helper big    big    = yes refl
        helper host   host   = yes refl
        helper little big    = no λ()
        helper little host   = no λ()
        helper big    little = no (λ ())
        helper big    host   = no (λ ())
        helper host   little = no (λ ())
        helper host   big    = no (λ ())
