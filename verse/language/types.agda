module verse.language.types where

open import Data.Nat         using    ( ℕ ; suc )
open import Function
import Level
open import Data.Unit        public
                             using    ()
                             renaming ( tt to scalar )

open import verse.endian
open import verse.error
open import verse.product


-- The dimension of a type. A type can be finite dimensional or
-- infinitary.
data Dim : Set where
  ∞      : Dim
  finite : ℕ → Dim

-- Scalars are kinds.
⟨scalar⟩ : Dim
⟨scalar⟩ = finite 0
⟨vector⟩ : Dim
⟨vector⟩ = finite 1


-- Types using dimensions and kinds
data Type  :  (d : Dim) → Set where
     word              : (n : ℕ)   -- 2^n bytes.
                       → endian
                       → Type ⟨scalar⟩

     array_of_endian_  : (n : ℕ)
                       → Type ⟨scalar⟩
                       → endian
                       → Type ⟨vector⟩

     _*                : {n : ℕ} 
                       → Type (finite n)
                       → Type ∞


------------------- Type short hands ---------------------------

-- The byte type
-- Byte   : Type ⟨scalar⟩; Byte   = word 0


-- Word types in Haskell types.
-- Word16 : Type ⟨scalar⟩; Word16 = word 1
-- Word32 : Type ⟨scalar⟩; Word32 = word 2
-- Word64 : Type ⟨scalar⟩; Word64 = word 3

----------------------------------------------------------------
{-

index? : {n : ℕ} → Index n → Index n  → Error IndexError
index? as bs = unless incr as ≤? bs raise (index as ≮ bs ∎)
  where incr : {n : ℕ} → Index n → Index n
        incr {0} a            = suc a
        incr {suc n} (a , aˢ) = a , incr aˢ


Type ⟨scalar⟩     = Type (bounded Scalar) ✓
ArrayType      = Type (bounded Array)
BoundedType k  = Type (bounded k) ✓


-- It is generally true that if a machine supports a word of size 2^k
-- then it supports any array whose underlying scalar is of the same
-- size. Similarly if it supports bounded type t, it supports
-- sequences of those sizes. We give a function which given the word
-- size checks if the particular type is supported.

supports? : {b : Size}{err : Error TypeError}
          → ℕ
          → Type b err → Error TypeError

supports? m (word n _)       = when suc m ≤?ℕ n raise wordsize m < n ∎
supports? m (array  _ of ty) = supports? m ty
supports? m (ty ⋆)           = supports? m ty

-}
