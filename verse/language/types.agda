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


-- Type that catches kind errors.
data KindError : Set where
  bound_≱_∎    : {n   : ℕ} → ℕⁿ {suc n} → ℕⁿ {suc n} → KindError


-- Checking for kind error.
private
  kind? : {n : ℕ} → ℕⁿ {n} → Error KindError
  kind? {0}         _ = ✓
  kind? {suc n } bˢ = unless 2 ˢ ≤? bˢ raise bound bˢ ≱ 2 ˢ ∎


-- The kind of a type.
data Kind : {dim : Dim} → Error KindError → Set where
     ⟨_⟩  : {n : ℕ}
          → (bs : ℕⁿ {n})
          → Kind {finite n} (kind? bs)

     ⟨∞⟩  : Kind {∞} ✓                      -- Infinitary


-- Scalars are kinds.
⟨scalar⟩ : Kind {finite 0} ✓
⟨scalar⟩ = ⟨_⟩ {0} scalar


-- Types using dimensions and kinds
data Type  :  {d : Dim} → Kind {d}  ✓ → Set where
  word       : (n : ℕ)   -- 2^n bytes.
             → endian
             → Type ⟨scalar⟩

  array_of_  : {n : ℕ}
             → (k : Kind {finite (suc n)} ✓)
             → Type ⟨scalar⟩
             → Type k

  _⋆         : {n : ℕ} {k : Kind {finite n} ✓}
             → Type k
             → Type ⟨∞⟩


------------------- Type short hands ---------------------------


-- The byte type
Byte   : Type ⟨scalar⟩


-- Endian explicit versions of some haskell types.
Word16 : endian → Type ⟨scalar⟩
Word32 : endian → Type ⟨scalar⟩
Word64 : endian → Type ⟨scalar⟩

-- Haskell word types that uses host endian.
Host16 : Type ⟨scalar⟩
Host32 : Type ⟨scalar⟩
Host64 : Type ⟨scalar⟩

Byte   = word 0 host
Word16 = word 1
Word32 = word 2
Word64 = word 3
Host16 = Word16 host
Host32 = Word32 host
Host64 = Word64 host


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
