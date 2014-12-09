module verse.language.types where

open import Data.Nat renaming ( _≤_ to _≤ℕ_; _≤?_ to _≤?ℕ_ )
open import Relation.Binary
open import Relation.Nullary
open import Function

import Level

open import verse.product
open import verse.error

-- -- The type for array indices.

Index : ℕ → Set
Index 0       = ℕ
Index (suc n) = ℕ × Index n

_≤_ : ∀{n}  → Rel (Index n) Level.zero
_≤_ {0}     a        b         = a ≤ℕ b
_≤_ {suc n} (a , as) (b , bs)  = a ≤ℕ b ×  as ≤ bs


_≤?_ : ∀{n} → Decidable (_≤_ {n})
_≤?_ {0}     a        b        = a ≤?ℕ b
_≤?_ {suc n} (a , as) (b , bs)
     with a ≤?ℕ b | as  ≤? bs
...  |    yes p   | yes q    = yes (p , q)
...  |    no  neg | _        = no (neg ∘ proj₀)
...  |    _       | no neg   = no (neg ∘ proj₁)

data IndexError :  Set where
  index_≮_∎     : {n : ℕ} → Index n → Index n → IndexError


data TypeError : Set where
  bound_≱_∎    : {n   : ℕ} → Index n → Index n → TypeError
  wordsize_<_∎ : (n m : ℕ) → TypeError


index? : {n : ℕ} → Index n → Index n  → Error IndexError
index? as bs = unless incr as ≤? bs raise (index as ≮ bs ∎)
  where incr : {n : ℕ} → Index n → Index n
        incr {0} a            = suc a
        incr {suc n} (a , aˢ) = a , incr aˢ

bound? : {n : ℕ} → Index n → Error TypeError
bound? bˢ = unless 2ˢ ≤? bˢ raise bound bˢ ≱ 2ˢ ∎
  where 2ˢ : {n : ℕ} → Index n
        2ˢ {0}     = 2
        2ˢ {suc n} = 2 , 2ˢ

data Endian : Set where
  little    : Endian
  big       : Endian
  host      : Endian

data Kind  : Set where
  Scalar   : Kind
  Array    : Kind

data Size  : Set   where
  ∞        : Size
  bounded  : Kind → Size


data Type    : Size → Error TypeError → Set where
  word       : (n : ℕ)   -- 2^n bytes.
             → Endian
             → Type (bounded Scalar) ✓
  array_of_  : {n  : ℕ}
             → (bˢ : Index n)
             → Type (bounded Scalar) ✓
             → Type (bounded Array)  (bound? bˢ)
  _⋆         : {k : Kind} → Type (bounded k) ✓ → Type ∞ ✓


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


ScalarType : Set
ScalarType = Type (bounded Scalar) ✓

-- The byte type
Byte   : ScalarType
Byte   = word 0 host

-- Endian explicit versions of some haskell types.
Word16 : Endian → ScalarType
Word32 : Endian → ScalarType
Word64 : Endian → ScalarType

Word16 = word 1
Word32 = word 2
Word64 = word 3

-- Haskell word types that uses host endian.
Host16 : ScalarType
Host32 : ScalarType
Host64 : ScalarType

Host16 = Word16 host
Host32 = Word32 host
Host64 = Word64 host
