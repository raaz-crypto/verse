module verse.util.typeEq where

open import Data.Bool        public
open import Data.Nat         using    ()
                             renaming ( _≟_ to _≟ℕ_ )
open import Relation.Nullary

open import verse.endian
open import verse.product
open import verse.language.arch
open import verse.language.types
open import verse.language.userError

open Arch


-- Dimension equality predicate
_dim≟_ : Dim → Dim → Bool
_dim≟_ ∞ ∞ = true
_dim≟_ (finite n₁) (finite n₂) = is n₁ ≟ℕ n₂ Provable
_dim≟_ _ _ = false


-- Type equality predicate
_type≟_ : {d₁ d₂ : Dim} → Type d₁ → Type d₂ → Bool
_type≟_ (word n₁ en₁)   (word n₂ en₂)   = ifProvable n₁ ≟ℕ n₂ Then (en₁ endian≟ en₂)
_type≟_ (array n₁ of x endian e₁) (array n₂ of y endian e₂) = ifProvable n₁ ≟ℕ n₂ Then (_type≟_ x y)
_type≟_ (x *) (y *)           = _type≟_ x y
_type≟_        _               _               = false
