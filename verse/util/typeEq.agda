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


-- Kind equality predicate
_kind≟_ : {d₁ d₂ : Dim}{ke₁ ke₂ : Error KindError} → Kind {d₁} ke₁ → Kind {d₂} ke₂ → Bool
_kind≟_ {finite n₁} {finite n₂} ⟨ bs₁ ⟩ ⟨ bs₂ ⟩ = ifProvable n₁ ≟ℕ n₂ Then (bs₁ ≟ℕⁿ bs₂)
_kind≟_ ⟨∞⟩ ⟨∞⟩    = true
_kind≟_  _   _      = false


-- Type equality predicate
_type≟_ : {arch : Arch}{d₁ d₂ : Dim}{k₁ : Kind {d₁} ✓}{k₂ : Kind {d₂} ✓} → Type k₁ → Type k₂ → Bool
_type≟_        (word n₁ en₁)   (word n₂ en₂)   = ifProvable n₁ ≟ℕ n₂ Then (en₁ endian≟ en₂)
_type≟_ {arch} (array k₁ of x) (array k₂ of y) = k₁ kind≟ k₂ ∧ (_type≟_ {arch} x y)
_type≟_ {arch} (x ⋆)           (y ⋆)           = _type≟_ {arch} x y
_type≟_        _               _               = false
