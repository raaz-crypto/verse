module verse.language.instructions where

open import Data.List
open import Relation.Binary.PropositionalEquality using (_≡_)

open import verse.error
open import verse.language.arch
open import verse.language.types

open Arch
open Operand


private
  module ArithmeticAssign {arch : Arch}{d : Dim}{k : Kind {d} ✓} where

    record AddEq (A B : Set) : Set where
      field
        ⦃ A' ⦄ : Operand {d}{k} A
        ⦃ B' ⦄ : Operand {d}{k} B
        accAEq  : access? A' ≡ ReadWrite
        typeEq  : typeOf? A' ≡ typeOf? B'
        _+≔_    : A → B → List (instruction arch)

open ArithmeticAssign public
