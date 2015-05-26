module verse.language.instructions where

open import Data.List
open import Relation.Binary.PropositionalEquality using (_≡_ ; refl)

open import verse.error
open import verse.language.arch
open import verse.language.function
open import verse.language.types

open Arch
open Operand


private
  module ArithmeticAssign {arch : Arch}{mach : Machine arch}{d : Dim}{k : Kind {d} ✓} where

    record AddEq (A B : Set) : Set where
      field
        ⦃ A' ⦄ : Operand {d}{k} A
        ⦃ B' ⦄ : Operand {d}{k} B
--        accAEq  : access? A' ≡ ReadWrite
        typeEq  : typeOf? A' ≡ typeOf? B'
        _←+_    : A → B → Statement mach

open ArithmeticAssign public
