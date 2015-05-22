module verse.language.instructions where

open import verse.error
open import verse.language.arch
open import verse.language.types
open import Data.List
open import Relation.Binary.PropositionalEquality using (_≡_)

open Arch
open Operand {{...}}
{-
private
  module ArithmeticAssign {arch : Arch}{d : Dim}{k : Kind {d} ✓} where
    
open ArithmeticAssign public
-}

record AddEq {arch : Arch}{d : Dim}{k : Kind {d} ✓}{ty : Type k}{acc : Access}(A B : Set) {{ A' : Operand {arch}{d}{k}{ty}{ReadWrite} A }} {{ B' : Operand {arch}{d}{k}{ty}{acc} B }} : Set where
  field
    _+≔_   : A → B → List (instruction arch)
--    accOfA : {a : A} → access? a ≡ ReadWrite
--    typeOf : {a : A}{b : B} → typeOf? a ≡ typeOf? b

open AddEq
