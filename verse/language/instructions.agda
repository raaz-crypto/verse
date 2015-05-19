module verse.language.instructions where

open import verse.error
open import verse.language.arch
open import verse.language.types
open import Data.List

open Arch

{-
private
  module ArithmeticAssign {arch : Arch}{d : Dim}{k : Kind {d} ✓} where
    
open ArithmeticAssign public
-}

record AddEq {arch : Arch}{d : Dim}{k : Kind {d} ✓}{acc : Access}(ty : Type k)(A B : Access → Type k → Set) : Set where
  field
    _+≔_ : A ReadWrite ty → B acc ty → List (instruction arch)

--open AddEq ⦃...⦄ public
       
