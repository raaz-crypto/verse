module verse.language.instructions where

open import verse.language.arch
open import Data.List
open import verse.language.types
open import verse.error

open Arch

private
  module ArithmeticAssign {arch : Arch}{d : Dim}{k : Kind {d} ✓} where

{-
    record AddEq {e : Error (MachineError arch)} (ty : Type k) : Set where
      field
        _+≔_ : (op₁ : Operand arch ReadWrite ty)(op₂ : Operand arch acc₂ ty) → Statement arch e
-}
  
    record AddEq (A B : Access → Type k → Set) : Set where
      field
        _+≔_ : {acc : Access}{ty : Type k} → A ReadWrite ty → B acc ty → List (instruction arch)

open ArithmeticAssign public
