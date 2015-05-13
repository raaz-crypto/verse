module verse.language.instructions where

open import verse.language.arch
open import Data.List
open import verse.language.types
open import verse.error

open Arch

record AddEq {arch : Arch}{opty : OpType}{d : Dim}{k : Kind {d} ✓}{ty : Type k}(op₁ : Operand arch ReadWrite ty)(op₂ : Operand arch opty ty) : Set where
  field
    _+≔_ : List (instruction arch)

