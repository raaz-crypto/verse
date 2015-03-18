module verse.language.instructions where

open import verse.language.arch
open import Data.List

open Arch

record AddEq (arch : Arch) : Set where
  field
    _+≔_ : {op : OpType} → Operand arch ReadWrite → Operand arch op → List (instruction arch)

