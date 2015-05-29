module verse.language.machine where

open import verse.language.arch
open import verse.language.types
open import verse.language.userError

open Arch ⦃...⦄


-- A machine is essentially a restriction on the architecture. It gives
-- predicates to check whether a register or instruction is supported.
record Machine (arch : Arch) : Set₁ where
  constructor MakeMachine
  field

    -- Check whether this register is supported and raise an error
    -- otherwise.
    register?    : register → Error (UserError arch)

    -- Check whether this instruction is supported and raise an error
    -- otherwise.
    instruction? : instruction → Error (UserError arch)

    -- Check whether this type is supported and raise an error
    -- otherwise.
    type?        : {d : Dim} → {k : Kind {d} ✓} → Type k → Error (UserError arch)
