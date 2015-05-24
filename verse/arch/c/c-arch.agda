module verse.arch.c.c-arch where

open import Data.String
open import Data.Nat renaming (_≤?_ to _≤?ℕ_)
open import Relation.Nullary

open import verse.error
open import verse.language.arch
open import verse.language.types


-- Define C Architecture

private
  module cArchitecture where

    data CVariable : Set where
      cvar_ : String → CVariable

    data CInstruction : Set where
      _+≐_  : CVariable → CVariable → CInstruction

    data CConstant : Set where

    c-arch : Arch
    c-arch = MakeArch CInstruction CVariable CVariable CConstant 

open cArchitecture public


-- ToCVar typeclass of those Type which can be converted to a CVariable

record ToCvar (A : Set) : Set where
  field
    toCvar : A → CVariable


-- Define C Machine

private
  module cMachine where

    CRegister? : CVariable → Error (MachineError c-arch)
    CRegister? _ = ✓

    CInstruction? : CInstruction → Error (MachineError c-arch)
    CInstruction? _ = ✓

    CType? : {d : Dim} → {k : Kind {d} ✓} → Type k → Error (MachineError c-arch)
    CType? (word n en) with n ≤?ℕ 3
    ...                | yes _   = ✓
    ...                | no  _   = error: (Type word n en Unsupported)
    CType? (array k of w) with CType? w
    ...                   | ✓ = ✓
    ...                   | _ = error: (Type array k of w Unsupported)
    CType? (t ⋆) with CType? t
    ...          | ✓ = ✓
    ...          | _ = error: (Type t ⋆ Unsupported)

    c-mach : Machine c-arch
    c-mach = MakeMachine CRegister? CInstruction? CType?

open cMachine public
