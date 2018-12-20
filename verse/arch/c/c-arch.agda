module verse.arch.c.c-arch where

open import Data.String
open import Data.Nat renaming ( _≤?_ to _≤?ℕ_ )
open import Relation.Nullary

open import verse.language.arch
open import verse.language.machine
open import verse.language.types
open import verse.language.userError


-- Define C Architecture

private
  module cArchitecture where

    data CVariable : Set where
      cvar_ : String → CVariable

    data CInstruction : Set where
      _+≔_  : CVariable → CVariable → CInstruction

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

    CRegister? : CVariable → Error (UserError c-arch)
    CRegister? _ = ✓

    CInstruction? : CInstruction → Error (UserError c-arch)
    CInstruction? _ = ✓

    CType? : {d : Dim} → Type d → Error (UserError c-arch)
    CType? (word n en) with n ≤?ℕ 3
    ...                |    yes _ = ✓
    ...                |    no  _ = error: (Type word n en Unsupported)
    CType? (array k of w) with CType? w
    ...                   |    ✓ = ✓
    ...                   |    _ = error: (Type array k of w Unsupported)
    CType? (t ⋆) with CType? t
    ...          |    ✓ = ✓
    ...          |    _ = error: (Type t ⋆ Unsupported)

    c-mach : Machine c-arch
    c-mach = MakeMachine CRegister? CInstruction? CType?

open cMachine public
