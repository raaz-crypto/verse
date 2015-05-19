module verse.arch.c.c-arch where

open import verse.error
open import verse.language.arch
open import verse.language.types
open import verse.language.instructions
open import Data.String
open import Data.List
open import Data.Nat

-- Define C Architecture

data CVariable : Set where
  cvar_ : String → CVariable


data CInstruction : Set where
  _+≛_  : CVariable → CVariable → CInstruction


data CConstant : Set where


c-arch : Arch
c-arch = MakeArch CInstruction CVariable CVariable CConstant 


-- ToCVar typeclass of those Type which can be converted to a CVariable

record ToCvar (A : Set) : Set where
  field
    toCvar : A → CVariable


-- Define C Machine

{-
CRegister? : CRegister → Error (MachineError c-arch)
CRegister? _ = ✓


CInstruction? : CInstruction → Error (MachineError c-arch)
CInstruction? (_ CInstruction.+≔ _) = ✓
CInstruction? other = error: Instruction other Unsupported


c-mach : Machine c-arch
c-mach = MakeMachine CRegister? CInstruction?
-}
