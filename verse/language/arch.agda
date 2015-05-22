module verse.language.arch where

open import verse.error
open import verse.language.types
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.List
open import Data.String

-- An architecture is a generic class of machines. It determines the
-- instructions and registers that machine of that architecture can
-- potentially support. Besides registers, the instructions can use
-- data stored in stack. The stack variables accessible to a code
-- fragment is essentially parameters that are pushed to the function
-- call context and local variables.
record Arch : Set₁ where

  constructor MakeArch
  field
    -- The instruction set.
    instruction   : Set

    -- The registers supported by machines
    register      : Set

    -- Type that captures stack offset in this architecture. Merely
    -- storing the byte offset is often not enough because the
    -- architectures can have alignment restrictions. We parameterise
    -- this over architecture.
    stackOffset   : Set

    -- Type that captures constants of the architecture.
    constant      : Set

    --⦃-_-⦄        : List (String) → List (instruction)

    --_♯_           : instruction → String → instruction

    -- Get the type of a register.
    --typeOf        : {d : Dim}{k : Kind {d} ✓}{ty : Type k} → register ty  → Type k
    --specTypeOf    : {d : Dim}{k : Kind {d} ✓}{ty : Type k}(r : register ty) → typeOf r ≡ ty

open Arch {{...}}

-- When generating instructions for a particular machine of a given
-- architecture there can be errors due to unsupported registers or
-- instructions. This type captures such errors.
data MachineError (arch : Arch) : Set where
  Register_Unsupported    : register    → MachineError arch
  Instruction_Unsupported : instruction → MachineError arch

-- A machine is essentially a restriction on the architecture. It gives
-- predicates to check whether a register or instruction is supported.
record Machine (arch : Arch) : Set₁ where
  constructor MakeMachine
  field

    -- Check whether this register is supported and raise an error
    -- otherwise.
    register?    : register → Error (MachineError arch)

    -- Check whether this instruction is supported and raise an error
    -- otherwise.
    instruction? : instruction → Error (MachineError arch)


-- Local variable is either allocated on the stack or is a register.
{-
data Local (arch : Arch) : Set where
     onStack    : stackOffset → Local arch
     inRegister : register    → Local arch
-}

data Access :  Set where
  ReadWrite : Access
  ReadOnly  : Access


{-
data Statement (arch : Arch)(e : Error (MachineError arch)) : Set where
  statement : List (instruction) → Statement arch e
-}


-- Operands associated with an architecture.
{-
data Operand {d : Dim}{k : Kind {d} ✓}(arch : Arch)(acc : Access) : Type k → Set where

     -- It can be a function parameter.
     param : (ty : Type k) → stackOffset → Operand arch acc ty

     -- Or a register
     reg   : (ty : Type k) → register → Operand arch acc ty

     -- Or a local variable. Local variable can be either on a stack or a register.
     local : (ty : Type k) → Local arch →  Operand arch acc ty
-}

private
  module DataStore {d : Dim}{k : Kind {d} ✓}(arch : Arch)(acc : Access) where

    data Parameter : Type k → Set where
      param : {ty : Type k} → stackOffset → Parameter ty

{-
    data Register  : Type k → Set where
      reg : (ty : Type k) → register → Register arch acc ty

    data Local     : Type k → Set where
      localStack : (ty : Type k) → stackOffset → Local arch acc ty
      localReg   : (ty : Type k) → register    → Local arch acc ty
-}

open DataStore public

record Operand {arch : Arch}{d : Dim}{k : Kind {d} ✓}{ty : Type k}{acc : Access}(A : Set) : Set where
  field
    access? : A → Access
    typeOf? : A → Type k

open Operand

