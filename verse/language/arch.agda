module verse.language.arch where

open import verse.error
open import verse.language.types

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

    -- Get the type of a register.
    typeOf        : {d : Dim}{k : Kind {d} ✓} → register → Type k

open Arch ⦃ ... ⦄

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
    register?    : register    → Error (MachineError arch)

    -- Check whether this instruction is supported and raise an error
    -- otherwise.
    instruction? : instruction → Error (MachineError arch)


-- Local variable is either allocated on the stack or is a register.
data Local (arch : Arch) : Set where
     onStack    : {d : Dim}{k : Kind {d} ✓} → stackOffset → Type k → Local arch
     inRegister : register    → Local arch

data OpType : Set where
     ReadOnly  : OpType
     ReadWrite : OpType

-- Operands associated with an architecture.
data Operand (arch : Arch) (o : OpType) : Set where

     -- It can be a function parameter.
     param : {d : Dim} → {k : Kind {d} ✓} → stackOffset → Type k →  Operand arch o

     -- Or a register
     reg   : register → Operand arch o

     -- Or a local variable. Local variable can be either on a stack or a register.
     local : Local arch →  Operand arch o


