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


open Arch ⦃...⦄


-- Local variable is either allocated on the stack or is a register.

data Access :  Set where
  ReadWrite : Access
  ReadOnly  : Access


private
  module DataStore {d : Dim}(arch : Arch)(acc : Access) where

    data Parameter : Type d → Set where
      param : {ty : Type d} → stackOffset → Parameter ty


    data Register : Type d → Set where
      reg : {ty : Type d} → register → Register ty

    data Local : Type d → Set where
      localStack : {ty : Type d} → stackOffset → Local ty
      localReg   : {ty : Type d} → register    → Local ty

open DataStore public


-- Operand Typeclass

record Operand {d : Dim}(A : Set) : Set where
  field
    access? : Access
    typeOf? : Type d

open Operand


-- Operand instances

private
  module OperandInstances {arch : Arch}{acc : Access}{d : Dim}{ty : Type d} where

    instance
      paramIsOperand : Operand (Parameter arch acc ty)
      paramIsOperand = record { access? = acc
                              ; typeOf? = ty
                              }

      regIsOperand : Operand (Register arch acc ty)
      regIsOperand = record { access? = acc
                            ; typeOf? = ty
                            }

      localIsOperand : Operand (Local arch acc ty)
      localIsOperand = record { access? = acc
                              ; typeOf? = ty
                              }

open OperandInstances public
