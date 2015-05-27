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
  module DataStore {d : Dim}{k : Kind {d} ✓}(arch : Arch)(acc : Access) where

    data Parameter : Type k → Set where
      param : {ty : Type k} → stackOffset → Parameter ty


    data Register : Type k → Set where
      reg : {ty : Type k} → register → Register ty

    data Local : Type k → Set where
      localStack : {ty : Type k} → stackOffset → Local ty
      localReg   : {ty : Type k} → register    → Local ty

open DataStore public


-- Operand Typeclass

record Operand {d : Dim}{k : Kind {d} ✓}(A : Set) : Set where
  field
    access? : Access
    typeOf? : Type k

open Operand


-- Operand instances

private
  module OperandInstances {arch : Arch}{acc : Access}{d : Dim}{k : Kind {d} ✓}{ty : Type k} where

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



{-
typeEq? : {arch : Arch}{d₁ d₂ : Dim}{k₁ : Kind {d₁} ✓}{k₂ : Kind {d₂} ✓} → Type k₁ → Type k₂ → Error (UserError arch)
typeEq? (word n₁ en₁) (word n₂ en₂) with n₁ ≟ℕ n₂ | en₁ ≟En en₂
...                                 |    yes _    | yes _       = ✓
...                                 |    _        | _           = error: (Type word n₁ en₁ MismatchWith word n₂ en₂)
typeEq? (word n en) ty₂ = error: (Type word n en MismatchWith ty₂)
typeEq? (array k₁ of x) (array k₂ of y) = {!!}
typeEq? (array k₁ of x) ty₂ = error: (Type array k₁ of x MismatchWith ty₂)
typeEq? (x ⋆) (y ⋆) = {!!}
typeEq? (x ⋆) ty₂ = error: (Type x ⋆ MismatchWith ty₂)
-}
