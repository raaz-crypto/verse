module verse.language.machine where

open import verse.language.types
open import verse.error
open import Data.List

-- An architecture is a generic class of machines. It determines the
-- instructions, registers and features that machine of that
-- architecture can potentially support.
record Arch : Set₁ where
  constructor MakeArch
  field
    -- The instruction set.
    instruction   : Set

    -- Features supported in the architecture.
    feature       : Set

    -- The registered supported by machines
    register      : Set

    -- Features required for a given register
    regFeatures   : register    → List feature

    instFeatures  : instruction → List feature

open Arch ⦃ ... ⦄

-- A machine of a given architecture is captured by the by the
-- features that it supports.

record Machine (arch : Arch) : Set₁ where
  constructor MakeMachine
  field
    -- The features that of arch that this machine supports.
    supports     : List feature
