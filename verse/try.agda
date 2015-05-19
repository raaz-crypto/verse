module verse.try where

open import verse.language.arch
open import verse.language.types
open import verse.language.instructions
open import Data.String
open import verse.arch.c.c-arch
open import verse.arch.c.c-instructions
open import Data.List
open import Data.Nat

open Arch
open ToCvar {{...}}
open AddEq {{...}}


op1 : Parameter c-arch ReadWrite Host16
op1 = param (cvar "op1")

op2 : Parameter c-arch ReadWrite Host16
op2 = param (cvar "op2")


try : List (instruction c-arch)
try = _+≔_ {_}{_}{_}{_}{_}{Parameter _}{Parameter _} op1 op2

