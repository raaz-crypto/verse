module verse.try where

open import Data.List

open import verse.arch.c.c-arch
open import verse.arch.c.c-instructions
open import verse.error
open import verse.language.arch
open import verse.language.instructions
open import verse.language.types

open Arch
open Operand

op1 : Parameter c-arch ReadWrite Host16
op1 = param (cvar "op1")

op2 : Register c-arch ReadOnly Host16
op2 = reg (cvar "op2")

open AddEq ⦃...⦄

try : List (instruction c-arch)
try = _+≔_ op1 op2
