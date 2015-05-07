module verse.language.function where

open import verse.language.arch
open import Data.String
open import Data.List
open Arch

data Statement (arch : Arch) : Set where
  stat : List (instruction arch) → Statement arch

data VarDecl (arch : Arch) : Set where

data FunctionBody (arch : Arch) : Set where
  funcBody : List (Statement arch) → FunctionBody arch

data Closure (arch : Arch) : Set where
  closure : List (VarDecl arch) → Closure arch

data Function (arch : Arch) : Set where
  func : String → Closure arch → FunctionBody arch → Function arch

