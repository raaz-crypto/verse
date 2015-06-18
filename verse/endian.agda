module verse.endian where

open import Data.Bool


-- Type capturing endianness.
data endian : Set where
  little    : endian  -- captures little endian
  big       : endian  -- big endian
  host      : endian  -- captures the endian of the host. If the
                      -- endianness is host that means no assumption
                      -- is to be made on the endianness of the data.


-- To decide if two endians are equal
_endian≟_ : endian → endian → Bool
_endian≟_ little little = true
_endian≟_ big    big    = true
_endian≟_ host   host   = true
_endian≟_  _      _     = false
