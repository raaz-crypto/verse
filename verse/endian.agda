module verse.endian where


-- Type capturing endianness.
data endian : Set where
  little    : endian  -- captures little endian
  big       : endian  -- big endian
  host      : endian  -- captures the endian of the host. If the
                      -- endianness is host that means no assumption
                      -- is to be made on the endianness of the data.
