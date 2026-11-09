module

public import Silmaril.Formats.Compression.Zlib.Basic

/-!
# A zlib member with a preserved input suffix

The existing one-shot `zlibDecompress` requires exact end of input. A library
call instead returns after one stream, leaving subsequent bytes untouched.
This shared specification adds that observation, while retaining the existing
header, raw-DEFLATE and checksum specifications. Preset dictionaries remain
outside this format profile, as in `zlibDecompress`.
-/

@[expose] public section

namespace Silmaril.Formats.Compression

open Deflate

/-- CHECK consumes four big-endian Adler bytes and preserves following input. -/
def zlibCheckTrailer (data afterData : List UInt8) : Option (List UInt8) :=
  match afterData with
  | a0 :: a1 :: a2 :: a3 :: rest =>
    if be32Val a0 a1 a2 a3 = (adler32 ⟨data.toArray⟩).toNat then some rest else none
  | _ => none

/-- Decode exactly one dictionary-free zlib member, keeping its suffix. -/
def zlibTake (bytes : List UInt8) : Option (List UInt8 × List UInt8) :=
  match zlibCheckHeader bytes with
  | none => none
  | some body =>
    match deflateTake body with
    | .error _ => none
    | .ok (data, rest) =>
      match zlibCheckTrailer data rest with
      | none => none
      | some tail => some (data, tail)

/-- A take-style result is an exact-end result only when no bytes remain. -/
def exactMember (result : Option (List UInt8 × List UInt8)) : Option ByteArray :=
  match result with
  | some (data, []) => some ⟨data.toArray⟩
  | _ => none

end Silmaril.Formats.Compression
