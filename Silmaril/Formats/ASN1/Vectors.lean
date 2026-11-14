module

public import Silmaril.Formats.ASN1.Time.Defs

/-!
# ASN.1 DER: known-answer checks

Boundary and negative cases for the DER layer and the universal-type codecs,
checked by evaluation in the kernel. The DER layer rejects non-minimal and
indefinite lengths, the reserved length octet `0xFF`, truncation, trailing
octets, the end-of-contents tag and non-minimal tags. The codecs reject
non-minimal INTEGERs, BOOLEANs other than `0x00`/`0xFF`, constructed strings,
bad BIT STRING padding, non-minimal OID subidentifiers, malformed or invalid
times, fractional seconds, and unsorted SET OF.
-/

namespace Silmaril.Formats.ASN1.Vectors

open Silmaril.Formats.ASN1

/-- Decode DER octets with a value codec. -/
def decodeAs {α : Type} (c : Codec Value α) (s : List UInt8) : Option α := (Codec.derCodec c).dec s

/-! ## Lengths -/

-- Short-form lengths must be used below 128.
example : decode [0x04, 0x81, 0x01, 0x00] = none := by decide +kernel
example : decode [0x04, 0x01, 0x00] = some (.prim Tag.octetString [0]) := by decide +kernel
-- Long-form lengths have no leading zero octet.
example : decode (0x04 :: 0x82 :: 0x00 :: 0x80 :: List.replicate 128 0) = none := by
  decide +kernel
example : decode (0x04 :: 0x81 :: 0x80 :: List.replicate 128 0) =
    some (.prim Tag.octetString (List.replicate 128 0)) := by decide +kernel
-- The BER indefinite length is not DER.
example : decode [0x30, 0x80, 0x05, 0x00, 0x00, 0x00] = none := by decide +kernel
example : decode [0x30, 0x02, 0x05, 0x00] = some (.cons Tag.sequence [.prim Tag.null []]) := by
  decide +kernel
-- The reserved length octet `0xFF`, truncation, and trailing octets.
example : decode [0x04, 0xFF, 0x00] = none := by decide +kernel
example : decode [0x04, 0x02, 0x00] = none := by decide +kernel
example : decode [0x04, 0x01, 0x00, 0x00] = none := by decide +kernel

/-! ## Identifiers -/

-- The end-of-contents tag does not occur in DER.
example : decode [0x00, 0x00] = none := by decide +kernel
-- Tag numbers below 31 use the low form; the high form is minimal.
example : decode [0x9F, 0x1E, 0x00] = none := by decide +kernel
example : decode [0x9F, 0x80, 0x1F, 0x00] = none := by decide +kernel
example : decode [0x9F, 0x1F, 0x00] = some (.prim (Tag.context 31) []) := by decide +kernel
example : encode (.prim (Tag.context 201) []) = [0x9F, 0x81, 0x49, 0x00] := by decide +kernel

/-! ## Universal types -/

-- INTEGER: minimal two's complement.
example : decodeAs integer [0x02, 0x02, 0x00, 0x05] = none := by decide +kernel
example : decodeAs integer [0x02, 0x02, 0xFF, 0x80] = none := by decide +kernel
example : decodeAs integer [0x02, 0x00] = none := by decide +kernel
example : decodeAs integer [0x02, 0x01, 0x05] = some 5 := by decide +kernel
example : decodeAs integer [0x02, 0x02, 0x00, 0x80] = some 128 := by decide +kernel
example : decodeAs integer [0x02, 0x01, 0x80] = some (-128) := by decide +kernel
example : decodeAs integer [0x02, 0x02, 0xFF, 0x7F] = some (-129) := by decide +kernel
example : (Codec.derCodec integer).enc (-1) = [0x02, 0x01, 0xFF] := by decide +kernel
example : decodeAs natural [0x02, 0x01, 0xFF] = none := by decide +kernel
-- BOOLEAN: only `0x00` and `0xFF`.
example : decodeAs boolean [0x01, 0x01, 0x01] = none := by decide +kernel
example : decodeAs boolean [0x01, 0x01, 0xFF] = some true := by decide +kernel
example : decodeAs boolean [0x01, 0x01, 0x00] = some false := by decide +kernel
-- Primitive types reject the constructed form.
example : decodeAs octetString [0x24, 0x03, 0x04, 0x01, 0x00] = none := by decide +kernel
-- NULL has empty contents.
example : decodeAs null [0x05, 0x01, 0x00] = none := by decide +kernel
-- BIT STRING: at most 7 unused bits, all zero.
example : decodeAs bitString [0x03, 0x02, 0x01, 0x81] = none := by decide +kernel
example : decodeAs bitString [0x03, 0x02, 0x08, 0x00] = none := by decide +kernel
example : decodeAs bitString [0x03, 0x01, 0x01] = none := by decide +kernel
example : decodeAs bitString [0x03, 0x02, 0x01, 0x80] = some ⟨1, [0x80]⟩ := by decide +kernel
-- OBJECT IDENTIFIER: `2.5.29.19` (basicConstraints) and `1.2.840.113549`.
example : decodeAs oid [0x06, 0x03, 0x55, 0x1D, 0x13] = some [2, 5, 29, 19] := by decide +kernel
example : decodeAs oid [0x06, 0x04, 0x55, 0x1D, 0x80, 0x13] = none := by decide +kernel
example : decodeAs oid [0x06, 0x00] = none := by decide +kernel
example : decodeAs oid [0x06, 0x06, 0x2A, 0x86, 0x48, 0x86, 0xF7, 0x0D] =
    some [1, 2, 840, 113549] := by decide +kernel
-- Character strings: `*` is not printable; `0x80` is not ASCII.
example : decodeAs printableString [0x13, 0x02, 0x41, 0x2A] = none := by decide +kernel
example : decodeAs printableString [0x13, 0x02, 0x41, 0x3F] = some [0x41, 0x3F] := by
  decide +kernel
example : decodeAs ia5String [0x16, 0x01, 0x80] = none := by decide +kernel

/-! ## Times (the strings are given as their ASCII octets) -/

-- `150604110438Z`
example : decodeAs utcTime (0x17 :: 0x0D :: [0x31, 0x35, 0x30, 0x36, 0x30, 0x34, 0x31, 0x31,
    0x30, 0x34, 0x33, 0x38, 0x5a]) = some ⟨2015, 6, 4, 11, 4, 38⟩ := by decide +kernel
-- Seconds are required: `1506041104Z`.
example : decodeAs utcTime (0x17 :: 0x0B :: [0x31, 0x35, 0x30, 0x36, 0x30, 0x34, 0x31, 0x31,
    0x30, 0x34, 0x5a]) = none := by decide +kernel
-- 31 February: `150231110438Z`.
example : decodeAs utcTime (0x17 :: 0x0D :: [0x31, 0x35, 0x30, 0x32, 0x33, 0x31, 0x31, 0x31,
    0x30, 0x34, 0x33, 0x38, 0x5a]) = none := by decide +kernel
-- `20500101000000Z`
example : decodeAs generalizedTime (0x18 :: 0x0F :: [0x32, 0x30, 0x35, 0x30, 0x30, 0x31, 0x30,
    0x31, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x5a]) = some ⟨2050, 1, 1, 0, 0, 0⟩ := by
  decide +kernel
-- No fractional seconds: `20500101000000.5Z`.
example : decodeAs generalizedTime (0x18 :: 0x11 :: [0x32, 0x30, 0x35, 0x30, 0x30, 0x31, 0x30,
    0x31, 0x30, 0x30, 0x30, 0x30, 0x30, 0x30, 0x2e, 0x35, 0x5a]) = none := by decide +kernel
-- RFC 5280: a 2049 date must be UTCTime, not GeneralizedTime (`20491231235959Z`).
example : decodeAs time (0x18 :: 0x0F :: [0x32, 0x30, 0x34, 0x39, 0x31, 0x32, 0x33, 0x31,
    0x32, 0x33, 0x35, 0x39, 0x35, 0x39, 0x5a]) = some (.generalized ⟨2049, 12, 31, 23, 59, 59⟩) := by
  decide +kernel
example : decodeAs rfc5280Time (0x18 :: 0x0F :: [0x32, 0x30, 0x34, 0x39, 0x31, 0x32, 0x33, 0x31,
    0x32, 0x33, 0x35, 0x39, 0x35, 0x39, 0x5a]) = none := by decide +kernel

/-! ## SET OF -/

-- SET OF is sorted by encoding.
example : decodeAs (setOf integer) [0x31, 0x06, 0x02, 0x01, 0x01, 0x02, 0x01, 0x02] =
    some [1, 2] := by decide +kernel
example : decodeAs (setOf integer) [0x31, 0x06, 0x02, 0x01, 0x02, 0x02, 0x01, 0x01] =
    none := by decide +kernel

end Silmaril.Formats.ASN1.Vectors
