module

public import Silmaril.Net.Hpack.Integer.Defs

@[expose] public section

/-!
# QPACK N-bit prefix string literals (RFC 9204 §4.1.2)

QPACK reuses HPACK's string literal (RFC 7541 §5.2) and generalizes it: "An 'N-bit prefix
string literal' begins mid-byte, with the first (8-N) bits allocated to a previous field. The
string uses one bit for the Huffman flag, followed by the length of the encoded string as a
(N-1)-bit prefix integer. The prefix size, N, can have a value between 2 and 8, inclusive. The
remainder of the string literal is unmodified" (§4.1.2).

```
  bits:   (8-N) caller flags | H | Length ((N-1)+) | Data (Length bytes)
```

`encodeStringN n hi s` writes the raw form (`H = 0`) under the caller's flag bits `hi` (a
multiple of `2^n` below 256). `decodeStringN n` ignores the caller's flags and **rejects
Huffman-coded strings** (`H = 1`), like HPACK's `decodeString` in this repository: the
Huffman code of RFC 7541 Appendix B is planned, not formalised.

"A string literal without a prefix length noted is an 8-bit prefix string literal and follows
the definitions in [RFC7541] without modification" (§4.1.2): `encodeStringN 8 0` is HPACK's
`encodeString` (its length has a 7-bit prefix) and `decodeStringN 8` is HPACK's
`decodeString` (`Silmaril.Net.Qpack.String.Thms`).
-/

namespace Silmaril.Net.Qpack

open Silmaril.Net.Hpack (encodeInt decodeInt)

/-- A raw (`H = 0`) `n`-bit prefix string literal under the flag bits `hi` (§4.1.2). -/
def encodeStringN (n hi : Nat) (s : List UInt8) : List UInt8 :=
  encodeInt (n - 1) hi s.length ++ s

/-- Read an `n`-bit prefix string literal (§4.1.2); the caller's `8 - n` flag bits are
ignored. Huffman-coded literals (`H = 1`, the bit of weight `2^(n-1)`) are rejected. -/
def decodeStringN (n : Nat) : List UInt8 → Option (List UInt8 × List UInt8)
  | [] => none
  | b :: bs =>
    if 2 ^ (n - 1) ≤ b.toNat % 2 ^ n then none
    else match decodeInt (n - 1) (b :: bs) with
      | some (len, rest) => if len ≤ rest.length then some (rest.take len, rest.drop len) else none
      | none => none

end Silmaril.Net.Qpack
