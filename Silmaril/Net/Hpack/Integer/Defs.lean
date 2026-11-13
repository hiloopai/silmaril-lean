module

@[expose] public section

/-!
# HPACK integers and string literals (RFC 7541 §5)

HPACK (RFC 7541), the field compression of HTTP/2, writes every number as an *N-bit prefix
integer* (§5.1) and every name or value as a *string literal* (§5.2).

**Integers (§5.1).** An integer `I` with an `N`-bit prefix (`1 ≤ N ≤ 8`) shares its first octet
with `8 - N` flag bits written by the caller (`hi`, a multiple of `2^N` below 256):

```
if I < 2^N - 1, encode I on N bits
else
    encode (2^N - 1) on N bits
    I = I - (2^N - 1)
    while I >= 128
         encode (I % 128 + 128) on 8 bits
         I = I / 128
    encode I on 8 bits
```

`encodeInt N hi I` is that pseudocode; `decodeInt N` reads it back (§5.1, "decode I from the next
N bits", then the continuation octets least significant first) and ignores the flag bits, which
the caller has already dispatched on.

**String literals (§5.2).** `H (1 bit) | String Length (7+) | String Data`. `encodeString`
writes the raw form (`H = 0`). `decodeString` accepts the raw form and **rejects Huffman-coded
strings** (`H = 1`), whose code (Appendix B) is not formalised yet (see docs/projects/http.md).

**Limits (§5.1).** "Integer encodings that exceed implementation limits — in value or octet
length — MUST be treated as decoding errors." The decoders here are total over unbounded
naturals; `decodeIntBounded` adds the octet-length limit a hardened decoder needs (RFC 7541
§7.4, "Implementation Limits").

All definitions are on `List UInt8` and depend only on Lean core.
-/

namespace Silmaril.Net.Hpack

/-- The largest value of an `n`-bit prefix: `2^n - 1`. -/
def prefixMax (n : Nat) : Nat := 2 ^ n - 1

/-- The continuation octets of §5.1: base 128, least significant group first, the high bit set
on every octet but the last. -/
def encodeRest (i : Nat) : List UInt8 :=
  if i < 128 then [i.toUInt8] else (i % 128 + 128).toUInt8 :: encodeRest (i / 128)
termination_by i
decreasing_by omega

/-- `encodeInt n hi i`: the integer `i` with an `n`-bit prefix, under the flag bits `hi`
(RFC 7541 §5.1). -/
def encodeInt (n hi i : Nat) : List UInt8 :=
  if i < prefixMax n then [(hi + i).toUInt8]
  else (hi + prefixMax n).toUInt8 :: encodeRest (i - prefixMax n)

/-- Read continuation octets (§5.1): the value and the remaining input. -/
def decodeRest : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | b :: bs =>
    if b.toNat < 128 then some (b.toNat, bs)
    else match decodeRest bs with
      | some (r, bs') => some (b.toNat - 128 + 128 * r, bs')
      | none => none

/-- Read an integer with an `n`-bit prefix (§5.1); the flag bits of the first octet are
ignored. -/
def decodeInt (n : Nat) : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | b :: bs =>
    let v := b.toNat % 2 ^ n
    if v < prefixMax n then some (v, bs)
    else match decodeRest bs with
      | some (r, bs') => some (prefixMax n + r, bs')
      | none => none

/-- The flag bits of an octet above an `n`-bit prefix (the caller's dispatch, §6). -/
def flags (n : Nat) (b : UInt8) : Nat := b.toNat / 2 ^ n * 2 ^ n

/-- `decodeInt` with at most `k` continuation octets (§5.1: an implementation limit on the
octet length). -/
def decodeIntBounded (k n : Nat) (xs : List UInt8) : Option (Nat × List UInt8) :=
  match decodeInt n xs with
  | some (i, rest) => if xs.length - rest.length ≤ k + 1 then some (i, rest) else none
  | none => none

/-! ## String literals (§5.2) -/

/-- A raw (non-Huffman) string literal: `H = 0`, the length with a 7-bit prefix, the octets. -/
def encodeString (s : List UInt8) : List UInt8 := encodeInt 7 0 s.length ++ s

/-- Read a string literal (§5.2). Huffman-coded literals (`H = 1`) are rejected: the Huffman
code of Appendix B is future work. -/
def decodeString : List UInt8 → Option (List UInt8 × List UInt8)
  | [] => none
  | b :: bs =>
    if 128 ≤ b.toNat then none
    else match decodeInt 7 (b :: bs) with
      | some (len, rest) => if len ≤ rest.length then some (rest.take len, rest.drop len) else none
      | none => none

end Silmaril.Net.Hpack
