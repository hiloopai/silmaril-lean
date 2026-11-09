module

public import Silmaril.X86.Ladder.ZlibChecksums.Spec.Defs

/-!
# Adler-32 as RFC 1950 defines it

RFC 1950 (ZLIB Compressed Data Format Specification 3.3, section 9, "Adler-32 algorithm"),
written independently of zlib's code and of `Spec.adler32`:

    A = 1 + D1 + D2 + ... + Dn (mod 65521)
    B = (1 + D1) + (1 + D1 + D2) + ... + (1 + D1 + D2 + ... + Dn) (mod 65521)
      = n×D1 + (n−1)×D2 + (n−2)×D3 + ... + Dn + n (mod 65521)
    Adler-32(D) = B × 65536 + A

`rfcA s1 bs` is `s1 + D1 + … + Dn` (unreduced); `rfcB s1 s2 bs` is
`s2 + Σ_{j=1..n} rfcA s1 (D1 … Dj)` (unreduced); `rfc1950 bs` reduces both with the start
`A = 1`, `B = 0` and packs them. `rfcFrom a bs` is the same with the start taken from the
two 16-bit halves of an incoming value `a` (the incremental use RFC 1950 describes: "the
Adler-32 of a sequence continued from a previous value"), each assumed `< 65521`.
-/

@[expose] public section

namespace Silmaril.X86.Ladder.ZlibChecksums.Rfc1950

open Silmaril.X86 (Byte)

/-- `s1 + D1 + … + Dn`, no reduction. -/
def rfcA (s1 : Nat) (bs : List Byte) : Nat := s1 + (bs.map (·.toNat)).sum

/-- `s2 + Σ_{j=1..n} (s1 + D1 + … + Dj)`, no reduction. -/
def rfcB (s1 s2 : Nat) (bs : List Byte) : Nat :=
  s2 + ((List.range bs.length).map fun j => rfcA s1 (bs.take (j + 1))).sum

/-- **RFC 1950 Adler-32** of `bs`: `B × 65536 + A` with `A`, `B` reduced mod `65521`. -/
def rfc1950 (bs : List Byte) : Nat := (rfcB 1 0 bs % 65521) * 65536 + rfcA 1 bs % 65521

/-- RFC 1950 Adler-32 continued from the value `a` (`A` from its low, `B` from its high half). -/
def rfcFrom (a : Nat) (bs : List Byte) : Nat :=
  (rfcB (a % 65536) (a / 65536 % 65536) bs % 65521) * 65536 + rfcA (a % 65536) bs % 65521

end Silmaril.X86.Ladder.ZlibChecksums.Rfc1950
