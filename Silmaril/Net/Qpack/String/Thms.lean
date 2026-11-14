module

public import Silmaril.Net.Qpack.String.Defs
public import Silmaril.Net.Hpack.Table.Defs
import Silmaril.Proofs.Net.Qpack.String

@[expose] public section

/-!
# QPACK N-bit prefix string literals: theorems

PROVED (standard axioms; proofs in `Silmaril/Proofs/Net/Qpack/String.lean`), RFC 9204 §4.1.2:

* `decodeStringN_encodeStringN`: for every prefix size `1 ≤ n ≤ 8` (the RFC uses `2..8`) and
  caller flag bits `hi` (a multiple of `2^n` below 256), a raw string literal is read back and
  the reader stops exactly after it;
* `encodeStringN_split`: the first octet of the literal lies in `[hi, hi + 2^(n-1))`, so the
  caller's flag bits survive and the Huffman bit is clear (what the instruction and field line
  decoders dispatch on);
* `encodeStringN_eight`, `decodeStringN_eight`: the 8-bit prefix string literal is exactly
  HPACK's string literal (RFC 7541 §5.2, 7-bit length prefix), encoder and decoder.

PLANNED: Huffman-coded literals (`H = 1`, RFC 7541 Appendix B) are rejected by the decoder.
-/

namespace Silmaril.Net.Qpack

open Silmaril.Net.Hpack (ascii encodeString decodeString)

theorem encodeStringN_split {n hi : Nat} (hn1 : 1 ≤ n) (hn8 : n ≤ 8) (hhi : hi % 2 ^ n = 0)
    (hhi' : hi < 256) (s rest : List UInt8) : ∃ b tl, encodeStringN n hi s ++ rest = b :: tl ∧
      hi ≤ b.toNat ∧ b.toNat < hi + 2 ^ (n - 1) ∧ decodeStringN n (b :: tl) = some (s, rest) :=
  Silmaril.Proofs.Net.Qpack.encodeStringN_split hn1 hn8 hhi hhi' s rest

theorem decodeStringN_encodeStringN {n hi : Nat} (hn1 : 1 ≤ n) (hn8 : n ≤ 8)
    (hhi : hi % 2 ^ n = 0) (hhi' : hi < 256) (s rest : List UInt8) :
    decodeStringN n (encodeStringN n hi s ++ rest) = some (s, rest) :=
  Silmaril.Proofs.Net.Qpack.decodeStringN_encodeStringN hn1 hn8 hhi hhi' s rest

theorem encodeStringN_eight (s : List UInt8) : encodeStringN 8 0 s = encodeString s := rfl

theorem decodeStringN_eight (xs : List UInt8) : decodeStringN 8 xs = decodeString xs :=
  Silmaril.Proofs.Net.Qpack.decodeStringN_eight xs

/-- The name of RFC 9204 B.3 (`custom-key`) as a 6-bit prefix literal under `01`. -/
example : encodeStringN 6 0x40 (ascii "custom-key") = 0x4a :: ascii "custom-key" := by
  decide +kernel
/-- A Huffman-coded literal (`H = 1`) is rejected (planned). -/
example : decodeStringN 6 [0x6a, 0x00] = none := by decide +kernel

end Silmaril.Net.Qpack
