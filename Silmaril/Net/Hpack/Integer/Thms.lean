module

public import Silmaril.Net.Hpack.Integer.Defs
import Silmaril.Proofs.Net.Hpack.Integer

@[expose] public section

/-!
# HPACK integers and string literals: theorems

PROVED (standard axioms; proofs in `Silmaril/Proofs/Net/Hpack/Integer.lean`):

* `decodeInt_encodeInt`: for a prefix of `n ≤ 8` bits and flag bits `hi` (a multiple of `2^n`
  below 256), the integer read back from `encodeInt n hi i ++ rest` is `i`, and the reader
  stops exactly at `rest` (RFC 7541 §5.1; every natural, no size bound);
* `flags_encodeInt_head`: the first octet of the encoding carries the flag bits `hi`, so a
  decoder that dispatches on them (RFC 7541 §6) sees the caller's representation type;
* `decodeRest_encodeRest`: the continuation octets alone;
* `decodeString_encodeString`: raw string literals round trip (RFC 7541 §5.2, `H = 0`).
-/

namespace Silmaril.Net.Hpack

theorem decodeRest_encodeRest (i : Nat) (rest : List UInt8) :
    decodeRest (encodeRest i ++ rest) = some (i, rest) :=
  Silmaril.Proofs.Net.Hpack.decodeRest_encodeRest i rest

theorem decodeInt_encodeInt {n hi : Nat} (hn8 : n ≤ 8) (hhi : hi % 2 ^ n = 0) (hhi' : hi < 256)
    (i : Nat) (rest : List UInt8) :
    decodeInt n (encodeInt n hi i ++ rest) = some (i, rest) :=
  Silmaril.Proofs.Net.Hpack.decodeInt_encodeInt hn8 hhi hhi' i rest

theorem flags_encodeInt_head {n hi : Nat} (hn8 : n ≤ 8) (hhi : hi % 2 ^ n = 0) (hhi' : hi < 256)
    (i : Nat) : ∃ b tl, encodeInt n hi i = b :: tl ∧ flags n b = hi :=
  Silmaril.Proofs.Net.Hpack.flags_encodeInt_head hn8 hhi hhi' i

theorem decodeString_encodeString (s rest : List UInt8) :
    decodeString (encodeString s ++ rest) = some (s, rest) :=
  Silmaril.Proofs.Net.Hpack.decodeString_encodeString s rest

/-! RFC 7541 Appendix C.1, checked by evaluation. -/

/-- C.1.1: 10 with a 5-bit prefix is one octet. -/
example : encodeInt 5 0 10 = [0x0a] := by decide +kernel
/-- C.1.2: 1337 with a 5-bit prefix is `1f 9a 0a`. -/
example : encodeInt 5 0 1337 = [0x1f, 0x9a, 0x0a] := by decide +kernel
/-- C.1.3: 42 at an octet boundary (8-bit prefix). -/
example : encodeInt 8 0 42 = [0x2a] := by decide +kernel
example : decodeInt 5 [0xff, 0x9a, 0x0a] = some (1337, []) := by decide +kernel

end Silmaril.Net.Hpack
