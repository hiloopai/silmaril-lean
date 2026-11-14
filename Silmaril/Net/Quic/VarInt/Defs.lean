module

public import Silmaril.Net.Wire.Defs

@[expose] public section

/-!
# QUIC variable-length integers (RFC 9000 §16)

"QUIC packets and frames commonly use a variable-length encoding for non-negative integer
values. … The QUIC variable-length integer encoding reserves the two most significant bits
of the first byte to encode the base-2 logarithm of the integer encoding length in bytes. The
integer value is encoded on the remaining bits, in network byte order." (RFC 9000 §16)

| 2MSB | Length | Usable bits | Range |
| --- | --- | --- | --- |
| 00 | 1 | 6 | 0–63 |
| 01 | 2 | 14 | 0–16383 |
| 10 | 4 | 30 | 0–1073741823 |
| 11 | 8 | 62 | 0–4611686018427387903 |

HTTP/3 (RFC 9114 §7.1), QPACK's encoder/decoder streams (RFC 9204 §4.2 stream types), the
HTTP Capsule Protocol (RFC 9297 §3.2) and WebTransport over HTTP/3 all reuse this encoding,
so it lives here, independent of the rest of the QUIC model.

* `lenOf v`: the length `encode` picks, the shortest one (`1, 2, 4, 8`);
* `encodeWith k v`: the encoding of `v` on exactly `k` bytes (`k ∈ {1,2,4,8}`), with the
  length prefix; §16 allows any length that fits ("values do not need to be encoded on the
  minimum number of bytes necessary"), so the decoder accepts all of them;
* `encode v = encodeWith (lenOf v) v`, `decode`: read one integer at the front of the input
  and return the rest; `none` when the input is shorter than the announced length.

Values are unbounded `Nat`s; `maxValue = 2^62 - 1` is the largest encodable one and `Valid v` is
`v ≤ maxValue`. Only RFC 9000 §16 is modelled here; the rest of QUIC is in `Silmaril.Net.Quic`'s
other topics (see `docs/projects/http3.md` for what is modelled and what is assumed).
-/

namespace Silmaril.Net.Quic.VarInt

open Silmaril.Net.Wire (beBytes)

/-- The largest variable-length integer, `2^62 - 1` (RFC 9000 §16). -/
def maxValue : Nat := 2 ^ 62 - 1

/-- A value the encoding can carry. -/
def Valid (v : Nat) : Prop := v ≤ maxValue

instance (v : Nat) : Decidable (Valid v) := inferInstanceAs (Decidable (v ≤ maxValue))

/-! `beBytes k x`, the big-endian octets of `x` in `k` octets, is `Net.Wire.beBytes`. -/

/-- The big-endian value of octets, added to `acc * 256^|xs|`. -/
def beValueFrom (acc : Nat) (xs : List UInt8) : Nat := xs.foldl (fun a b => a * 256 + b.toNat) acc

/-- The two-bit length prefix of an encoding length (`1 ↦ 0, 2 ↦ 1, 4 ↦ 2, 8 ↦ 3`). -/
def prefixOf : Nat → Nat
  | 1 => 0
  | 2 => 1
  | 4 => 2
  | _ => 3

/-- The encoding length announced by a two-bit prefix: `2^p`. -/
def lengthOfPrefix (p : Nat) : Nat := 2 ^ (p % 4)

/-- The encoding lengths RFC 9000 §16 defines. -/
def lengths : List Nat := [1, 2, 4, 8]

/-- The shortest encoding length for `v` (values above `maxValue` get 8 and do not fit). -/
def lenOf (v : Nat) : Nat :=
  if v < 2 ^ 6 then 1 else if v < 2 ^ 14 then 2 else if v < 2 ^ 30 then 4 else 8

/-- `v` fits in an encoding of `k` bytes: `v < 2^(8k - 2)`. -/
def FitsIn (k v : Nat) : Prop := k ∈ lengths ∧ v < 64 * 256 ^ (k - 1)

/-- The encoding of `v` on exactly `k` bytes: the prefix and the top six value bits, then the
remaining `k - 1` bytes big-endian. -/
def encodeWith (k v : Nat) : List UInt8 :=
  (prefixOf k * 64 + v / 256 ^ (k - 1) % 64).toUInt8 :: beBytes (k - 1) v

/-- The shortest encoding of `v` (RFC 9000 §16; the sample encoder of Appendix A.1 instead
always matches the given length). -/
def encode (v : Nat) : List UInt8 := encodeWith (lenOf v) v

/-- Read one variable-length integer at the front of the input (RFC 9000 Appendix A.1). -/
def decode : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | b :: rest =>
    let k := lengthOfPrefix (b.toNat / 64)
    if rest.length < k - 1 then none
    else some (beValueFrom (b.toNat % 64) (rest.take (k - 1)), rest.drop (k - 1))

/-- Read `n` variable-length integers in a row. -/
def decodeMany : Nat → List UInt8 → Option (List Nat × List UInt8)
  | 0, xs => some ([], xs)
  | n + 1, xs =>
    match decode xs with
    | none => none
    | some (v, rest) =>
      match decodeMany n rest with
      | none => none
      | some (vs, rest') => some (v :: vs, rest')

/-- Read variable-length integers until the input is used up (for SETTINGS-like payloads).
Each integer consumes at least one byte, so the length is enough fuel. -/
def decodeAllFuel : Nat → List UInt8 → Option (List Nat)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, xs@(_ :: _) =>
    match decode xs with
    | none => none
    | some (v, rest) => (decodeAllFuel fuel rest).map (v :: ·)

/-- Read variable-length integers filling the whole input. -/
def decodeAll (xs : List UInt8) : Option (List Nat) := decodeAllFuel xs.length xs

end Silmaril.Net.Quic.VarInt
