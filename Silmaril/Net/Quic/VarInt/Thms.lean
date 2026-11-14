module

public import Silmaril.Net.Quic.VarInt.Defs
import Silmaril.Proofs.Net.Quic.VarInt

@[expose] public section

/-!
# QUIC variable-length integers: theorems

PROVED (standard axioms; proofs in `Silmaril/Proofs/Net/Quic/VarInt.lean`):

* `decode_encode`: every `v ≤ 2^62 - 1` round trips through the shortest encoding, and the
  reader stops exactly where the encoding ends;
* `decode_encodeWith`: every permitted (possibly non-minimal) length round trips too, as
  RFC 9000 §16 requires of receivers;
* `encode_length`: the encoding has `lenOf v ∈ {1, 2, 4, 8}` bytes;
* `decode_valid`: whatever is decoded is at most `2^62 - 1`;
* `decode_local`, `decode_suffix`, `decode_length`: a decoded integer is a self-delimiting
  prefix: appended bytes are passed through and at least one byte is consumed;
* `decodeAll_flatMap`: concatenated encodings decode back to the list of values.

CHECKED: the four sample encodings of RFC 9000 Appendix A.1, including the non-minimal
two-byte encoding of 37.
-/

namespace Silmaril.Net.Quic.VarInt

theorem decode_encodeWith {k v : Nat} (h : FitsIn k v) (rest : List UInt8) :
    decode (encodeWith k v ++ rest) = some (v, rest) :=
  Silmaril.Proofs.Net.Quic.VarInt.decode_encodeWith h rest

theorem lenOf_fits {v : Nat} (h : Valid v) : FitsIn (lenOf v) v :=
  Silmaril.Proofs.Net.Quic.VarInt.lenOf_fits h

theorem decode_encode {v : Nat} (h : Valid v) (rest : List UInt8) :
    decode (encode v ++ rest) = some (v, rest) :=
  Silmaril.Proofs.Net.Quic.VarInt.decode_encode h rest

theorem lenOf_mem (v : Nat) : lenOf v ∈ lengths := Silmaril.Proofs.Net.Quic.VarInt.lenOf_mem v

theorem encode_length (v : Nat) : (encode v).length = lenOf v :=
  Silmaril.Proofs.Net.Quic.VarInt.encode_length v

theorem encode_ne_nil (v : Nat) : encode v ≠ [] := by simp [encode, encodeWith]

theorem decode_valid {xs : List UInt8} {v : Nat} {rest : List UInt8}
    (h : decode xs = some (v, rest)) : Valid v :=
  Silmaril.Proofs.Net.Quic.VarInt.decode_valid h

theorem decode_local {xs : List UInt8} {v : Nat} {rest : List UInt8} (tail : List UInt8)
    (h : decode xs = some (v, rest)) : decode (xs ++ tail) = some (v, rest ++ tail) :=
  Silmaril.Proofs.Net.Quic.VarInt.decode_local tail h

theorem decode_suffix {xs : List UInt8} {v : Nat} {rest : List UInt8}
    (h : decode xs = some (v, rest)) : rest <:+ xs :=
  Silmaril.Proofs.Net.Quic.VarInt.decode_suffix h

theorem decode_length {xs : List UInt8} {v : Nat} {rest : List UInt8}
    (h : decode xs = some (v, rest)) : rest.length < xs.length :=
  Silmaril.Proofs.Net.Quic.VarInt.decode_length h

theorem decodeAll_flatMap (vs : List Nat) (hv : ∀ v ∈ vs, Valid v) :
    decodeAll (vs.flatMap encode) = some vs :=
  Silmaril.Proofs.Net.Quic.VarInt.decodeAll_flatMap vs hv

/-! ## RFC 9000 Appendix A.1 sample encodings -/

theorem sample_eight :
    decode [0xc2, 0x19, 0x7c, 0x5e, 0xff, 0x14, 0xe8, 0x8c] = some (151288809941952652, []) := by
  rfl

theorem sample_four : decode [0x9d, 0x7f, 0x3e, 0x7d] = some (494878333, []) := by rfl

theorem sample_two : decode [0x7b, 0xbd] = some (15293, []) := by rfl

theorem sample_one : decode [0x25] = some (37, []) := by rfl

/-- "the same value [37] could also be decoded from the two-byte sequence 0x4025". -/
theorem sample_two_nonminimal : decode [0x40, 0x25] = some (37, []) := by rfl

theorem encode_samples :
    encode 151288809941952652 = [0xc2, 0x19, 0x7c, 0x5e, 0xff, 0x14, 0xe8, 0x8c] ∧
      encode 494878333 = [0x9d, 0x7f, 0x3e, 0x7d] ∧ encode 15293 = [0x7b, 0xbd] ∧
      encode 37 = [0x25] ∧ encodeWith 2 37 = [0x40, 0x25] := by
  refine ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- A truncated encoding is rejected rather than read short. -/
theorem truncated : decode [0x9d, 0x7f, 0x3e] = none := by rfl

end Silmaril.Net.Quic.VarInt
