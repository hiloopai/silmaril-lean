module

public import Silmaril.Formats.Der.Defs
import Silmaril.Proofs.Formats.Der

@[expose] public section

/-!
# DER: theorems

PROVED (standard axioms; proofs in `Silmaril/Proofs/Formats/Der.lean`):

* **Minimal unsigned integers.** `natValue_natBytes` and `natBytes_natValue`: `natBytes` and
  `natValue` are inverse between numbers and octet strings without a leading zero. Also
  `minimal_natBytes`, `natValue_lt`, `natValue_ge` (a minimal string's value has exactly its
  length in octets) and `length_natBytes_le`.
* **Lengths** (X.690 §10.1). `decodeLength_encodeLength` is the round trip. `decodeLength_sound`:
  the reader accepts only the minimal definite form.
* **Items.** `decode_encode`: every valid item is read back from any stream it starts.
  `decode_sound` (**distinguished encoding**): whatever the reader accepts is exactly the DER
  encoding of the item it returns. `encode_injective` follows. Together they make DER octets and
  items interchangeable, which is what a signature over DER octets needs (RFC 5280 §4.1.1.3).
* **Non-negative INTEGERs** (§8.3.2). `decodeNatContents_encodeNatContents` and
  `decodeNatContents_sound` give the same bijection for minimal two's complement contents.
  `decodeNat_encodeNat` is the round trip for INTEGER items.

CHECKED (`decide +kernel`): X.690 length and INTEGER examples, and the ISRG Root X2 certificate
(`Der.Examples`).
-/

namespace Silmaril.Formats.Der

theorem natValue_natBytes (n : Nat) : natValue (natBytes n) = n :=
  Silmaril.Proofs.Formats.Der.natValue_natBytes n

theorem natBytes_natValue {xs : List UInt8} (hm : Minimal xs) : natBytes (natValue xs) = xs :=
  Silmaril.Proofs.Formats.Der.natBytes_natValue hm

theorem minimal_natBytes (n : Nat) : Minimal (natBytes n) :=
  Silmaril.Proofs.Formats.Der.minimal_natBytes n

theorem natBytes_eq_nil (n : Nat) : natBytes n = [] ↔ n = 0 :=
  Silmaril.Proofs.Formats.Der.natBytes_eq_nil n

theorem natValue_lt (xs : List UInt8) : natValue xs < 256 ^ xs.length :=
  Silmaril.Proofs.Formats.Der.natValue_lt xs

theorem natValue_ge {xs : List UInt8} (hm : Minimal xs) (hne : xs ≠ []) :
    256 ^ (xs.length - 1) ≤ natValue xs :=
  Silmaril.Proofs.Formats.Der.natValue_ge hm hne

theorem length_natBytes_le {n k : Nat} (h : n < 256 ^ k) : (natBytes n).length ≤ k :=
  Silmaril.Proofs.Formats.Der.length_natBytes_lt h

theorem decodeLength_encodeLength (n : Nat) (hn : n < maxLength) (rest : List UInt8) :
    decodeLength (encodeLength n ++ rest) = .ok (n, rest) :=
  Silmaril.Proofs.Formats.Der.decodeLength_encodeLength n hn rest

theorem decodeLength_sound {xs rest : List UInt8} {n : Nat}
    (h : decodeLength xs = .ok (n, rest)) : n < maxLength ∧ xs = encodeLength n ++ rest :=
  Silmaril.Proofs.Formats.Der.decodeLength_sound h

theorem ofByte_byte (t : Tag) (hv : t.Valid) : Tag.ofByte t.byte = some t :=
  Silmaril.Proofs.Formats.Der.ofByte_byte t hv

theorem decode_encode (x : Tlv) (hv : x.Valid) (rest : List UInt8) :
    decode (encode x ++ rest) = .ok (x, rest) :=
  Silmaril.Proofs.Formats.Der.decode_encode x hv rest

theorem decode_sound {xs rest : List UInt8} {x : Tlv} (h : decode xs = .ok (x, rest)) :
    x.Valid ∧ xs = encode x ++ rest :=
  Silmaril.Proofs.Formats.Der.decode_sound h

/-- Two valid items with the same DER octets are equal. -/
theorem encode_injective {x y : Tlv} (hx : x.Valid) (hy : y.Valid) (h : encode x = encode y) :
    x = y := by
  have e := decode_encode x hx []
  rw [h, decode_encode y hy] at e
  cases e; rfl

theorem decodeNatContents_encodeNatContents (n : Nat) :
    decodeNatContents (encodeNatContents n) = some n :=
  Silmaril.Proofs.Formats.Der.decodeNatContents_encodeNatContents n

theorem decodeNatContents_sound {c : List UInt8} {n : Nat} (h : decodeNatContents c = some n) :
    encodeNatContents n = c :=
  Silmaril.Proofs.Formats.Der.decodeNatContents_sound h

theorem decodeNat_encodeNat (n : Nat) (hn : n < 256 ^ 125) (rest : List UInt8) :
    decodeNat (encodeNat n ++ rest) = .ok (n, rest) := by
  have hl : (encodeNatContents n).length < maxLength := by
    have h1 := Silmaril.Proofs.Formats.Der.length_encodeNatContents n
    have h2 := length_natBytes_le hn
    have : 126 < maxLength := Nat.lt_of_lt_of_le (by decide) (Nat.le_self_pow (by decide) 256)
    have : (encodeNatContents n).length ≤ 126 := by omega
    unfold maxLength at *
    exact Nat.lt_of_le_of_lt this (by decide)
  unfold decodeNat encodeNat
  rw [decode_encode _ ⟨(by decide : tagInteger.Valid), hl⟩]
  simp [decodeNatContents_encodeNatContents]

/-! ## X.690 examples -/

/-- Lengths: 38 is short form, 201 is `81 C9`, 435 is `82 01 B3` (X.690 §8.1.3). -/
example : encodeLength 38 = [0x26] ∧ encodeLength 201 = [0x81, 0xc9] ∧
    encodeLength 435 = [0x82, 0x01, 0xb3] := by
  decide +kernel

/-- A non-minimal long form and the indefinite form are rejected (§10.1). -/
def isBadLength (r : Except Error (Nat × List UInt8)) : Bool :=
  match r with
  | .error .badLength => true
  | _ => false

example : (isBadLength (decodeLength [0x81, 0x26]) && isBadLength (decodeLength [0x82, 0x00, 0xc9])
    && isBadLength (decodeLength [0x80])) = true := by
  decide +kernel

/-- INTEGERs: 0, 127, 128 (needs a leading zero), 256. -/
example : encodeNat 0 = [0x02, 0x01, 0x00] ∧ encodeNat 127 = [0x02, 0x01, 0x7f] ∧
    encodeNat 128 = [0x02, 0x02, 0x00, 0x80] ∧ encodeNat 256 = [0x02, 0x02, 0x01, 0x00] := by
  decide +kernel

/-- Non-minimal and negative INTEGER contents are rejected (§8.3.2). -/
example : decodeNatContents [0x00, 0x7f] = none ∧ decodeNatContents [0x80] = none ∧
    decodeNatContents [] = none := by
  decide +kernel

end Silmaril.Formats.Der
