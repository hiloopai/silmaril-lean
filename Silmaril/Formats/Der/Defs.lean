module

@[expose] public section

/-!
# DER: the distinguished encoding of ASN.1 values (X.690 §8.1, §8.3, §10)

The first ASN.1 layer that X.509 certificates (RFC 5280), PKCS#1 keys (RFC 8017 App. A), ECDSA
signatures (RFC 3279 §2.2.3, SEC 1) and PKCS#8 need: tag-length-value (TLV) items in their
**distinguished** (DER) form, and non-negative INTEGERs. DER gives every value exactly one
encoding, which signatures rely on (a certificate's signature covers its DER octets, RFC 5280
§4.1.1.3). The reader here is strict, so that property is a theorem: `Der.Thms.decode_sound`
says that whatever it accepts is exactly the encoding of what it returns.

* `natBytes n`: the minimal big-endian octets of `n` (empty for 0), and `natValue`, its inverse
  on octet strings without a leading zero. These are the unsigned integer codec that DER
  lengths, INTEGER contents, RSA moduli and exponents (I2OSP/OS2IP without padding, RFC 8017
  §4) share.
* `Tag`: class (universal, application, context-specific, private), primitive/constructed,
  and a tag number below 31 (the low-tag-number form, X.690 §8.1.2.2). The high-tag-number
  form (§8.1.2.4) is rejected: X.509, PKCS#1 and PKCS#8 use no tag number above 30.
* Lengths (§8.1.3, §10.1): definite only; the short form below 128, otherwise the long form with
  the minimal number of octets (§10.1: "the definite form of length encoding shall be used,
  encoded in the minimum number of octets"). The indefinite form (0x80) and the reserved 0xFF are
  rejected.
* `Tlv`: an item, `encode`/`decode`, and `decodeAll` for the contents of a constructed item.
* INTEGER (§8.3): two's complement in the minimal number of octets (§8.3.2: the first nine bits
  are not all zero or all one). `encodeNat`/`decodeNat` cover the non-negative values, which are
  all X.509 serial numbers (RFC 5280 §4.1.2.2: "MUST be a positive integer") and RSA/ECDSA
  integers. A negative INTEGER is read as `none` by `decodeNat`.

Not covered yet (docs/projects/crypto.md, milestone X1): OBJECT IDENTIFIER, BIT STRING, the
string and time types, negative INTEGERs, and a schema layer for X.509 itself.

This module imports only Lean core.
-/

namespace Silmaril.Formats.Der

/-! ## Unsigned integers in the minimal number of octets -/

/-- The value of big-endian octets. -/
def natValue (xs : List UInt8) : Nat := xs.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- Minimal big-endian octets with explicit fuel (structural, so the kernel evaluates it). -/
def natBytesAux : Nat → Nat → List UInt8
  | 0, _ => []
  | fuel + 1, n => if n = 0 then [] else natBytesAux fuel (n / 256) ++ [(n % 256).toUInt8]

/-- The minimal big-endian octets of `n`: no leading zero octet, empty for 0. -/
def natBytes (n : Nat) : List UInt8 := natBytesAux n n

/-- Octets without a leading zero (the image of `natBytes`). -/
def Minimal (xs : List UInt8) : Prop := xs.head? ≠ some 0

instance (xs : List UInt8) : Decidable (Minimal xs) := by unfold Minimal; infer_instance

/-! ## Identifiers -/

/-- An identifier in the low-tag-number form. -/
structure Tag where
  /-- 0 universal, 1 application, 2 context-specific, 3 private. -/
  cls : Nat
  constructed : Bool
  number : Nat
  deriving DecidableEq, Repr

def Tag.Valid (t : Tag) : Prop := t.cls < 4 ∧ t.number < 31

instance (t : Tag) : Decidable t.Valid := by unfold Tag.Valid; infer_instance

/-- The identifier octet (§8.1.2.2). -/
def Tag.byte (t : Tag) : UInt8 := (t.cls * 64 + t.constructed.toNat * 32 + t.number).toUInt8

/-- Read an identifier octet; `none` for the high-tag-number form. -/
def Tag.ofByte (b : UInt8) : Option Tag :=
  if b.toNat % 32 = 31 then none
  else some ⟨b.toNat / 64, b.toNat / 32 % 2 == 1, b.toNat % 32⟩

/-- Universal tags used by X.509 (X.680 §8.6). -/
def tagInteger : Tag := ⟨0, false, 2⟩
def tagBitString : Tag := ⟨0, false, 3⟩
def tagOctetString : Tag := ⟨0, false, 4⟩
def tagNull : Tag := ⟨0, false, 5⟩
def tagOid : Tag := ⟨0, false, 6⟩
def tagSequence : Tag := ⟨0, true, 16⟩
def tagSet : Tag := ⟨0, true, 17⟩
/-- `[n]` EXPLICIT, as in `version [0] EXPLICIT Version` (RFC 5280 §4.1). -/
def tagContext (n : Nat) : Tag := ⟨2, true, n⟩

/-! ## Lengths (§8.1.3, §10.1) -/

/-- The largest length this codec writes: the long form has at most 126 length octets. -/
def maxLength : Nat := 256 ^ 126

/-- The length octets. -/
def encodeLength (n : Nat) : List UInt8 :=
  if n < 128 then [n.toUInt8] else (0x80 + (natBytes n).length).toUInt8 :: natBytes n

/-- Why a reader stops. -/
inductive Error where
  | truncated
  /-- The indefinite form, 0xFF, or a long form that is not minimal (§10.1). -/
  | badLength
  /-- The high-tag-number form. -/
  | highTag
  /-- Contents that break the type's rules (§8.3.2 for INTEGER). -/
  | badContents
  deriving DecidableEq, Repr

/-- Read the length octets. -/
def decodeLength : List UInt8 → Except Error (Nat × List UInt8)
  | [] => .error .truncated
  | b :: rest =>
    if b.toNat < 128 then .ok (b.toNat, rest)
    else
      let k := b.toNat - 128
      if k = 0 ∨ k = 127 then .error .badLength
      else if rest.length < k then .error .truncated
      else
        let bs := rest.take k
        if bs.head? = some 0 ∨ natValue bs < 128 then .error .badLength
        else .ok (natValue bs, rest.drop k)

/-! ## Items -/

/-- A TLV item: identifier and contents. -/
structure Tlv where
  tag : Tag
  contents : List UInt8
  deriving DecidableEq, Repr

def Tlv.Valid (x : Tlv) : Prop := x.tag.Valid ∧ x.contents.length < maxLength

instance (x : Tlv) : Decidable x.Valid := by unfold Tlv.Valid; infer_instance

/-- The DER octets of an item. -/
def encode (x : Tlv) : List UInt8 := x.tag.byte :: (encodeLength x.contents.length ++ x.contents)

/-- Read one item at the front of the input. -/
def decode : List UInt8 → Except Error (Tlv × List UInt8)
  | [] => .error .truncated
  | b :: rest =>
    match Tag.ofByte b with
    | none => .error .highTag
    | some t =>
      match decodeLength rest with
      | .error e => .error e
      | .ok (n, body) =>
        if body.length < n then .error .truncated
        else .ok (⟨t, body.take n⟩, body.drop n)

/-- Read a sequence of items that fills the input (the contents of a constructed item). -/
def decodeAll : Nat → List UInt8 → Except Error (List Tlv)
  | _, [] => .ok []
  | 0, _ => .error .truncated
  | fuel + 1, xs =>
    match decode xs with
    | .error e => .error e
    | .ok (x, rest) => match decodeAll fuel rest with
      | .error e => .error e
      | .ok xs => .ok (x :: xs)

/-! ## Non-negative INTEGERs (§8.3) -/

/-- The contents of a non-negative INTEGER: minimal two's complement, so a zero octet is added
when the top bit of the first octet is set, and 0 is one zero octet. -/
def encodeNatContents (n : Nat) : List UInt8 :=
  match natBytes n with
  | [] => [0]
  | b :: bs => if b.toNat < 128 then b :: bs else 0 :: b :: bs

/-- Read the contents of a non-negative INTEGER: `none` if empty, negative, or not minimal. -/
def decodeNatContents : List UInt8 → Option Nat
  | [] => none
  | [b] => if b.toNat < 128 then some b.toNat else none
  | b :: c :: rest =>
    if 128 ≤ b.toNat then none
    else if b = 0 ∧ c.toNat < 128 then none
    else some (natValue (b :: c :: rest))

/-- An INTEGER item. -/
def encodeNat (n : Nat) : List UInt8 := encode ⟨tagInteger, encodeNatContents n⟩

/-- Read an INTEGER item with a non-negative value. -/
def decodeNat (xs : List UInt8) : Except Error (Nat × List UInt8) :=
  match decode xs with
  | .error e => .error e
  | .ok (x, rest) =>
    if x.tag ≠ tagInteger then .error .badContents
    else match decodeNatContents x.contents with
      | some n => .ok (n, rest)
      | none => .error .badContents

end Silmaril.Formats.Der
