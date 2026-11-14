module

public import Silmaril.Encoding.Relation
public import Silmaril.Formats.ASN1.Digits.Defs
public import Silmaril.Formats.ASN1.Value.Defs

/-!
# DER: the tag-length-value layer (X.690 §8.1, §10.1)

`derRel : EncRel (List UInt8) Value` transcribes the type-independent part of
the Distinguished Encoding Rules:

* identifier octets (§8.1.2): the class bits, the constructed bit (`Value.cons`
  versus `Value.prim`) and the tag number, in a single octet for numbers below
  31 and otherwise in the minimal base-128 high-tag-number form;
* length octets (§8.1.3, §10.1): definite form only, in the minimum number of
  octets: the short form below 128, otherwise the long form with no leading
  zero octet and at most 126 subsequent octets (§8.1.3.5 c reserves `0xFF`);
* contents octets: the contents of a primitive value, or the concatenated
  encodings of the children of a constructed one;
* the end-of-contents tag `[UNIVERSAL 0]` does not occur (no indefinite
  lengths, §10.1).

Restrictions that depend on the type (primitive form for the string types,
§10.2; BOOLEAN and INTEGER contents; SET OF ordering) are enforced by the typed
views in `Universal` and `Codec`, not here.

The executable side is the encoder `encode` (defined on values with
`Value.wf`) and the decoder `decode`; `Silmaril.Formats.ASN1.Der.Thms` proves
that `derRel` is exactly the graph of `encode` on well-formed values and that
`decode` is sound and complete for it.
-/

@[expose] public section

namespace Silmaril.Formats.ASN1

open Silmaril

/-! ## Identifier octets -/

/-- The leading identifier octet: class bits, constructed bit, and the low
five bits `k` (the tag number, or 31 for the high-tag-number form). -/
def leadOctet (cls : TagClass) (constructed : Bool) (k : Nat) : UInt8 :=
  (cls.bits * 64 + (if constructed then 32 else 0) + k).toUInt8

/-- X.690 §8.1.2, transcribed. -/
inductive IdentifierOctets : Tag → Bool → List UInt8 → Prop
  /-- §8.1.2.2–3: tag numbers 0..30 use a single octet. -/
  | low {t : Tag} {c : Bool} : t.number < 31 →
      IdentifierOctets t c [leadOctet t.cls c t.number]
  /-- §8.1.2.4: larger tag numbers follow a leading octet whose bits 5..1 are
  set, in minimal base 128. -/
  | high {t : Tag} {c : Bool} {ds : List UInt8} : 31 ≤ t.number → Base128Octets t.number ds →
      IdentifierOctets t c (leadOctet t.cls c 31 :: ds)

/-- The identifier octets of a tag. -/
def encodeIdentifier (t : Tag) (constructed : Bool) : List UInt8 :=
  if t.number < 31 then [leadOctet t.cls constructed t.number]
  else leadOctet t.cls constructed 31 :: base128 t.number

/-- Read identifier octets: tag, constructed bit, remaining input. A high-form
tag number below 31 is rejected. -/
def decodeIdentifier : List UInt8 → Option (Tag × Bool × List UInt8)
  | [] => none
  | b :: r =>
      let cls := TagClass.ofBits (b.toNat / 64)
      let c := decide (b.toNat / 32 % 2 = 1)
      let k := b.toNat % 32
      if k < 31 then some (⟨cls, k⟩, c, r)
      else
        match readBase128 r with
        | some (n, r') => if 31 ≤ n then some (⟨cls, n⟩, c, r') else none
        | none => none

/-! ## Length octets -/

/-- A length has DER length octets: the long form has at most 126 subsequent
octets (§8.1.3.5 c). -/
def LengthOK (n : Nat) : Prop := n < 128 ∨ (beBytes n).length ≤ 126

instance (n : Nat) : Decidable (LengthOK n) := inferInstanceAs (Decidable (_ ∨ _))

/-- X.690 §8.1.3 with the DER restriction of §10.1, transcribed. -/
inductive LengthOctets : Nat → List UInt8 → Prop
  /-- §8.1.3.4: the short form, for lengths up to 127. -/
  | short {n : Nat} : n < 128 → LengthOctets n [n.toUInt8]
  /-- §8.1.3.5: the long form with 1..126 subsequent octets; minimal (§10.1):
  no leading zero octet, and only for lengths of 128 and above. -/
  | long {bs : List UInt8} : bs ≠ [] → bs.length ≤ 126 → bs.head? ≠ some 0 → 128 ≤ beNat bs →
      LengthOctets (beNat bs) ((128 + bs.length).toUInt8 :: bs)

/-- The definite length octets of `n`, in the minimum number of octets. -/
def encodeLength (n : Nat) : List UInt8 :=
  if n < 128 then [n.toUInt8] else (128 + (beBytes n).length).toUInt8 :: beBytes n

/-- Read definite, minimal length octets. The indefinite form `0x80`, the
reserved `0xFF`, non-minimal long forms and truncated input are rejected. -/
def decodeLength : List UInt8 → Option (Nat × List UInt8)
  | [] => none
  | b :: r =>
      if b.toNat < 128 then some (b.toNat, r)
      else
        let k := b.toNat - 128
        if k = 0 ∨ 126 < k ∨ r.length < k then none
        else
          let bs := r.take k
          if bs.head? = some 0 ∨ beNat bs < 128 then none else some (beNat bs, r.drop k)

/-! ## The relation -/

/-- `DerList s vs`: `s` is the concatenation of the DER encodings of `vs`
(X.690 §8.1.1 with the identifier and length rules above). -/
inductive DerList : List UInt8 → List Value → Prop
  | nil : DerList [] []
  | prim {t : Tag} {ids lo b rest : List UInt8} {vs : List Value} :
      IdentifierOctets t false ids → LengthOctets b.length lo → t ≠ Tag.eoc → DerList rest vs →
      DerList (ids ++ lo ++ b ++ rest) (.prim t b :: vs)
  | cons {t : Tag} {ids lo c rest : List UInt8} {kids vs : List Value} :
      IdentifierOctets t true ids → LengthOctets c.length lo → t ≠ Tag.eoc → DerList c kids →
      DerList rest vs → DerList (ids ++ lo ++ c ++ rest) (.cons t kids :: vs)

/-- DER as an encoding relation: `s` is the DER encoding of the single value
`v`. -/
def derRel : EncRel (List UInt8) Value := fun s v => DerList s [v]

/-! ## The encoder -/

mutual
/-- The DER encoding of a value tree. -/
def encode : Value → List UInt8
  | .prim t b => encodeIdentifier t false ++ encodeLength b.length ++ b
  | .cons t vs => encodeIdentifier t true ++ encodeLength (encodeList vs).length ++ encodeList vs

/-- The concatenated encodings of a list of values. -/
def encodeList : List Value → List UInt8
  | [] => []
  | v :: vs => encode v ++ encodeList vs
end

mutual
/-- A value tree has a DER encoding: no end-of-contents tag, and every contents
length fits the long form. -/
def Value.wf : Value → Bool
  | .prim t b => decide (t ≠ Tag.eoc) && decide (LengthOK b.length)
  | .cons t vs =>
      decide (t ≠ Tag.eoc) && decide (LengthOK (encodeList vs).length) && Value.wfList vs

/-- Every value of the list is well formed. -/
def Value.wfList : List Value → Bool
  | [] => true
  | v :: vs => v.wf && Value.wfList vs
end

/-! ## The decoder -/

mutual
/-- Decode one TLV from the front of the input. `fuel` bounds the recursion;
the input length suffices. -/
def decodeTLV : Nat → List UInt8 → Option (Value × List UInt8)
  | 0, _ => none
  | fuel + 1, s =>
      match decodeIdentifier s with
      | none => none
      | some (t, c, s₁) =>
          match decodeLength s₁ with
          | none => none
          | some (n, s₂) =>
              if s₂.length < n ∨ t = Tag.eoc then none
              else if c then
                match decodeSeq fuel (s₂.take n) with
                | some vs => some (.cons t vs, s₂.drop n)
                | none => none
              else some (.prim t (s₂.take n), s₂.drop n)

/-- Decode the whole input as a sequence of TLVs. -/
def decodeSeq : Nat → List UInt8 → Option (List Value)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, s@(_ :: _) =>
      match decodeTLV fuel s with
      | none => none
      | some (v, r) =>
          match decodeSeq fuel r with
          | some vs => some (v :: vs)
          | none => none
end

/-- Decode a complete DER encoding of one value; trailing octets are
rejected. -/
def decode (s : List UInt8) : Option Value :=
  match decodeTLV s.length s with
  | some (v, []) => some v
  | _ => none

end Silmaril.Formats.ASN1
