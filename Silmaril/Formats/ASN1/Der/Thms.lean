module

public import Silmaril.Formats.ASN1.Der.Defs
import Silmaril.Proofs.Formats.ASN1.Der

/-!
# DER: the tag-length-value layer, laws

* `identifierOctets_iff`, `lengthOctets_iff`: the transcriptions of X.690
  §8.1.2 and §8.1.3/§10.1 admit exactly the octets of `encodeIdentifier` and
  `encodeLength`; `decodeIdentifier_eq_some` and `decodeLength_eq_some` say the
  readers accept exactly those, followed by anything;
* `derRel_iff`: `derRel` is the graph of `encode` on well-formed values;
* `decode_sound`, `decode_complete`, `decode_encode`, `encode_correct`: the
  decoder and encoder against `derRel`;
* `derRel_functional`, `derRel_deterministic`: the octets determine the value,
  and each value has at most one DER encoding.
-/

@[expose] public section

namespace Silmaril.Formats.ASN1

open Silmaril

/-! ## Identifier and length octets -/

theorem identifierOctets_iff (t : Tag) (c : Bool) (ids : List UInt8) :
    IdentifierOctets t c ids ↔ ids = encodeIdentifier t c :=
  Proofs.Formats.ASN1.identifierOctets_iff t c ids

theorem decodeIdentifier_eq_some {s r : List UInt8} {t : Tag} {c : Bool} :
    decodeIdentifier s = some (t, c, r) ↔ s = encodeIdentifier t c ++ r :=
  Proofs.Formats.ASN1.decodeIdentifier_eq_some

theorem lengthOctets_iff (n : Nat) (lo : List UInt8) :
    LengthOctets n lo ↔ LengthOK n ∧ lo = encodeLength n :=
  Proofs.Formats.ASN1.lengthOctets_iff n lo

theorem decodeLength_eq_some {s r : List UInt8} {n : Nat} :
    decodeLength s = some (n, r) ↔ LengthOK n ∧ s = encodeLength n ++ r :=
  Proofs.Formats.ASN1.decodeLength_eq_some

/-! ## Relation, encoder and decoder -/

theorem derList_iff (s : List UInt8) (vs : List Value) :
    DerList s vs ↔ Value.wfList vs = true ∧ s = encodeList vs :=
  Proofs.Formats.ASN1.derList_iff s vs

/-- `derRel` is the graph of the encoder on well-formed values. -/
theorem derRel_iff (s : List UInt8) (v : Value) : derRel s v ↔ v.wf = true ∧ encode v = s :=
  Proofs.Formats.ASN1.derRel_iff s v

/-- Decoding a well-formed value's encoding gives the value back. -/
theorem decode_encode {v : Value} (h : v.wf = true) : decode (encode v) = some v :=
  Proofs.Formats.ASN1.decode_encode h

/-- The decoder only accepts DER encodings. -/
theorem decode_sound : derRel.DecoderSound decode := Proofs.Formats.ASN1.decode_sound

/-- The decoder accepts every DER encoding. -/
theorem decode_complete : derRel.DecoderComplete decode := Proofs.Formats.ASN1.decode_complete

theorem decode_eq_some_iff {s : List UInt8} {v : Value} : decode s = some v ↔ derRel s v :=
  ⟨decode_sound s v, decode_complete s v⟩

/-- The encoder is correct on well-formed values. -/
theorem encode_correct : derRel.EncoderCorrectOn (fun v => v.wf = true) encode :=
  fun _ hv => (derRel_iff _ _).mpr ⟨hv, rfl⟩

/-- **DER is functional**: the octets determine the value. -/
theorem derRel_functional : derRel.Functional := fun s _ _ h h' =>
  Option.some.inj ((decode_complete s _ h).symm.trans (decode_complete s _ h'))

/-- **DER is deterministic**: a value has at most one encoding. -/
theorem derRel_deterministic : derRel.Deterministic := fun _ _ _ h h' =>
  ((derRel_iff _ _).mp h).2.symm.trans ((derRel_iff _ _).mp h').2

/-- The encoder is injective on well-formed values. -/
theorem encode_injective {v v' : Value} (hv : v.wf = true) (hv' : v'.wf = true)
    (h : encode v = encode v') : v = v' :=
  Option.some.inj ((decode_encode hv).symm.trans (h ▸ decode_encode hv'))

end Silmaril.Formats.ASN1
