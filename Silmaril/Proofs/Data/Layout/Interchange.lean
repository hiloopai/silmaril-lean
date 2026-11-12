module

public import Silmaril.Data.Layout.Interchange.Defs

/-!
# Proofs: the v1 report codec round-trips at the JSON-tree level

`unitsString? (stringUnits s) = some s` for every string (UTF-16 encoding followed by
decoding is the identity on Unicode scalar values), and from it `decode (encode r) = .ok r`
for every report.
-/

@[expose] public section

namespace Silmaril.Proofs.Data.Layout.Interchange

open Silmaril.Data.Layout Silmaril.Data.Layout.Record Silmaril.Data.Layout.Interchange
open Silmaril.Formats.JsonWire

theorem char_valid (c : Char) :
    c.toNat < 0xd800 ∨ (0xdfff < c.toNat ∧ c.toNat < 0x110000) := c.valid

theorem unitsChars?_charUnits (c : Char) (us : Units) :
    unitsChars? (charUnits c ++ us) = (unitsChars? us).map (c :: ·) := by
  have hv := char_valid c
  unfold charUnits
  split
  · rename_i hlt
    have hu : (UInt16.ofNat c.toNat).toNat = c.toNat :=
      UInt16.toNat_ofNat_of_lt' (by simp [UInt16.size]; omega)
    rw [List.singleton_append]
    conv_lhs => rw [unitsChars?.eq_def]
    simp only [hu]
    have h1 : ¬ (0xD800 ≤ c.toNat ∧ c.toNat ≤ 0xDBFF) := by omega
    have h2 : ¬ (0xDC00 ≤ c.toNat ∧ c.toNat ≤ 0xDFFF) := by omega
    simp only [Bool.and_eq_true, decide_eq_true_eq, h1, h2, ite_false, Char.ofNat_toNat]
    cases unitsChars? us <;> rfl
  · rename_i hge
    have hn : c.toNat - 0x10000 < 0x100000 := by omega
    have hu : (UInt16.ofNat (0xD800 + (c.toNat - 0x10000) / 0x400)).toNat =
        0xD800 + (c.toNat - 0x10000) / 0x400 :=
      UInt16.toNat_ofNat_of_lt' (by simp [UInt16.size]; omega)
    have hw : (UInt16.ofNat (0xDC00 + (c.toNat - 0x10000) % 0x400)).toNat =
        0xDC00 + (c.toNat - 0x10000) % 0x400 :=
      UInt16.toNat_ofNat_of_lt' (by simp [UInt16.size]; omega)
    simp only [List.cons_append, List.nil_append]
    conv_lhs => rw [unitsChars?.eq_def]
    simp only [hu, hw]
    have h1 : 0xD800 ≤ 0xD800 + (c.toNat - 0x10000) / 0x400 ∧
        0xD800 + (c.toNat - 0x10000) / 0x400 ≤ 0xDBFF := by omega
    have h2 : 0xDC00 ≤ 0xDC00 + (c.toNat - 0x10000) % 0x400 ∧
        0xDC00 + (c.toNat - 0x10000) % 0x400 ≤ 0xDFFF := by omega
    have h3 : 0x10000 + (0xD800 + (c.toNat - 0x10000) / 0x400 - 0xD800) * 0x400 +
        (0xDC00 + (c.toNat - 0x10000) % 0x400) - 0xDC00 = c.toNat := by omega
    simp only [Bool.and_eq_true, decide_eq_true_eq, h1, h2, and_self, ite_true, h3,
      Char.ofNat_toNat]
    cases unitsChars? us <;> rfl

theorem unitsChars?_stringUnits (cs : List Char) :
    unitsChars? (cs.flatMap charUnits) = some cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => rw [List.flatMap_cons, unitsChars?_charUnits, ih]; rfl

theorem unitsString?_stringUnits (s : String) : unitsString? (stringUnits s) = some s := by
  simp [unitsString?, stringUnits, unitsChars?_stringUnits]

@[simp] theorem stringUnits_inj {a b : String} : stringUnits a = stringUnits b ↔ a = b := by
  constructor
  · intro h
    have := congrArg unitsString? h
    simpa [unitsString?_stringUnits] using this
  · rintro rfl; rfl

theorem asString_jstr (w s : String) : asString w (jstr s) = .ok s := by
  simp [asString, jstr, unitsString?_stringUnits]

theorem asNat_jnat (w : String) (n : Nat) : asNat w (jnat n) = .ok n := by
  cases n <;> simp [asNat, jnat, Decimal.toInt?]; omega

theorem decodeField_encodeField (f : ObservedField) : decodeField (encodeField f) = .ok f := by
  simp [decodeField, encodeField, jobj, objectOf, member, stringMember, natMember, asString_jstr,
    asNat_jnat,
    bind, Except.bind, pure, Except.pure]

theorem traverse_map {α β : Type} {f : α → Except String β} {g : β → α}
    (h : ∀ b, f (g b) = .ok b) : ∀ bs : List β, traverse f (bs.map g) = .ok bs
  | [] => rfl
  | b :: bs => by simp [traverse, h b, traverse_map h bs]

theorem asList_jarr (w : String) (xs : List Json) : asList w (jarr xs) = .ok xs := by
  simp [asList, jarr]

theorem kindOf?_kindName (k : Kind) : kindOf? (kindName k) = .ok k := by
  cases k <;> rfl

theorem decodeRecord_encodeRecord (r : ObservedRecord) : decodeRecord (encodeRecord r) = .ok r := by
  simp [decodeRecord, encodeRecord, jobj, objectOf, member, stringMember, natMember, asString_jstr,
    asNat_jnat, asList_jarr, kindOf?_kindName, traverse_map decodeField_encodeField, bind,
    Except.bind, pure, Except.pure]

theorem decodeProvenance_encodeProvenance (p : Provenance) :
    decodeProvenance (encodeProvenance p) = .ok p := by
  simp [decodeProvenance, encodeProvenance, jobj, objectOf, member, stringMember, asString_jstr,
    bind, Except.bind, pure, Except.pure]

theorem decode_encode (r : Report) : decode (encode r) = .ok r := by
  simp [decode, Interchange.encode, jobj, objectOf, member, stringMember, natMember, asString_jstr,
    asNat_jnat, asList_jarr, traverse_map decodeRecord_encodeRecord,
    decodeProvenance_encodeProvenance, bind, Except.bind, pure, Except.pure, schemaName,
    schemaVersion]

end Silmaril.Proofs.Data.Layout.Interchange
