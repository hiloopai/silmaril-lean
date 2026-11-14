module

public import Silmaril.Net.Qpack.Section.Defs
public import Silmaril.Net.Qpack.Instruction.Thms
import Silmaril.Proofs.Net.Qpack.Section

@[expose] public section

/-!
# QPACK encoded field sections: theorems

PROVED (standard axioms; proofs in `Silmaril/Proofs/Net/Qpack/Section.lean`):

* `decodeRic_encodeRic` (§4.5.1.1): the decoder reconstructs the Required Insert Count when it
  is zero, or when `MaxEntries > 0` and it lies in the window
  `(TotalNumberOfInserts - MaxEntries, TotalNumberOfInserts + MaxEntries]`;
* `decodeBase_encodeBase` (§4.5.1.2): Sign and Delta Base determine the Base;
* `decodePrefix_encode`, `decodeFieldLine_encode`, `decodeEncodedSection_encode`: the prefix,
  every field line representation (§4.5.2–§4.5.6, both `N` bits, both `T` bits, post-Base
  forms) and whole encoded field sections round trip; so the first-octet dispatch is
  unambiguous;
* `decodeFieldSection_blocked_iff` (§2.1.2, §2.2.1): a field section blocks exactly when its
  Required Insert Count exceeds the decoder's insert count;
* `decodeFieldSection_ric_zero` (§2.1, §2.1.2): a section with encoded Required Insert Count 0
  never blocks, and if it decodes, every representation references only the static table or
  is a literal;
* `decodeFieldSection_refs` (§2.2.3): in a decoded section, every dynamic reference names an
  absolute index below the Required Insert Count, of an entry still in the table;
  `lookupDyn_error_of_le`, `lookupDyn_error_of_evicted`: references at or above the Required
  Insert Count, or to evicted entries, are `QPACK_DECOMPRESSION_FAILED`;
* `decodeFieldSection_decoded_le`: a decoded section's Required Insert Count is at most the
  insert count; `decodeFieldSection_length`: one field line per representation, in order (§2.2).

CHECKED by evaluation: the example of §4.5.1.1 (encoded 4 → 9), the example of §4.5.1.2, and
the encoded field sections of Appendix B.1, B.2 and B.4 against the tables built from the
Appendix B encoder streams.
-/

namespace Silmaril.Net.Qpack

open Silmaril.Net.Hpack (Entry Entry.ofStrings ascii)

theorem decodeRic_encodeRic {M T ric : Nat}
    (h : ric = 0 ∨ (0 < M ∧ ric ≤ T + M ∧ T < ric + M)) :
    decodeRic M T (encodeRic M ric) = some ric :=
  Silmaril.Proofs.Net.Qpack.decodeRic_encodeRic h

theorem decodeBase_encodeBase (ric base : Nat) :
    decodeBase ric (encodeBase ric base).1 (encodeBase ric base).2 = some base :=
  Silmaril.Proofs.Net.Qpack.decodeBase_encodeBase ric base

theorem decodePrefix_encode (p : SectionPrefix) (rest : List UInt8) :
    decodePrefix (p.encode ++ rest) = some (p, rest) :=
  Silmaril.Proofs.Net.Qpack.decodePrefix_encode p rest

theorem decodeFieldLine_encode (l : FieldLine) (rest : List UInt8) :
    decodeFieldLine (l.encode ++ rest) = some (l, rest) :=
  Silmaril.Proofs.Net.Qpack.decodeFieldLine_encode l rest

theorem decodeEncodedSection_encode (s : EncodedSection) :
    decodeEncodedSection s.encode = some s :=
  Silmaril.Proofs.Net.Qpack.decodeEncodedSection_encode s

theorem decodeFieldSection_blocked_iff (t : DynTable) (s : EncodedSection) (ric : Nat) :
    decodeFieldSection t s = .ok (.blocked ric) ↔
      decodeRic t.maxEntries t.insertCount s.pre.encRic = some ric ∧ t.insertCount < ric :=
  Silmaril.Proofs.Net.Qpack.decodeFieldSection_blocked_iff t s ric

theorem decodeFieldSection_decoded {t : DynTable} {s : EncodedSection} {ric : Nat}
    {fs : List Entry} (h : decodeFieldSection t s = .ok (.decoded ric fs)) :
    decodeRic t.maxEntries t.insertCount s.pre.encRic = some ric ∧ ric ≤ t.insertCount ∧
      ∃ base, decodeBase ric s.pre.sign s.pre.deltaBase = some base ∧
        resolveLines t ric base s.lines = .ok fs :=
  Silmaril.Proofs.Net.Qpack.decodeFieldSection_decoded h

theorem decodeFieldSection_decoded_le {t : DynTable} {s : EncodedSection} {ric : Nat}
    {fs : List Entry} (h : decodeFieldSection t s = .ok (.decoded ric fs)) :
    ric ≤ t.insertCount :=
  (decodeFieldSection_decoded h).2.1

theorem decodeFieldSection_ric_zero {t : DynTable} {s : EncodedSection} (h0 : s.pre.encRic = 0)
    {r : SectionResult} (h : decodeFieldSection t s = .ok r) :
    ∃ fs, r = .decoded 0 fs ∧ ∀ l ∈ s.lines, l.staticOnly = true :=
  Silmaril.Proofs.Net.Qpack.decodeFieldSection_ric_zero h0 h

theorem decodeFieldSection_ric_zero_not_blocked {t : DynTable} {s : EncodedSection}
    (h0 : s.pre.encRic = 0) (ric : Nat) : decodeFieldSection t s ≠ .ok (.blocked ric) :=
  fun h => by obtain ⟨_, hfs, -⟩ := decodeFieldSection_ric_zero h0 h; cases hfs

theorem decodeFieldSection_refs {t : DynTable} {s : EncodedSection} {ric : Nat}
    {fs : List Entry} (h : decodeFieldSection t s = .ok (.decoded ric fs)) :
    ∃ base, decodeBase ric s.pre.sign s.pre.deltaBase = some base ∧
      ∀ l ∈ s.lines, ∀ a, l.absRef base = some a → a < ric ∧ (t.lookupAbs a).isSome :=
  Silmaril.Proofs.Net.Qpack.decodeFieldSection_refs h

theorem decodeFieldSection_length {t : DynTable} {s : EncodedSection} {ric : Nat}
    {fs : List Entry} (h : decodeFieldSection t s = .ok (.decoded ric fs)) :
    fs.length = s.lines.length :=
  Silmaril.Proofs.Net.Qpack.decodeFieldSection_length h

theorem lookupDyn_error_of_le {t : DynTable} {ric a : Nat} (h : ric ≤ a) :
    lookupDyn t ric a = .error .decompressionFailed :=
  Silmaril.Proofs.Net.Qpack.lookupDyn_error_of_le h

theorem lookupDyn_error_of_evicted {t : DynTable} {ric a : Nat} (h : t.lookupAbs a = none) :
    lookupDyn t ric a = .error .decompressionFailed :=
  Silmaril.Proofs.Net.Qpack.lookupDyn_error_of_evicted h

/-! ## RFC 9204 examples -/

/-- §4.5.1.1: a 100-byte table (MaxEntries 3), 10 inserts received, encoded value 4: the
Required Insert Count is 9. -/
example : decodeRic 3 10 4 = some 9 := by decide
example : encodeRic 3 9 = 4 := by decide
/-- §4.5.1.2: Required Insert Count 9, Sign 1, Delta Base 2: the Base is 6. -/
example : decodeBase 9 true 2 = some 6 := by decide
/-- §4.5.1.2: a Sign bit of 1 with Delta Base ≥ Required Insert Count is invalid. -/
example : decodeBase 2 true 2 = none := by decide

/-- The table after an encoder stream, from the initial table with maximum capacity `m`. -/
def tableAfter (m : Nat) (xs : List UInt8) : Option DynTable :=
  match decodeEncoderInstrs xs with
  | none => none
  | some is =>
    match (DynTable.empty m).applyInstrs is with
    | .ok t => some t
    | .error _ => none

/-- Decode a field section's octets after an encoder stream. -/
def sectionAfter (m : Nat) (enc sec : List UInt8) : Option SectionResult :=
  (tableAfter m enc).bind fun t =>
    match decodeFieldSectionBytes t sec with
    | .ok r => some r
    | .error _ => none

/-- B.1: `0000 51 0b "/index.html"`: Required Insert Count 0, Base 0, a literal field line with
static name reference 1, `:path: /index.html`. -/
def b1Section : List UInt8 := [0x00, 0x00, 0x51, 0x0b] ++ ascii "/index.html"

example : decodeEncodedSection b1Section =
    some ⟨⟨0, false, 0⟩, [.literalRef false (.static 1) (ascii "/index.html")]⟩ := by
  decide +kernel
example : sectionAfter 0 [] b1Section =
    some (.decoded 0 [Entry.ofStrings ":path" "/index.html"]) := by decide +kernel

/-- B.2, stream 4: `0381 10 11`: Required Insert Count 2, Base 0, two post-Base indexed lines. -/
def b2Section : List UInt8 := [0x03, 0x81, 0x10, 0x11]

example : decodeEncodedSection b2Section =
    some ⟨⟨3, true, 1⟩, [.indexed (.postBase 0), .indexed (.postBase 1)]⟩ := by decide +kernel
example : sectionAfter 220 b2Encoder b2Section =
    some (.decoded 2 [Entry.ofStrings ":authority" "www.example.com",
      Entry.ofStrings ":path" "/sample/path"]) := by decide +kernel
/-- Before the B.2 encoder stream arrives the section is blocked on Required Insert Count 2. -/
example : sectionAfter 220 [] b2Section = some (.blocked 2) := by decide +kernel

/-- B.4, stream 8: `0500 80 c1 81`: Required Insert Count 4, Base 4; dynamic relative 0
(absolute 3), static 1, dynamic relative 1 (absolute 2). -/
def b4Section : List UInt8 := [0x05, 0x00, 0x80, 0xc1, 0x81]

example : sectionAfter 220 (b2Encoder ++ b3Encoder ++ b4Encoder) b4Section =
    some (.decoded 4 [Entry.ofStrings ":authority" "www.example.com",
      Entry.ofStrings ":path" "/", Entry.ofStrings "custom-key" "custom-value"]) := by
  decide +kernel
/-- B.4: the section is blocked while the Duplicate is delayed (insert count 3 < 4). -/
example : sectionAfter 220 (b2Encoder ++ b3Encoder) b4Section = some (.blocked 4) := by
  decide +kernel
/-- RIC 1, Base 1, dynamic relative index 0 (absolute 0): valid after B.4, but after B.5
evicts absolute index 0 the reference fails (§2.2.3). -/
example : sectionAfter 220 (b2Encoder ++ b3Encoder ++ b4Encoder) [0x02, 0x00, 0x80] =
    some (.decoded 1 [Entry.ofStrings ":authority" "www.example.com"]) := by decide +kernel
example : sectionAfter 220 (b2Encoder ++ b3Encoder ++ b4Encoder ++ b5Encoder)
    [0x02, 0x00, 0x80] = none := by decide +kernel
/-- A reference at the Required Insert Count fails (§2.2.3): RIC 1, post-Base index 1. -/
example : sectionAfter 220 b2Encoder [0x02, 0x80, 0x11] = none := by decide +kernel

end Silmaril.Net.Qpack
