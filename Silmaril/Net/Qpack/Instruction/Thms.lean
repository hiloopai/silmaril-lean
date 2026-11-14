module

public import Silmaril.Net.Qpack.Instruction.Defs
import Silmaril.Proofs.Net.Qpack.Instruction

@[expose] public section

/-!
# QPACK encoder and decoder instructions: theorems

PROVED (standard axioms; proofs in `Silmaril/Proofs/Net/Qpack/Instruction.lean`):

* `decodeEncoderInstr_encode`, `decodeEncoderInstrs_encode`: every encoder instruction
  (§4.3.1–§4.3.4) is read back from its serialization and the reader stops exactly after it;
  so the first-octet dispatch of §4.3 is unambiguous, and an encoder stream payload round trips;
* `decodeDecoderInstr_encode`, `decodeDecoderInstrs_encode`: the same for decoder instructions
  (§4.4.1–§4.4.3);
* `decodeMany_flatMap`: the generic sequence reader inverts concatenation for any codec whose
  items are non-empty;
* `applyInstr_valid`, `applyInstrs_valid`: applying encoder instructions keeps the decoder's
  table valid (size ≤ capacity ≤ maximum, §3.2.2, §3.2.3), whatever the peer sends;
* `applyInstr_error`: every failure is `QPACK_ENCODER_STREAM_ERROR` (§3.1, §2.2.3, §3.2.2,
  §4.3.1);
* `applyInstrs_insertCount`, `applyInstrs_lookup`, `applyInstr_maxCapacity`: the insert count
  never decreases, entries never change their absolute index, the maximum capacity is fixed.

CHECKED by evaluation: the encoder and decoder stream octets of RFC 9204 Appendix B.2–B.5 and
the resulting table sizes (106, 160, 217, 215).
-/

namespace Silmaril.Net.Qpack

open Silmaril.Net.Hpack (Entry Entry.ofStrings ascii tableSize)

theorem decodeMany_flatMap {α : Type} (enc : α → List UInt8)
    (dec : List UInt8 → Option (α × List UInt8))
    (hrt : ∀ x rest, dec (enc x ++ rest) = some (x, rest)) (hne : ∀ x, enc x ≠ [])
    (xs : List α) : decodeMany dec (xs.flatMap enc) = some xs :=
  Silmaril.Proofs.Net.Qpack.decodeMany_flatMap enc dec hrt hne xs

theorem decodeEncoderInstr_encode (i : EncoderInstr) (rest : List UInt8) :
    decodeEncoderInstr (i.encode ++ rest) = some (i, rest) :=
  Silmaril.Proofs.Net.Qpack.decodeEncoderInstr_encode i rest

theorem decodeEncoderInstrs_encode (is : List EncoderInstr) :
    decodeEncoderInstrs (encodeEncoderInstrs is) = some is :=
  Silmaril.Proofs.Net.Qpack.decodeEncoderInstrs_encode is

theorem decodeDecoderInstr_encode (i : DecoderInstr) (rest : List UInt8) :
    decodeDecoderInstr (i.encode ++ rest) = some (i, rest) :=
  Silmaril.Proofs.Net.Qpack.decodeDecoderInstr_encode i rest

theorem decodeDecoderInstrs_encode (is : List DecoderInstr) :
    decodeDecoderInstrs (encodeDecoderInstrs is) = some is :=
  Silmaril.Proofs.Net.Qpack.decodeDecoderInstrs_encode is

namespace DynTable

theorem applyInstr_cases {t t' : DynTable} {i : EncoderInstr} (h : t.applyInstr i = .ok t') :
    (∃ e, t.insert e = some t') ∨ (∃ c, t.setCapacity c = some t') :=
  Silmaril.Proofs.Net.Qpack.DynTable.applyInstr_cases h

theorem applyInstr_valid {t t' : DynTable} (ht : t.Valid) {i : EncoderInstr}
    (h : t.applyInstr i = .ok t') : t'.Valid :=
  Silmaril.Proofs.Net.Qpack.DynTable.applyInstr_valid ht h

theorem applyInstr_error {t : DynTable} {i : EncoderInstr} {err : QpackError}
    (h : t.applyInstr i = .error err) : err = .encoderStreamError :=
  Silmaril.Proofs.Net.Qpack.DynTable.applyInstr_error h

theorem applyInstr_insertCount {t t' : DynTable} {i : EncoderInstr}
    (h : t.applyInstr i = .ok t') : t.insertCount ≤ t'.insertCount :=
  Silmaril.Proofs.Net.Qpack.DynTable.applyInstr_insertCount h

theorem applyInstr_maxCapacity {t t' : DynTable} {i : EncoderInstr}
    (h : t.applyInstr i = .ok t') : t'.maxCapacity = t.maxCapacity :=
  Silmaril.Proofs.Net.Qpack.DynTable.applyInstr_maxCapacity h

theorem applyInstr_lookup {t t' : DynTable} {i : EncoderInstr} (h : t.applyInstr i = .ok t')
    {a : Nat} (ha : a < t.insertCount) {x : Entry} (hx : t'.lookupAbs a = some x) :
    t.lookupAbs a = some x :=
  Silmaril.Proofs.Net.Qpack.DynTable.applyInstr_lookup h ha hx

theorem applyInstrs_valid {t t' : DynTable} (ht : t.Valid) {is : List EncoderInstr}
    (h : t.applyInstrs is = .ok t') : t'.Valid :=
  Silmaril.Proofs.Net.Qpack.DynTable.applyInstrs_valid ht h

theorem applyInstrs_insertCount {t t' : DynTable} {is : List EncoderInstr}
    (h : t.applyInstrs is = .ok t') : t.insertCount ≤ t'.insertCount :=
  Silmaril.Proofs.Net.Qpack.DynTable.applyInstrs_insertCount h

theorem applyInstrs_lookup {t t' : DynTable} {is : List EncoderInstr}
    (h : t.applyInstrs is = .ok t') {a : Nat} (ha : a < t.insertCount) {x : Entry}
    (hx : t'.lookupAbs a = some x) : t.lookupAbs a = some x :=
  Silmaril.Proofs.Net.Qpack.DynTable.applyInstrs_lookup h ha hx

end DynTable

/-! ## RFC 9204 Appendix B: encoder and decoder streams -/

/-- B.2, encoder stream: Set Dynamic Table Capacity 220 and two insertions with static name
references. -/
def b2Encoder : List UInt8 :=
  [0x3f, 0xbd, 0x01, 0xc0, 0x0f] ++ ascii "www.example.com" ++ [0xc1, 0x0c] ++
    ascii "/sample/path"

example : decodeEncoderInstrs b2Encoder = some [.setCapacity 220,
    .insertNameRef true 0 (ascii "www.example.com"),
    .insertNameRef true 1 (ascii "/sample/path")] := by decide +kernel

/-- B.3, encoder stream: Insert with Literal Name `custom-key: custom-value`. -/
def b3Encoder : List UInt8 :=
  [0x4a] ++ ascii "custom-key" ++ [0x0c] ++ ascii "custom-value"

example : decodeEncoderInstrs b3Encoder =
    some [.insertLiteral (ascii "custom-key") (ascii "custom-value")] := by decide +kernel

/-- B.4, encoder stream: Duplicate relative index 2. -/
def b4Encoder : List UInt8 := [0x02]

/-- B.5, encoder stream: Insert with Name Reference, dynamic relative index 1. -/
def b5Encoder : List UInt8 := [0x81, 0x0d] ++ ascii "custom-value2"

example : decodeEncoderInstrs b5Encoder =
    some [.insertNameRef false 1 (ascii "custom-value2")] := by decide +kernel

/-- The table size and live absolute indices `[dropped, insertCount)` after an encoder stream. -/
def tableSummary (t : DynTable) (xs : List UInt8) : Option (Nat × Nat × Nat) :=
  match decodeEncoderInstrs xs with
  | none => none
  | some is =>
    match t.applyInstrs is with
    | .ok t' => some (tableSize t'.entries, t'.dropped, t'.insertCount)
    | .error _ => none

/-- B.2: size 106, entries 0 and 1 (maximum capacity 220 assumed for the decoder). -/
example : tableSummary (.empty 220) b2Encoder = some (106, 0, 2) := by decide +kernel
/-- B.3: size 160, entries 0..2. -/
example : tableSummary (.empty 220) (b2Encoder ++ b3Encoder) = some (160, 0, 3) := by
  decide +kernel
/-- B.4: size 217, entries 0..3; entry 3 duplicates entry 0. -/
example : tableSummary (.empty 220) (b2Encoder ++ b3Encoder ++ b4Encoder) = some (217, 0, 4) := by
  decide +kernel
/-- B.5: size 215; entry 0 is evicted, entries 1..4 remain. -/
example : tableSummary (.empty 220) (b2Encoder ++ b3Encoder ++ b4Encoder ++ b5Encoder) =
    some (215, 1, 5) := by decide +kernel

/-- B.2–B.4, decoder stream: Section Acknowledgment (stream 4), Insert Count Increment (1),
Stream Cancellation (stream 8). -/
example : decodeDecoderInstrs [0x84, 0x01, 0x48] =
    some [.sectionAck 4, .insertCountIncrement 1, .streamCancel 8] := by decide +kernel

/-- A capacity above the maximum is an encoder stream error (§4.3.1). -/
example : (DynTable.empty 100).applyInstr (.setCapacity 101) = .error .encoderStreamError :=
  rfl
/-- A Duplicate of a never-inserted entry is an encoder stream error (§2.2.3). -/
example : (DynTable.empty 100).applyInstr (.duplicate 0) = .error .encoderStreamError :=
  rfl

end Silmaril.Net.Qpack
