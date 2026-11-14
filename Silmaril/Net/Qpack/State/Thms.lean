module

public import Silmaril.Net.Qpack.State.Defs
public import Silmaril.Net.Qpack.Section.Thms
import Silmaril.Proofs.Net.Qpack.State

@[expose] public section

/-!
# QPACK connection state: theorems

PROVED (standard axioms; proofs in `Silmaril/Proofs/Net/Qpack/State.lean`):

Encoder (§2.1):

* `Encoder.init_valid`, `Encoder.applyInstr_valid`, `Encoder.sendSection_valid`,
  `Encoder.onDecoderInstr_valid`: the invariant `Encoder.Valid` — valid table,
  `Known Received Count ≤ insert count`, outstanding references below their Required Insert
  Count, and **every pinned entry (unacknowledged or referenced by an unacknowledged section)
  still in the table** — holds initially and after every allowed step; in particular the
  eviction guard `evictionOk` guarantees the encoder never evicts a non-evictable entry
  (§2.1.1, §3.2.2, §4.3.1);
* `Encoder.onDecoderInstr_krc_mono`: the Known Received Count never decreases (§2.1.4), and
  by `Valid` it never exceeds the insert count;
* `Encoder.onDecoderInstr_increment_error`, `Encoder.onDecoderInstr_error`: an Insert Count
  Increment of zero or beyond the insert count is `QPACK_DECODER_STREAM_ERROR` (§4.4.3), and
  decoder instructions fail only with that error (§4.4.1, §6);
* `Encoder.init_blockedOk`, `Encoder.sendSection_blockedOk`, `Encoder.applyInstr_blockedOk`,
  `Encoder.onDecoderInstr_blockedOk`: the number of streams that could become blocked stays
  within `SETTINGS_QPACK_BLOCKED_STREAMS` "at all times" (§2.1.2).

Decoder (§2.2):

* `Decoder.init_valid`, `Decoder.onEncoderInstr_valid`, `Decoder.onSection_valid`,
  `Decoder.cancelStream_valid`, `Decoder.insertCountIncrement_valid`: valid table, at most
  `SETTINGS_QPACK_BLOCKED_STREAMS` blocked streams, reported count ≤ insert count;
* `Decoder.onSection_too_many_blocked`: one blocked stream too many is
  `QPACK_DECOMPRESSION_FAILED` (§2.1.2); `Decoder.onSection_error`,
  `Decoder.onEncoderInstr_error`: the error codes of §6;
* `Decoder.onSection_ack`: a Section Acknowledgment is emitted exactly for decoded sections with
  non-zero Required Insert Count (§2.2.2.1, §4.4.1);
* `Decoder.insertCountIncrement_spec`, `increment_accepted`: an emitted Insert Count Increment is
  non-zero, brings the count to the insert count, and is accepted by an encoder in agreement
  (§2.2.2.3, §4.4.3);
* `Decoder.onSection_krc_mono`, `Decoder.insertCountIncrement_krc_mono`: the decoder's Known
  Received Count never decreases.

CHECKED by evaluation: the whole exchange of RFC 9204 Appendix B.1–B.5 on both sides — the
encoder's table size, insert count, evictions and Known Received Count, and the decoder's
emitted instructions (`84`, `01`, `48`) — and the eviction guard refusing B.5's eviction when
the evicted entry is still referenced or unacknowledged.
-/

namespace Silmaril.Net.Qpack

open Silmaril.Net.Hpack (Entry Entry.ofStrings ascii tableSize)

namespace Encoder

theorem init_valid (m b : Nat) : (init m b).Valid :=
  Silmaril.Proofs.Net.Qpack.Encoder.init_valid m b

theorem init_blockedOk (m b : Nat) : (init m b).BlockedOk := Nat.zero_le _

theorem applyInstr_valid {enc enc' : Encoder} (hv : enc.Valid) {i : EncoderInstr}
    (h : enc.applyInstr i = some enc') : enc'.Valid :=
  Silmaril.Proofs.Net.Qpack.Encoder.applyInstr_valid hv h

theorem applyInstr_blockedOk {enc enc' : Encoder} (hb : enc.BlockedOk) {i : EncoderInstr}
    (h : enc.applyInstr i = some enc') : enc'.BlockedOk :=
  Silmaril.Proofs.Net.Qpack.Encoder.applyInstr_blockedOk hb h

theorem sendSection_valid {enc enc' : Encoder} (hv : enc.Valid) {sid ric : Nat}
    {refs : List Nat} (h : enc.sendSection sid ric refs = some enc') : enc'.Valid :=
  Silmaril.Proofs.Net.Qpack.Encoder.sendSection_valid hv h

theorem sendSection_blockedOk {enc enc' : Encoder} (hb : enc.BlockedOk) {sid ric : Nat}
    {refs : List Nat} (h : enc.sendSection sid ric refs = some enc') : enc'.BlockedOk :=
  Silmaril.Proofs.Net.Qpack.Encoder.sendSection_blockedOk hb h

theorem onDecoderInstr_valid {enc enc' : Encoder} (hv : enc.Valid) {i : DecoderInstr}
    (h : enc.onDecoderInstr i = .ok enc') : enc'.Valid :=
  Silmaril.Proofs.Net.Qpack.Encoder.onDecoderInstr_valid hv h

theorem onDecoderInstr_blockedOk {enc enc' : Encoder} (hb : enc.BlockedOk) {i : DecoderInstr}
    (h : enc.onDecoderInstr i = .ok enc') : enc'.BlockedOk :=
  Silmaril.Proofs.Net.Qpack.Encoder.onDecoderInstr_blockedOk hb h

theorem onDecoderInstr_krc_mono {enc enc' : Encoder} {i : DecoderInstr}
    (h : enc.onDecoderInstr i = .ok enc') : enc.krc ≤ enc'.krc :=
  Silmaril.Proofs.Net.Qpack.Encoder.onDecoderInstr_krc_mono h

theorem onDecoderInstr_table {enc enc' : Encoder} {i : DecoderInstr}
    (h : enc.onDecoderInstr i = .ok enc') : enc'.table = enc.table :=
  Silmaril.Proofs.Net.Qpack.Encoder.onDecoderInstr_table h

theorem onDecoderInstr_error {enc : Encoder} {i : DecoderInstr} {err : QpackError}
    (h : enc.onDecoderInstr i = .error err) : err = .decoderStreamError :=
  Silmaril.Proofs.Net.Qpack.Encoder.onDecoderInstr_error h

theorem onDecoderInstr_increment_error {enc : Encoder} {k : Nat}
    (hk : k = 0 ∨ enc.table.insertCount < enc.krc + k) :
    enc.onDecoderInstr (.insertCountIncrement k) = .error .decoderStreamError :=
  Silmaril.Proofs.Net.Qpack.Encoder.onDecoderInstr_increment_error hk

/-- The Known Received Count is at most the insert count (§2.1.4). -/
theorem krc_le_insertCount {enc : Encoder} (hv : enc.Valid) : enc.krc ≤ enc.table.insertCount :=
  hv.2.1

/-- A pinned entry (unacknowledged, or referenced by an unacknowledged section) is in the
table (§2.1.1). -/
theorem pinned_present {enc : Encoder} (hv : enc.Valid) {a : Nat} (ha : enc.Pinned a) :
    (enc.table.lookupAbs a).isSome :=
  hv.2.2.2 a ha

end Encoder

namespace Decoder

theorem init_valid (m b : Nat) : (init m b).Valid :=
  ⟨DynTable.empty_valid m, Nat.zero_le _, Nat.le_refl _⟩

theorem onEncoderInstr_valid {d d' : Decoder} (hv : d.Valid) {i : EncoderInstr}
    (h : d.onEncoderInstr i = .ok d') : d'.Valid :=
  Silmaril.Proofs.Net.Qpack.Decoder.onEncoderInstr_valid hv h

theorem onEncoderInstr_error {d : Decoder} {i : EncoderInstr} {err : QpackError}
    (h : d.onEncoderInstr i = .error err) : err = .encoderStreamError :=
  Silmaril.Proofs.Net.Qpack.Decoder.onEncoderInstr_error h

theorem onSection_valid {d d' : Decoder} (hv : d.Valid) {sid : Nat} {s : EncodedSection}
    {out : Option (List Entry)} {ins : Option DecoderInstr}
    (h : d.onSection sid s = .ok (d', out, ins)) : d'.Valid :=
  Silmaril.Proofs.Net.Qpack.Decoder.onSection_valid hv h

theorem onSection_krc_mono {d d' : Decoder} {sid : Nat} {s : EncodedSection}
    {out : Option (List Entry)} {ins : Option DecoderInstr}
    (h : d.onSection sid s = .ok (d', out, ins)) : d.krc ≤ d'.krc :=
  Silmaril.Proofs.Net.Qpack.Decoder.onSection_krc_mono h

theorem onSection_error {d : Decoder} {sid : Nat} {s : EncodedSection} {err : QpackError}
    (h : d.onSection sid s = .error err) : err = .decompressionFailed :=
  Silmaril.Proofs.Net.Qpack.Decoder.onSection_error h

theorem onSection_too_many_blocked {d : Decoder} {sid : Nat} {s : EncodedSection} {ric : Nat}
    (hd : decodeFieldSection d.table s = .ok (.blocked ric)) (hm : sid ∉ d.blocked)
    (hl : d.maxBlocked ≤ d.blocked.length) :
    d.onSection sid s = .error .decompressionFailed :=
  Silmaril.Proofs.Net.Qpack.Decoder.onSection_too_many_blocked hd hm hl

theorem onSection_ack {d d' : Decoder} {sid : Nat} {s : EncodedSection}
    {out : Option (List Entry)} {ins : Option DecoderInstr}
    (h : d.onSection sid s = .ok (d', out, ins)) :
    ins.isSome ↔ ∃ ric fs, decodeFieldSection d.table s = .ok (.decoded ric fs) ∧ ric ≠ 0 :=
  Silmaril.Proofs.Net.Qpack.Decoder.onSection_ack h

theorem cancelStream_valid {d : Decoder} (hv : d.Valid) (sid : Nat) :
    (d.cancelStream sid).1.Valid :=
  Silmaril.Proofs.Net.Qpack.Decoder.cancelStream_valid hv sid

theorem insertCountIncrement_valid {d : Decoder} (hv : d.Valid) :
    d.insertCountIncrement.1.Valid :=
  Silmaril.Proofs.Net.Qpack.Decoder.insertCountIncrement_valid hv

theorem insertCountIncrement_spec (d : Decoder) {k : Nat}
    (h : d.insertCountIncrement.2 = some (.insertCountIncrement k)) :
    k ≠ 0 ∧ d.krc + k = d.table.insertCount ∧ d.insertCountIncrement.1.krc = d.krc + k :=
  Silmaril.Proofs.Net.Qpack.Decoder.insertCountIncrement_spec d h

theorem insertCountIncrement_krc_mono (d : Decoder) : d.krc ≤ d.insertCountIncrement.1.krc :=
  Silmaril.Proofs.Net.Qpack.Decoder.insertCountIncrement_krc_mono d

end Decoder

theorem increment_accepted {d : Decoder} {enc : Encoder} {k : Nat}
    (h : d.insertCountIncrement.2 = some (.insertCountIncrement k)) (hk : enc.krc = d.krc)
    (hic : d.table.insertCount ≤ enc.table.insertCount) :
    enc.onDecoderInstr (.insertCountIncrement k) = .ok { enc with krc := enc.krc + k } :=
  Silmaril.Proofs.Net.Qpack.increment_accepted h hk hic

/-! ## RFC 9204 Appendix B, both sides -/

/-- Perform an encoder stream's instructions on the encoder, if all are allowed. -/
def Encoder.sendInstrs (enc : Encoder) (xs : List UInt8) : Option Encoder :=
  (decodeEncoderInstrs xs).bind fun is => go enc is
where
  go (enc : Encoder) : List EncoderInstr → Option Encoder
    | [] => some enc
    | i :: is => (enc.applyInstr i).bind fun e => go e is

/-- Process a decoder stream's instructions on the encoder. -/
def Encoder.receive (enc : Encoder) (xs : List UInt8) : Option Encoder :=
  (decodeDecoderInstrs xs).bind fun is => go enc is
where
  go (enc : Encoder) : List DecoderInstr → Option Encoder
    | [] => some enc
    | i :: is => (enc.onDecoderInstr i).toOption.bind fun e => go e is

/-- Known Received Count, outstanding sections, table size, dropped count, insert count. -/
def Encoder.summary (enc : Encoder) : Nat × Nat × Nat × Nat × Nat :=
  (enc.krc, enc.pending.length, tableSize enc.table.entries, enc.table.dropped,
    enc.table.insertCount)

/-- The encoder of Appendix B (maximum capacity 220, one blocked stream allowed). -/
def bEncoder0 : Encoder := Encoder.init 220 1

/-- B.2: capacity and two insertions, a section on stream 4 referencing absolute 0 and 1
(Required Insert Count 2), then the decoder's Section Acknowledgment `84`. -/
def bEncoder2 : Option Encoder :=
  (bEncoder0.sendInstrs b2Encoder).bind fun e => (e.sendSection 4 2 [0, 1]).bind
    fun e => e.receive [0x84]

example : bEncoder2.map Encoder.summary = some (2, 0, 106, 0, 2) := by decide +kernel

/-- B.3: a speculative insertion, then the decoder's Insert Count Increment `01`. -/
def bEncoder3 : Option Encoder :=
  bEncoder2.bind fun e => (e.sendInstrs b3Encoder).bind fun e => e.receive [0x01]

example : bEncoder3.map Encoder.summary = some (3, 0, 160, 0, 3) := by decide +kernel

/-- B.4: Duplicate, a section on stream 8 referencing absolute 3 and 2 (Required Insert Count
4), then the decoder's Stream Cancellation `48`. -/
def bEncoder4 : Option Encoder :=
  bEncoder3.bind fun e => (e.sendInstrs b4Encoder).bind fun e => (e.sendSection 8 4 [3, 2]).bind
    fun e => e.receive [0x48]

example : bEncoder4.map Encoder.summary = some (3, 0, 217, 0, 4) := by decide +kernel

/-- B.5: an insertion evicting absolute index 0, which is acknowledged and unreferenced. -/
example : (bEncoder4.bind fun e => e.sendInstrs b5Encoder).map Encoder.summary =
    some (3, 0, 215, 1, 5) := by decide +kernel

/-- The eviction guard: had the stream 8 section referenced absolute 0 and not been cancelled,
B.5 would evict a referenced entry, so the encoder must not send it (§2.1.1). -/
example : (bEncoder3.bind fun e => (e.sendInstrs b4Encoder).bind fun e =>
    (e.sendSection 8 4 [3, 0]).bind fun e => e.sendInstrs b5Encoder) = none := by decide +kernel

/-- The eviction guard: without any acknowledgment (Known Received Count 0) entry 0 is not
evictable, so B.5 cannot be sent either (§2.1.1). -/
example : ((bEncoder0.sendInstrs (b2Encoder ++ b3Encoder ++ b4Encoder)).bind fun e =>
    e.sendInstrs b5Encoder) = none := by decide +kernel

/-- An Insert Count Increment of zero is a decoder stream error (§4.4.3). -/
example : (bEncoder3.bind fun e => e.receive [0x00]) = none := by decide +kernel
/-- So is an increment beyond the insert count (§4.4.3). -/
example : (bEncoder3.bind fun e => e.receive [0x01]) = none := by decide +kernel
/-- A second Section Acknowledgment for stream 4 is a decoder stream error (§4.4.1). -/
example : (bEncoder2.bind fun e => e.receive [0x84]) = none := by decide +kernel

/-- A second stream that could block exceeds `SETTINGS_QPACK_BLOCKED_STREAMS = 1` (§2.1.2). -/
example : ((bEncoder0.sendInstrs b2Encoder).bind fun e => (e.sendSection 4 2 [0, 1]).bind
    fun e => e.sendSection 8 1 [0]) = none := by decide +kernel

/-- Run the decoder: encoder stream octets, then a field section on a stream. -/
def Decoder.step (d : Decoder) (enc : List UInt8) :
    Option Decoder :=
  (decodeEncoderInstrs enc).bind fun is => go d is
where
  go (d : Decoder) : List EncoderInstr → Option Decoder
    | [] => some d
    | i :: is => (d.onEncoderInstr i).toOption.bind fun d => go d is

/-- A field section's octets on a stream: the decoder, the fields, the emitted instruction's
octets. -/
def Decoder.sectionBytes (d : Decoder) (sid : Nat) (xs : List UInt8) :
    Option (Decoder × Option (List Entry) × List UInt8) :=
  (decodeEncodedSection xs).bind fun s =>
    (d.onSection sid s).toOption.map fun (d', out, ins) =>
      (d', out, (ins.map DecoderInstr.encode).getD [])

/-- The decoder of Appendix B (maximum capacity 220, one blocked stream allowed). -/
def bDecoder0 : Decoder := Decoder.init 220 1

/-- B.1: decoded without acknowledgment (Required Insert Count 0). -/
example : ((bDecoder0.sectionBytes 0 b1Section).map fun (_, out, ins) => (out, ins)) =
    some (some [Entry.ofStrings ":path" "/index.html"], []) := by decide +kernel

/-- B.2: after the encoder stream, stream 4 decodes and the decoder emits `84`. -/
def bDecoder2 : Option (Decoder × Option (List Entry) × List UInt8) :=
  (bDecoder0.step b2Encoder).bind fun d => d.sectionBytes 4 b2Section

example : (bDecoder2.map fun (_, out, ins) => (out, ins)) =
    some (some [Entry.ofStrings ":authority" "www.example.com",
      Entry.ofStrings ":path" "/sample/path"], [0x84]) := by decide +kernel

/-- B.3: after the speculative insertion the decoder emits Insert Count Increment `01`. -/
def bDecoder3 : Option Decoder :=
  bDecoder2.bind fun (d, _, _) => d.step b3Encoder

example : (bDecoder3.map fun d => (d.insertCountIncrement.2.map DecoderInstr.encode)) =
    some (some [0x01]) := by decide +kernel

/-- B.4: the encoder stream is delayed, so stream 8 blocks (Required Insert Count 4 > 3); the
decoder then abandons the stream and emits Stream Cancellation `48`. -/
example : ((bDecoder3.map fun d => d.insertCountIncrement.1).bind fun d =>
    (d.sectionBytes 8 b4Section).map fun (d', out, ins) =>
      (d'.blocked, out, ins, (d'.cancelStream 8).2.encode, (d'.cancelStream 8).1.blocked)) =
    some ([8], none, [], [0x48], []) := by decide +kernel

/-- With one blocked stream allowed, a second blocked stream is `QPACK_DECOMPRESSION_FAILED`
(§2.1.2). -/
example : ((bDecoder0.sectionBytes 4 b2Section).bind fun (d, _, _) =>
    d.sectionBytes 8 b4Section) = none := by decide +kernel

end Silmaril.Net.Qpack
