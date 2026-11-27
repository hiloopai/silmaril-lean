module

public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.Chunk.Thms
import Silmaril.Formats.Parquet.Page.Checksum.Thms
import Silmaril.Formats.Parquet.Payload.Thms
import Silmaril.Formats.Parquet.FlatPage.Thms
import Silmaril.Formats.Parquet.Hybrid.Thms
import Silmaril.Formats.Parquet.Plain.Thms

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk

open Silmaril.Formats (Bytes)
open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.RecursiveSchema.Repeated (Leaf Slot)
open Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk

private theorem bind_ok {α β ε : Type} {first : Except ε α} {next : α → Except ε β} {value : β}
    (read : (first >>= next) = .ok value) : ∃ found, first = .ok found ∧ next found = .ok value := by
  cases first with
  | error => contradiction
  | ok result => exact ⟨result, rfl, read⟩

private theorem from_mapError {α ε δ : Type} {first : Except ε α} {wrap : ε → δ} {value : α}
    (read : first.mapError wrap = .ok value) : first = .ok value := by
  cases first with
  | error => simp [Except.mapError] at read
  | ok => simpa only [Except.mapError, Except.ok.injEq] using read

public theorem levels_wire {limits : Hybrid.Limits} {maximum count : Nat} {body : Bytes}
    {result : LevelBlock} (read : readLevels limits maximum count body = .ok result) :
    LevelWire limits maximum count body result ∧ result.levels.length = count := by
  unfold readLevels at read
  split at read
  · rename_i omitted
    split at read
    · contradiction
    · rename_i cap
      cases Except.ok.inj read
      exact ⟨.omitted omitted (by omega) (by omega), List.length_replicate⟩
  · rename_i nonzero
    obtain ⟨parts, split, read⟩ := bind_ok read
    obtain ⟨levels, decoded, packaged⟩ := bind_ok read
    obtain ⟨lengthBytes, size, word, bounded, bodyBytes⟩ :=
      FlatPage.splitV1Optional_ok_iff.mp (from_mapError split)
    have exactLevels := Hybrid.decode_ok_iff.mp (from_mapError decoded)
    cases Except.ok.inj packaged
    exact ⟨.encoded nonzero size word bounded bodyBytes exactLevels.2.2.2.2,
      Hybrid.decode_length (from_mapError decoded)⟩

private theorem classifySlotsFrom_wire {leaf : Leaf} {ceiling : Nat} {reps defs : List Nat}
    {start : State} {reversed : List LevelSlot} {out : Classified}
    (accepted : classifySlotsFrom leaf ceiling reps defs start reversed = .ok out) :
    ∃ levels, out.levels = reversed.reverse ++ levels ∧ SlotsWire leaf ceiling reps defs start levels out.after := by
  induction reps generalizing defs start reversed out with
  | nil =>
    cases defs with
    | cons => simp [classifySlotsFrom] at accepted
    | nil =>
      cases Except.ok.inj accepted
      exact ⟨[], by simp, .nil start⟩
  | cons rep reps ih =>
    cases defs with
    | nil => simp [classifySlotsFrom] at accepted
    | cons defn defs =>
      simp only [classifySlotsFrom] at accepted
      cases classified : leaf.classify start.slot rep defn with
      | error cause => simp [classified] at accepted
      | ok slot =>
        simp only [classified] at accepted
        split at accepted
        · rename_i live
          split at accepted
          · rename_i rows
            obtain ⟨levels, output, wire⟩ := ih accepted
            refine ⟨⟨rep, defn, slot⟩ :: levels, ?_, .cons classified live rows wire⟩
            simpa [List.reverse_cons, List.append_assoc] using output
          · contradiction
        · contradiction

public theorem classifySlots_wire {leaf : Leaf} {ceiling : Nat} {reps defs : List Nat}
    {start : State} {out : Classified}
    (accepted : classifySlots leaf ceiling reps defs start = .ok out) :
    SlotsWire leaf ceiling reps defs start out.levels out.after := by
  obtain ⟨levels, result, wire⟩ := classifySlotsFrom_wire accepted
  simp only [List.reverse_nil, List.nil_append] at result
  exact result.symm ▸ wire

public theorem slot_counts {leaf : Leaf} {ceiling : Nat} {reps defs : List Nat}
    {start stop : State} {slots : List LevelSlot} (wire : SlotsWire leaf ceiling reps defs start slots stop) :
    start.slot + slots.length = stop.slot ∧
      start.rows + slots.countP LevelSlot.startsRow = stop.rows := by
  induction wire with
  | nil => simp
  | @cons rep defn reps defs start classified tail stop _ _ _ _ ih =>
    obtain ⟨slots, rows⟩ := ih
    simp only [State.consume] at slots rows
    by_cases begins : rep = 0 <;>
      simp [LevelSlot.startsRow, begins] at rows ⊢ <;> omega

public theorem original_levels {leaf : Leaf} {ceiling : Nat} {reps defs : List Nat}
    {start stop : State} {slots : List LevelSlot} (wire : SlotsWire leaf ceiling reps defs start slots stop) :
    slots.map (·.repetition) = reps ∧ slots.map (·.definition) = defs := by
  induction wire with
  | nil => simp
  | cons _ _ _ _ ih => simp [ih.1, ih.2]

private theorem checked_extent {maxBytes : Nat} {source : Bytes} {frame : Page.Frame}
    {checksum : Page.Checksum.Status}
    (checked : Page.Checksum.verify maxBytes source frame = .ok checksum) :
    frame.value.compressedSize ≤ maxBytes ∧ Page.Checksum.PayloadWithin source frame := by
  cases checksum with
  | absent => exact let h := Page.Checksum.verify_absent_iff.mp checked; ⟨h.1, h.2.1⟩
  | valid crc => exact let h := Page.Checksum.verify_valid_iff.mp checked; ⟨h.1, h.2.1⟩

public theorem decodeSnappy_wire {bounds : Payload.Bounds} {stored body : Bytes}
    (read : decodeSnappy bounds stored = .ok body) :
    Payload.Decodes bounds.expectedSize .snappy stored.toList body.toList ∧
      stored.length = bounds.compressedSize ∧ stored.length ≤ bounds.compressedLimit ∧
      body.length = bounds.expectedSize ∧ body.length ≤ bounds.outputLimit := by
  unfold decodeSnappy at read
  cases decoded : Payload.decode bounds Payload.Codec.snappy.id stored.toList with
  | error => simp [decoded, Except.mapError, Except.map] at read
  | ok bytes =>
    simp only [decoded, Except.mapError, Except.map, Except.ok.injEq] at read
    subst body
    obtain ⟨codec, id, model, inputSize, inputCap, outputSize, outputCap⟩ := Payload.decode_sound decoded
    have snappy : codec = .snappy := by
      simpa only [Payload.Codec.ofId_id, Option.some.injEq] using id.symm
    subst codec
    simpa using And.intro model (And.intro inputSize (And.intro inputCap (And.intro outputSize outputCap)))

public theorem readV1Body_wire {limits : Limits} {codec : ColumnCodec} {source : Bytes}
    {frame : Page.Frame} {body : Bytes}
    (sizes : (codec == ColumnCodec.uncompressed) = true →
      frame.value.uncompressedSize = frame.value.compressedSize)
    (read : readV1Body limits codec source frame = .ok body) :
    V1BodyWire limits codec source frame body := by
  unfold readV1Body at read
  obtain ⟨checksum, checked, read⟩ := bind_ok read
  have verified := from_mapError checked
  obtain ⟨cap, geometry⟩ := checked_extent verified
  obtain ⟨stored, storedSize⟩ := Page.Checksum.payload_exact geometry
  refine ⟨_, checksum, verified, stored, storedSize, storedSize.symm ▸ cap, ?_⟩
  cases codec with
  | uncompressed =>
    cases Except.ok.inj read
    exact ⟨storedSize.trans (sizes rfl).symm, storedSize.symm ▸ cap, .uncompressed _⟩
  | snappy =>
    obtain ⟨model, _, _, bodySize, bodyCap⟩ := decodeSnappy_wire read
    exact ⟨bodySize, bodyCap, model⟩

public theorem decodeSlots_wire {leaf : Leaf} {reps defs : List Nat} {suffix : Bytes}
    {start : State} {rowCeiling : Nat} {decoded : DecodedPage}
    (read : decodeSlots leaf reps defs suffix start rowCeiling = .ok decoded) :
    DecodedWire leaf reps defs suffix start rowCeiling decoded := by
  unfold decodeSlots at read
  obtain ⟨classified, levelRead, read⟩ := bind_ok read
  obtain ⟨values, valueRead, read⟩ := bind_ok read
  obtain ⟨aligned, alignment, packaged⟩ := bind_ok read
  obtain ⟨_, words, exactWords, wordCount, width, ordered⟩ :=
    Plain.decodeFixedWidth_ok_iff.mp (from_mapError valueRead)
  obtain ⟨mask, positions⟩ := FlatPage.reconstruct_ok_iff.mp (from_mapError alignment)
  cases Except.ok.inj packaged
  exact ⟨classifySlots_wire levelRead, words, exactWords, wordCount, width, mask,
    positions.trans ordered⟩

public theorem decodeV1Page_wire {limits : Limits} {codec : ColumnCodec} {leaf : Leaf} {source : Bytes}
    {frame : Page.Frame} {start : State} {remaining rowCeiling : Nat} {decoded : DecodedPage}
    (read : decodeV1Page limits codec leaf source frame start remaining rowCeiling = .ok decoded) :
    PageWire limits leaf source frame start remaining rowCeiling decoded codec := by
  unfold decodeV1Page at read
  obtain ⟨info, header, read⟩ := bind_ok read
  obtain ⟨body, decodedBody, read⟩ := bind_ok read
  obtain ⟨reps, repRead, read⟩ := bind_ok read
  obtain ⟨defs, defRead, read⟩ := bind_ok read
  obtain ⟨kind, encodings, cap, sizes⟩ :=
    RecursiveSchema.Chunk.admitPageWith_wire (from_mapError header)
  obtain ⟨repetition, repCount⟩ := levels_wire (from_mapError repRead)
  obtain ⟨definition, _⟩ := levels_wire (from_mapError defRead)
  have decodedWire := decodeSlots_wire read
  have count : decoded.levels.length = info.numValues := by
    simpa only [List.length_map, repCount] using congrArg List.length (original_levels decodedWire.slots).1
  exact ⟨info, body, reps, defs, kind, encodings, cap, readV1Body_wire sizes decodedBody,
    repetition, definition, decodedWire, count⟩

public theorem v1_state_counts {limits : Limits} {codec : ColumnCodec} {leaf : Leaf} {source : Bytes}
    {frame : Page.Frame} {start : State} {remaining rowCeiling : Nat} {decoded : DecodedPage}
    (wire : PageWire limits leaf source frame start remaining rowCeiling decoded codec) :
    start.slot + decoded.levels.length = decoded.after.slot ∧
      start.rows + decoded.levels.countP LevelSlot.startsRow = decoded.after.rows := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, slots, _⟩ := wire.original
  exact slot_counts slots.slots

public theorem rejects_closed_continuation {leaf : Leaf} {ceiling rep defn : Nat}
    {reps defs : List Nat} {start : State} {slot : Slot}
    (classified : leaf.classify start.slot rep defn = .ok slot)
    (continuation : rep ≠ 0) (closed : start.live = false) :
    classifySlots leaf ceiling (rep :: reps) (defn :: defs) start =
      .error (.continuationWithoutList start.slot) := by
  simp [classifySlots, classifySlotsFrom, classified, continuation, closed]

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Repeated.Chunk
