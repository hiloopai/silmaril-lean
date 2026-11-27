module

public import Silmaril.Formats.Parquet.RecursiveSchema.Chunk.Defs
import Silmaril.Formats.Parquet.Page.Checksum.Thms
import Silmaril.Formats.Parquet.FlatPage.Thms
import Silmaril.Formats.Parquet.Hybrid.Thms
import Silmaril.Formats.Parquet.Plain.Thms
import Mathlib.Data.List.Forall2

@[expose] public section

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Chunk

open Silmaril.Formats (Bytes)
open Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.RecursiveSchema (Leaf Presence)
open Silmaril.Formats.Parquet.RecursiveSchema.Chunk

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

public theorem admit_with_wire {requireEqualSizes : Bool} {frame : Page.Frame} {remaining : Nat} {encoding : Int}
    {info : Page.DataV1} (read : admitPageWith requireEqualSizes frame remaining encoding = .ok info) :
    frame.value.kind = .dataV1 info ∧
      (info.encoding = encoding ∧ info.definitionLevelEncoding = 3 ∧ info.repetitionLevelEncoding = 3) ∧
      info.numValues ≤ remaining ∧
      (requireEqualSizes = true → frame.value.uncompressedSize = frame.value.compressedSize) := by
  cases source : frame.value.kind <;> simp only [admitPageWith, source] at read <;> try contradiction
  split at read
  · contradiction
  · rename_i encodings
    split at read
    · contradiction
    · rename_i sizes
      split at read
      · contradiction
      · rename_i count
        cases Except.ok.inj read
        exact ⟨rfl, Classical.not_not.mp encodings, by omega,
          fun identity => Classical.byContradiction fun different => sizes ⟨identity, different⟩⟩

theorem admit_wire {frame : Page.Frame} {remaining : Nat} {info : Page.DataV1}
    (read : admitPage frame remaining = .ok info) : HeaderWire frame remaining info := by
  obtain ⟨kind, encodings, count, sizes⟩ := admit_with_wire read
  exact ⟨kind, encodings, sizes rfl, count⟩

theorem definitions_wire {leaf : Leaf} {limits : Hybrid.Limits} {count : Nat} {body : Bytes}
    {definitions : Definitions} (read : readDefinitions leaf limits count body = .ok definitions) :
    DefinitionWire leaf limits count body definitions ∧ definitions.levels.length = count := by
  unfold readDefinitions at read
  split at read
  · rename_i required
    split at read
    · contradiction
    · rename_i cap
      cases Except.ok.inj read
      exact ⟨.required required (by omega) (by omega), List.length_replicate⟩
  · rename_i optional
    obtain ⟨parts, split, read⟩ := bind_ok read
    obtain ⟨levels, decoded, packaged⟩ := bind_ok read
    have sections := FlatPage.splitV1Optional_ok_iff.mp (from_mapError split)
    obtain ⟨lengthBytes, size, word, bounded, bodyBytes⟩ := sections
    have exactLevels := Hybrid.decode_ok_iff.mp (from_mapError decoded)
    cases Except.ok.inj packaged
    exact ⟨.optional optional size word bounded bodyBytes exactLevels.2.2.2.2,
      Hybrid.decode_length (from_mapError decoded)⟩

private theorem mapM_ordered {α β ε : Type} {decode : α → Except ε β}
    {input : List α} {output : List β} (accepted : input.mapM decode = .ok output) :
    List.Forall₂ (fun item value => decode item = .ok value) input output := by
  induction input generalizing output with
  | nil =>
    simp only [List.mapM_nil, pure, Except.pure, Except.ok.injEq] at accepted
    subst output
    exact .nil
  | cons item rest ih =>
    rw [List.mapM_cons] at accepted
    obtain ⟨first, decoded, accepted⟩ := bind_ok accepted
    obtain ⟨tail, remaining, accepted⟩ := bind_ok accepted
    cases Except.ok.inj accepted
    exact .cons decoded (ih remaining)

theorem classification_wire {leaf : Leaf} {firstRow : Nat} {levels : List Nat} {states : List Presence}
    (accepted : classifyLevels leaf firstRow levels = .ok states) :
    ClassificationWire leaf firstRow levels states := by
  refine List.Forall₂.imp ?_ (mapM_ordered accepted)
  intro position state hit
  cases position
  exact from_mapError hit

theorem fill_wire {states : List Presence} {words : List Word} {reversed slots : List Slot}
    (filled : fill states words reversed = .ok slots) :
    slots.map Slot.presence = reversed.reverse.map Slot.presence ++ states ∧
      slots.filterMap Slot.word? = reversed.reverse.filterMap Slot.word? ++ words := by
  induction states generalizing words reversed slots with
  | nil =>
    cases words with
    | nil =>
      cases Except.ok.inj filled
      simp
    | cons _ _ => simp [fill] at filled
  | cons state rest ih =>
    cases state with
    | absent location =>
      have result := ih (reversed := .absent location :: reversed) filled
      have absentWord : [Slot.absent location].filterMap Slot.word? = [] := rfl
      simpa [List.reverse_cons, List.map_append, List.filterMap_append, Slot.presence,
        absentWord, List.append_assoc] using result
    | value =>
      cases words with
      | nil => simp [fill] at filled
      | cons word words =>
        have result := ih (reversed := .value word :: reversed) filled
        simpa [List.reverse_cons, List.map_append, List.filterMap_append, Slot.presence,
          Slot.word?, List.append_assoc] using result

private theorem checked_payload {maxBytes : Nat} {source : Bytes} {frame : Page.Frame}
    {checksum : Page.Checksum.Status}
    (checked : Page.Checksum.verify maxBytes source frame = .ok checksum) :
    source.slice? frame.payload.start (some frame.payload.stop) =
      some (Page.Checksum.payloadBytes source frame) ∧
      (Page.Checksum.payloadBytes source frame).length = frame.value.compressedSize := by
  apply Page.Checksum.payload_exact
  cases checksum with
  | absent => exact (Page.Checksum.verify_absent_iff.mp checked).2.1
  | valid crc => exact (Page.Checksum.verify_valid_iff.mp checked).2.1

theorem decodePage_wire {limits : Limits} {leaf : Leaf} {source : Bytes} {frame : Page.Frame}
    {firstRow remaining : Nat} {slots : List Slot}
    (read : decodePage limits leaf source frame firstRow remaining = .ok slots) :
    PageWire limits leaf source frame firstRow remaining slots := by
  unfold decodePage at read
  obtain ⟨info, header, read⟩ := bind_ok read
  obtain ⟨checksum, checked, read⟩ := bind_ok read
  obtain ⟨defs, split, read⟩ := bind_ok read
  obtain ⟨states, classified, read⟩ := bind_ok read
  obtain ⟨values, decoded, filled⟩ := bind_ok read
  have verified := from_mapError checked
  obtain ⟨payload, bodySize⟩ := checked_payload verified
  obtain ⟨levels, levelCount⟩ := definitions_wire split
  have classification := classification_wire classified
  have stateCount : states.length = info.numValues := by
    have aligned := classification.length_eq
    simpa only [List.length_zipIdx, levelCount] using aligned.symm
  have consumed := Plain.decodeFixedWidth_ok_iff.mp (from_mapError decoded)
  obtain ⟨_, words, bytes, wordsCount, width, ordered⟩ := consumed
  obtain ⟨presence, scalars⟩ := fill_wire filled
  simp only [List.reverse_nil, List.map_nil, List.filterMap_nil, List.nil_append] at presence scalars
  have slotCount : slots.length = info.numValues := by
    simpa only [List.length_map, stateCount] using congrArg List.length presence
  exact ⟨info, Page.Checksum.payloadBytes source frame, defs, states, words, checksum,
    admit_wire header, verified, payload, bodySize, levels, classification, bytes, wordsCount,
    width, presence, scalars.trans ordered, slotCount⟩

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.Chunk
