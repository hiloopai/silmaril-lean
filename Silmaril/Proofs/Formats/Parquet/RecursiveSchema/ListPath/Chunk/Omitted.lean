module

public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Chunk.Defs

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk

open Silmaril.Formats
open Parquet
open Parquet.RecursiveSchema.ListPath.Chunk
open Parquet.RecursiveSchema.Repeated.Chunk (LevelBlock LevelWire V2LevelWire V2SectionsWireWith bytesAt)

variable {P : Type} [ScanShape P]

private theorem v1_zero {limits : Hybrid.Limits} {maximum count : Nat} {physical : List UInt8}
    {levels : List Nat} {source : Bytes} {span : Footer.Span}
    (zero : maximum = 0)
    (wire : LevelWire limits maximum count (Bytes.ofList physical) ⟨levels, Bytes.empty⟩)
    (slice : source.slice? span.start (some span.stop) = some (Bytes.ofList physical)) :
    span.start = span.stop ∧ levels = List.replicate count 0 := by
  have omitted : ∀ {body block}, LevelWire limits maximum count body block →
      block = ⟨List.replicate count 0, body⟩ := by
    intro body block read
    cases read with
    | omitted => rfl
    | encoded nonzero => exact False.elim (nonzero zero)
  have block := omitted wire
  have payload := congrArg LevelBlock.tail block
  change Bytes.empty = Bytes.ofList physical at payload
  have length := Bytes.length_of_slice? slice
  rw [← payload] at length
  have ordered := (Bytes.slice?_eq_some_iff.mp slice).1
  simp only [Bytes.length_empty, Option.getD_some] at length ordered
  exact ⟨by omega, congrArg LevelBlock.levels block⟩

public theorem section_zero_repetition {limits : Hybrid.Limits} {plan : P} {count : Nat} {input : SectionSource}
    {spans : Sections} {reps defs : List Nat} {suffix : Bytes}
    (wire : SectionsWire limits plan count input spans reps defs suffix)
    (zero : (ScanShape.shape plan).repetitions = 0) :
    spans.repetition.start = spans.repetition.stop ∧ reps = List.replicate count 0 := by
  obtain ⟨_, _, levels, _, _, _, _, _, _, slice, _, _⟩ := wire.original
  exact v1_zero zero levels slice

public theorem section_zero_definition {limits : Hybrid.Limits} {plan : P} {count : Nat} {input : SectionSource}
    {spans : Sections} {reps defs : List Nat} {suffix : Bytes}
    (wire : SectionsWire limits plan count input spans reps defs suffix)
    (zero : (ScanShape.shape plan).definitions = 0) :
    spans.definition.start = spans.definition.stop ∧ defs = List.replicate count 0 := by
  obtain ⟨_, _, _, levels, _, _, _, _, _, _, slice, _⟩ := wire.original
  exact v1_zero zero levels slice

private theorem v2_zero {limits : Hybrid.Limits} {maximum count : Nat} {bytes : Bytes} {levels : List Nat}
    (zero : maximum = 0) (wire : V2LevelWire limits maximum count bytes levels) :
    bytes.length = 0 ∧ levels = List.replicate count 0 := by
  cases wire with
  | omitted _ length _ _ => exact ⟨length, rfl⟩
  | encoded nonzero => exact False.elim (nonzero zero)

private theorem v2_extents {limits : Parquet.RecursiveSchema.Chunk.Limits} {rep defn : Nat}
    {source : Bytes} {frame : Page.Frame} {info : Page.DataV2}
    {parts : Parquet.RecursiveSchema.Repeated.Chunk.V2Sections}
    (kind : frame.value.kind = .dataV2 info)
    (wire : V2SectionsWireWith limits rep defn source frame info parts) :
    (bytesAt source parts.spans.repetition).length = info.repetitionBytes ∧
      (bytesAt source parts.spans.definition).length = info.definitionBytes := by
  have repLength := Bytes.length_of_slice? (wire.slices parts.spans.repetition (by simp))
  have defLength := Bytes.length_of_slice? (wire.slices parts.spans.definition (by simp))
  have spans := wire.spans
  simp only [Page.Frame.v2Spans, kind] at spans
  split at spans
  · have exactSpans := (Option.some.inj spans).symm
    rw [exactSpans] at repLength defLength ⊢
    exact ⟨by simpa using repLength, by simpa using defLength⟩
  · contradiction

public theorem v2_zero_repetition {limits : Limits} {plan : P} {wrappers : List Nat}
    {source : Bytes} {frame : Page.Frame} {start : State} {remaining ceiling : Nat} {decoded : Decoded}
    {codec : Codec} {encoding : ValueEncoding}
    (wire : V2PageWire limits plan wrappers source frame start remaining ceiling decoded codec encoding)
    (zero : (ScanShape.shape plan).repetitions = 0) :
    ∃ info, frame.value.kind = .dataV2 info ∧ info.repetitionBytes = 0 ∧ info.numRows = info.numValues := by
  obtain ⟨info, _, _, _, kind, _, _, _, levels, _, _, _, rows, _, _, _, _⟩ := wire.original
  have ⟨bytes, logical⟩ := v2_zero zero levels.repetitions
  rw [logical, List.count_replicate_self] at rows
  exact ⟨info, kind, (v2_extents kind levels).1.symm.trans bytes, rows.symm⟩

private theorem atoms_present {levels : List (Nat × Nat)}
    {words : List (Option Parquet.RecursiveSchema.Chunk.Word)}
    (present : ∀ word ∈ words, word.isSome = true) :
    (atoms levels words).countP (·.word.isNone) = 0 := by
  induction levels generalizing words with
  | nil => rfl
  | cons level tail ih =>
    obtain ⟨rep, defn⟩ := level
    cases words with
    | nil => rfl
    | cons word rest =>
      have head := present word (by simp)
      have suffix := ih (words := rest) (fun item member => present item (by simp [member]))
      cases word with
      | none => contradiction
      | some word => simpa [atoms, List.zipWith] using suffix

public theorem v2_zero_definition {limits : Limits} {plan : P} {wrappers : List Nat}
    {source : Bytes} {frame : Page.Frame} {start : State} {remaining ceiling : Nat} {decoded : Decoded}
    {codec : Codec} {encoding : ValueEncoding}
    (wire : V2PageWire limits plan wrappers source frame start remaining ceiling decoded codec encoding)
    (zero : (ScanShape.shape plan).definitions = 0) :
    ∃ info, frame.value.kind = .dataV2 info ∧ info.definitionBytes = 0 ∧ info.numNulls = 0 := by
  obtain ⟨info, _, _, checked, kind, _, _, _, levels, _, _, _, _, nulls, _, slots, rfl⟩ := wire.original
  have ⟨bytes, logical⟩ := v2_zero zero levels.definitions
  have ⟨words, _, _, aligned, exactAtoms⟩ := slots.original
  have present (word : Option Parquet.RecursiveSchema.Chunk.Word) (member : word ∈ words) :
      word.isSome = true := by
    have included := List.mem_map_of_mem (f := Option.isSome) member
    rw [aligned, mask, zero, logical, List.map_replicate] at included
    exact List.eq_of_mem_replicate included
  change checked.atoms.countP (·.word.isNone) = info.numNulls at nulls
  rw [exactAtoms, atoms_present present] at nulls
  exact ⟨info, kind, (v2_extents kind levels).2.symm.trans bytes, nulls.symm⟩

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.ListPath.Chunk
