module

public import Silmaril.Formats.Arrow.LargeUtf8.Stream.Events.Defs
import Silmaril.Proofs.Formats.Arrow.LargeUtf8.Stream.Events.Source
import Silmaril.Formats.Arrow.LargeUtf8.StreamWriter.Thms
import Silmaril.Formats.Arrow.Events.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.LargeUtf8.Stream.Events

open Silmaril Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Relational
open LargeUtf8.Stream.Events

theorem emit_one (limits : Limits) (field : LargeUtf8.Field) (trace : Trace field)
    (done : trace.termination = .eos) :
    emit limits (.ok ⟨schema field, trace⟩) =
      (LargeUtf8.StreamWriter.emit limits field (trace.batches.map slots)).mapError .writer := by
  simp [emit, schema, done]
  rfl

private theorem ofSlots {field : LargeUtf8.Field} (batch : Batch field) :
    ofValues field (slots batch) = batch := by
  apply AlignedColumns.ext
  · exact batch.length_eq ⟨0, Nat.zero_lt_one⟩
  · funext i
    have : Subsingleton (Fin (schema field).width) := inferInstanceAs (Subsingleton (Fin 1))
    have same : i = ⟨0, Nat.zero_lt_one⟩ := Subsingleton.elim _ _
    subst i
    rfl

theorem emit_readback {limits : Limits} {field : LargeUtf8.Field} {trace : Trace field} {wire : KBytes}
    (done : trace.termination = .eos) (written : emit limits (.ok ⟨schema field, trace⟩) = .ok wire) :
    ∃ native, LargeUtf8.Stream.read limits .modern wire = .ok native ∧
      LargeUtf8.Stream.StreamWire limits .modern wire native ∧
      LargeUtf8.StreamWriter.Agrees field (trace.batches.map slots) native ∧
      readAll limits .modern wire = .ok ⟨schema field, trace⟩ := by
  rw [emit_one limits field trace done] at written
  cases emitted : LargeUtf8.StreamWriter.emit limits field (trace.batches.map slots) with
  | error cause => simp [emitted, Except.mapError] at written
  | ok bytes =>
    simp [emitted, Except.mapError] at written
    subst bytes
    obtain ⟨native, decoded, agrees, wireProof, _⟩ := LargeUtf8.StreamWriter.emit_readback emitted
    refine ⟨native, decoded, wireProof, agrees, ?_⟩
    obtain ⟨fieldEq, strings⟩ := agrees
    rw [read_success decoded, fieldEq]
    have batchEq : native.batches.map (ofBatch field) = trace.batches := by
      change (native.batches.map fun batch => ofValues field batch.values) = trace.batches
      have valuesEq := congrArg (List.map (ofValues field)) strings
      simpa [List.map_map, Function.comp_def, ofSlots] using valuesEq
    cases trace with
    | mk batches termination => simp_all

private theorem schema_one {signature : Signature} (one : signature.width = 1) :
    ∃ field, signature = schema field := by
  cases signature with
  | mk width kind =>
    change width = 1 at one
    subst width
    let zero : Fin 1 := 0
    cases exactKind : kind zero with
    | mk field tag =>
      cases tag
      refine ⟨field, ?_⟩
      change PositionalSchema.mk 1 kind = PositionalSchema.mk 1 (fun _ => (field, .largeUtf8))
      congr 1
      funext i
      have same : i = zero := Subsingleton.elim _ _
      rw [same, exactKind]

theorem emit_events {limits : Limits} {source : EventStream} {wire : KBytes}
    (written : emit limits source = .ok wire) :
    readAll limits .modern wire = source := by
  cases source with
  | error cause => simp [emit] at written
  | ok pair =>
    obtain ⟨signature, trace⟩ := pair
    by_cases one : signature.width = 1
    · obtain ⟨field, rfl⟩ := schema_one one
      cases done : trace.termination with
      | eos =>
        obtain ⟨_, _, _, _, observed⟩ := emit_readback done written
        exact observed
      | closed => simp [emit, done] at written
      | readError cause => simp [emit, done] at written
      | closeError cause => simp [emit, done] at written
    · cases done : trace.termination <;> simp [emit, done, one] at written

private theorem terminal_of_emit {limits : Limits} {field : LargeUtf8.Field} {trace : Trace field}
    {wire : KBytes} (written : emit limits (.ok ⟨schema field, trace⟩) = .ok wire) :
    trace.termination = .eos := by
  cases done : trace.termination <;> simp [emit, done] at written ⊢

theorem emit_rechunk {limits : Limits} {field : LargeUtf8.Field} {left right : Trace field}
    {first second : KBytes} (firstWritten : emit limits (.ok ⟨schema field, left⟩) = .ok first)
    (secondWritten : emit limits (.ok ⟨schema field, right⟩) = .ok second) (rows : left.rows = right.rows) :
    Arrow.Events.EventStream.Equivalent (readAll limits .modern first) (readAll limits .modern second) := by
  rw [emit_events firstWritten, emit_events secondWritten]
  exact Arrow.Events.EventStream.equivalent_open_iff.mpr
    ⟨rows, (terminal_of_emit firstWritten).trans (terminal_of_emit secondWritten).symm⟩

theorem transcode_exact {readLimits writeLimits : Limits} {framing : LargeUtf8.Stream.Framing}
    {input output : KBytes} (written : emit writeLimits (readAll readLimits framing input) = .ok output) :
    TranscodeWire readLimits writeLimits framing input output ∧
      readAll writeLimits .modern output = readAll readLimits framing input := by
  have agreed := readAll_exact readLimits framing input
  cases admitted : admit readLimits framing input with
  | error error =>
    rw [admitted] at agreed
    simp [agreed.1, emit] at written
  | ok checked =>
    obtain ⟨field, offset⟩ := checked
    rw [admitted] at agreed
    obtain ⟨trace, eventsEq, source⟩ := agreed
    cases native : LargeUtf8.Stream.read readLimits framing input with
    | error error =>
      simp only [SourceWire, native] at source
      obtain ⟨records, final, cause, delivered, failed, same, rfl⟩ := source
      simp [eventsEq, emit] at written
    | ok original =>
      simp only [SourceWire, native] at source
      obtain ⟨rfl, originalWire, rfl⟩ := source
      rw [eventsEq] at written
      obtain ⟨outputRead, decoded, outputWire, values, observation⟩ := emit_readback rfl written
      refine ⟨⟨original, outputRead, native, originalWire, decoded, outputWire, ?_⟩, ?_⟩
      · have slotMap : (original.batches.map (ofBatch original.field)).map slots =
            original.batches.map LargeUtf8.Stream.Batch.values := by
          rw [List.map_map]
          rfl
        rw [← slotMap]
        exact values
      · simpa [eventsEq] using observation

theorem transcode_late_error {readLimits writeLimits : Limits} {framing : LargeUtf8.Stream.Framing}
    {input : KBytes} {field : LargeUtf8.Field} {offset : Nat} {error : LargeUtf8.Stream.Error}
    (opened : admit readLimits framing input = .ok (field, offset))
    (failed : LargeUtf8.Stream.read readLimits framing input = .error error) :
    ∃ records final cause,
      Prefix readLimits framing input field ⟨readLimits.batches, 0, offset⟩ records final ∧
      readNext readLimits framing input field final = .error error ∧ error = final.failure cause ∧
      readAll readLimits framing input = .ok ⟨schema field, ⟨records.map (ofBatch field), .readError error⟩⟩ ∧
      emit writeLimits (readAll readLimits framing input) = .error (.termination (.readError error)) := by
  have agreed := readAll_exact readLimits framing input
  rw [opened] at agreed
  obtain ⟨trace, eventsEq, source⟩ := agreed
  simp only [SourceWire, failed] at source
  obtain ⟨records, final, cause, delivered, stop, same, rfl⟩ := source
  exact ⟨records, final, cause, delivered, same.symm ▸ stop, same, eventsEq, by simp [eventsEq, emit]⟩

end Silmaril.Proofs.Formats.Arrow.LargeUtf8.Stream.Events
