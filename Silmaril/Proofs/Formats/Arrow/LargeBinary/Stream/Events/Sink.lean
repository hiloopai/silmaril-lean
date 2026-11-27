module

public import Silmaril.Formats.Arrow.LargeBinary.Stream.Events.Defs
import Silmaril.Proofs.Formats.Arrow.LargeBinary.Stream.Events.Source
import Silmaril.Formats.Arrow.LargeBinary.StreamWriter.Thms
import Silmaril.Formats.Arrow.Events.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.LargeBinary.Stream.Events

open Silmaril Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Relational
open LargeBinary.Stream.Events

theorem emit_one (limits : Limits) (field : LargeBinary.Field) (trace : Trace field)
    (done : trace.termination = .eos) :
    emit limits (.ok ⟨schema field, trace⟩) =
      (LargeBinary.StreamWriter.emit limits field (trace.batches.map slots)).mapError .writer := by
  simp [emit, schema, done]
  rfl

private theorem observe_one {field : LargeBinary.Field} (batch : Batch field) :
    observeBatch batch = ofValues field (Binary.StreamWriter.observe (slots batch)) := by
  apply AlignedColumns.ext
  · simpa [observeBatch, ofValues, Binary.StreamWriter.observe, slots] using
      (batch.length_eq ⟨0, Nat.zero_lt_one⟩).symm
  · funext i
    have : Subsingleton (Fin (schema field).width) := inferInstanceAs (Subsingleton (Fin 1))
    have same : i = ⟨0, Nat.zero_lt_one⟩ := Subsingleton.elim _ _
    subst i
    rfl

theorem emit_readback {limits : Limits} {field : LargeBinary.Field} {trace : Trace field} {wire : KBytes}
    (done : trace.termination = .eos) (written : emit limits (.ok ⟨schema field, trace⟩) = .ok wire) :
    ∃ native, LargeBinary.Stream.read limits .modern wire = .ok native ∧
      LargeBinary.Stream.StreamWire limits .modern wire native ∧
      LargeBinary.StreamWriter.Agrees field (trace.batches.map slots) native ∧
      observe (readAll limits .modern wire) = observe (.ok ⟨schema field, trace⟩) := by
  rw [emit_one limits field trace done] at written
  cases emitted : LargeBinary.StreamWriter.emit limits field (trace.batches.map slots) with
  | error cause => simp [emitted, Except.mapError] at written
  | ok bytes =>
    simp [emitted, Except.mapError] at written
    subst bytes
    obtain ⟨native, decoded, agrees, wireProof, _⟩ := LargeBinary.StreamWriter.emit_readback emitted
    refine ⟨native, decoded, wireProof, agrees, ?_⟩
    obtain ⟨fieldEq, octets⟩ := agrees
    rw [read_success decoded]
    cases fieldEq
    have normalized := congrArg (List.map (ofValues native.field (value := List UInt8))) octets
    have batchMap : @observeBatch (schema native.field) =
        fun batch => ofValues native.field (Binary.StreamWriter.observe (slots batch)) :=
      funext observe_one
    simp only [observe, Except.map, done, List.map_map, batchMap]
    exact congrArg (fun (batches : List (Arrow.Events.Batch (schema native.field) Octets)) =>
      (Except.ok ⟨schema native.field, ⟨batches, .eos⟩⟩ : ObservedEvents)) (by
        simpa [List.map_map, Function.comp_def, ofBatch, slots, ofValues] using normalized)

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
      change PositionalSchema.mk 1 kind = PositionalSchema.mk 1 (fun _ => (field, .largeBinary))
      congr 1
      funext i
      have same : i = zero := Subsingleton.elim _ _
      rw [same, exactKind]

theorem emit_observed {limits : Limits} {source : EventStream} {wire : KBytes}
    (written : emit limits source = .ok wire) :
    observe (readAll limits .modern wire) = observe source := by
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

theorem transcode_exact {readLimits writeLimits : Limits} {framing : LargeBinary.Stream.Framing}
    {input output : KBytes} (written : emit writeLimits (readAll readLimits framing input) = .ok output) :
    TranscodeWire readLimits writeLimits framing input output ∧
      observe (readAll writeLimits .modern output) = observe (readAll readLimits framing input) := by
  have agreed := readAll_exact readLimits framing input
  cases admitted : admit readLimits framing input with
  | error error =>
    rw [admitted] at agreed
    simp [agreed.1, emit] at written
  | ok checked =>
    obtain ⟨field, offset⟩ := checked
    rw [admitted] at agreed
    obtain ⟨trace, eventsEq, source⟩ := agreed
    cases native : LargeBinary.Stream.read readLimits framing input with
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
            original.batches.map Binary.Stream.Batch.values := by
          rw [List.map_map]
          rfl
        rw [← slotMap]
        exact values
      · simpa [eventsEq] using observation

theorem transcode_late_error {readLimits writeLimits : Limits} {framing : LargeBinary.Stream.Framing}
    {input : KBytes} {field : LargeBinary.Field} {offset : Nat} {error : LargeBinary.Stream.Error}
    (opened : admit readLimits framing input = .ok (field, offset))
    (failed : LargeBinary.Stream.read readLimits framing input = .error error) :
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

end Silmaril.Proofs.Formats.Arrow.LargeBinary.Stream.Events
