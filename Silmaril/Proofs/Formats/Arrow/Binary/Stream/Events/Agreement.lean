module

public import Silmaril.Formats.Arrow.Binary.Stream.Events.Defs
import Silmaril.Formats.Arrow.Binary.Stream.Thms
import Init.Omega

public section

namespace Silmaril.Proofs.Formats.Arrow.Binary.Stream.Events

open Silmaril.Formats Silmaril.Formats.Arrow
open Silmaril.Formats.Arrow.Binary.Stream.Events

private theorem pull_prefix (limits : Limits) (framing : Binary.Stream.Framing)
    (field : Binary.Field) {source final : Binary.Stream.Cursor} {records : List Binary.Stream.Batch}
    {ending : Binary.Stream.End} (delivered : Binary.Stream.Prefix source records final)
    (finished : Binary.Stream.EndWire final ending) (reversed : List (Batch field)) :
    Arrow.Events.BatchReader.read.pull (reader limits framing) (schema field)
      (source.remaining + 1) (.at field source) reversed =
      ⟨reversed.reverse ++ records.map (ofBatch field), termination ending⟩ := by
  induction delivered generalizing reversed with
  | stop source =>
    cases ending with
    | eos offset =>
      have next : source.next = .ok none := finished.2.2.2
      simp [Arrow.Events.BatchReader.read.pull, reader, next, termination, Except.mapError, Except.map]
    | failed failure =>
      have next : source.next = .error failure := finished.2.2
      simp [Arrow.Events.BatchReader.read.pull, reader, next, termination, Except.mapError, Except.map]
  | @more source record rest final size envelope budget layout next preceding ih =>
    have calls : (source.advance record).remaining + 1 = source.remaining := by
      show source.remaining - 1 + 1 = source.remaining
      omega
    have adapted : (reader limits framing).next (.at field source) =
        .ok (some (ofBatch field record, .at field (source.advance record))) := by
      simp [reader, next, Except.mapError, Except.map]
    rw [Arrow.Events.BatchReader.read.pull, adapted]
    simpa [calls, List.reverse_cons, List.append_assoc] using
      ih finished (ofBatch field record :: reversed)

theorem pull_exact (limits : Limits) (framing : Binary.Stream.Framing)
    (field : Binary.Field) (source : Binary.Stream.Cursor) :
    Arrow.Events.BatchReader.read.pull (reader limits framing) (schema field)
      (source.remaining + 1) (.at field source) [] = ofTrace field source.drain := by
  obtain ⟨_, delivered, finished⟩ := Binary.Stream.drain_sound source
  simpa [ofTrace] using pull_prefix limits framing field delivered finished []

theorem readAll_exact (limits : Limits) (framing : Binary.Stream.Framing) (input : KBytes) :
    readAll limits framing input =
      (((Binary.Stream.readAll limits framing input).mapError .schema).map fun (field, trace) =>
        ⟨schema field, ofTrace field trace⟩) := by
  cases opened : Binary.Stream.openInput limits framing input with
  | error cause =>
    simp [readAll, Arrow.Events.BatchReader.read, reader, Binary.Stream.readAll,
      opened, Except.mapError, Except.map]
  | ok source =>
    have remaining : source.remaining = limits.batches := by
      obtain ⟨_, _, _, _, _, rfl⟩ := Binary.Stream.openInput_sound opened
      rfl
    unfold readAll Arrow.Events.BatchReader.read Binary.Stream.readAll
    simp only [reader, opened, Except.mapError, Except.map]
    rw [← remaining]
    exact congrArg (fun trace : Trace source.field => (Except.ok ⟨schema source.field, trace⟩ : EventStream))
      (pull_exact limits framing source.field source)

theorem readAll_failure {limits : Limits} {framing : Binary.Stream.Framing} {input : KBytes}
    {field : Binary.Field} {trace : Binary.Stream.Trace} {failure : Binary.Stream.Failure}
    (native : Binary.Stream.readAll limits framing input = .ok (field, trace))
    (failed : trace.terminal = .failed failure) :
    ∃ start final, Binary.Stream.SchemaWire limits framing input start ∧ start.field = field ∧
      Binary.Stream.Prefix start trace.batches final ∧
      readAll limits framing input = .ok ⟨schema field,
        ⟨trace.batches.map (ofBatch field), .readError (.record failure)⟩⟩ ∧
      failure.ordinal = trace.batches.length ∧ failure.offset = final.offset ∧
      final.next = .error failure := by
  obtain ⟨start, final, opened, declares, delivered, ordinal, offset, cause⟩ :=
    Binary.Stream.readAll_failed_prefix native failed
  refine ⟨start, final, opened, declares, delivered, ?_, ordinal, offset, ?_⟩
  · simp [readAll_exact, native, ofTrace, failed, termination, Except.mapError, Except.map]
  · have first : start.ordinal = 0 := by
      obtain ⟨_, _, _, _, _, rfl⟩ := opened
      rfl
    have index : failure.ordinal = final.ordinal := by
      rw [Binary.Stream.Prefix.ordinal delivered, first, Nat.zero_add]
      exact ordinal
    cases failure
    simp_all [Binary.Stream.Cursor.next, Binary.Stream.Cursor.failure, Except.mapError, Except.map]

end Silmaril.Proofs.Formats.Arrow.Binary.Stream.Events
