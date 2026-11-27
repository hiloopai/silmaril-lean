module

public import Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Writer.Defs
import Silmaril.Formats.Arrow.MixedFlat.LargeUtf8.Stream.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.MixedFlat.LargeUtf8.Writer

open Silmaril.Formats Silmaril.Formats.Arrow
open MixedFlat.LargeUtf8.Writer

theorem compile_largeUtf8 {limits : MixedFlat.Limits} {rows position : Nat} {name : String}
    {nullable : Bool} {values : Arrow.LargeUtf8.Column} {physical : MixedFlat.OrderedWriter.PhysicalColumn}
    (written : Column.compile limits rows position (.largeUtf8 name nullable values) = .ok physical) :
    values.length = rows ∧ ∃ node,
      Binary.StreamWriter.checkRecordSize .i64 limits.observation.ipc nullable values Writer.utf8ByteCount =
        .ok node ∧
      physical = ⟨node, none, Binary.StreamWriter.columnPartsFor .i64
        (Arrow.LargeUtf8.StreamWriter.encodeColumn values)⟩ := by
  by_cases length : values.length = rows
  · cases checked : Binary.StreamWriter.checkRecordSize .i64 limits.observation.ipc nullable values
        Writer.utf8ByteCount with
    | error => simp [Column.compile, length, checked, Bind.bind, Except.bind, Except.mapError] at written
    | ok node =>
      simp [Column.compile, length, checked, Bind.bind, Except.bind, Except.mapError, Pure.pure, Except.pure]
        at written
      exact ⟨length, node, rfl, written.symm⟩
  · simp [Column.compile, length] at written

theorem record_readBatch {limits : MixedFlat.Limits} {input : BatchInput}
    (record : Record limits input) {schemaBytes : KBytes}
    (schema : MixedFlat.LargeUtf8.readSchema limits.observation.ipc schemaBytes = .ok input.fields) :
    ∃ decoded,
      MixedFlat.LargeUtf8.readBatch limits schemaBytes record.output.metadataBytes record.output.body =
        .ok decoded ∧ observeBatch decoded = input.observe ∧
      MixedFlat.LargeUtf8.BatchWire limits input.fields record.output.metadata record.output.body decoded := by
  obtain ⟨decoded, parsed, compared⟩ := record.readback
  refine ⟨decoded, ?_, compared, MixedFlat.LargeUtf8.readParsed_sound parsed⟩
  simp [MixedFlat.LargeUtf8.readBatch, schema, record.metadataRead, parsed, Bind.bind, Except.bind,
    Except.mapError]

private theorem trace_eos {limits : MixedFlat.Limits} {framing : MixedFlat.LargeUtf8.Stream.Framing}
    {input : KBytes} {fields : List MixedFlat.LargeUtf8.Field} {fuel ordinal rows offset eos : Nat}
    {batches : List MixedFlat.LargeUtf8.Stream.Batch} {terminal : MixedFlat.LargeUtf8.Stream.Termination}
    (wire : MixedFlat.LargeUtf8.Stream.TraceWire limits framing input fields fuel ordinal rows offset batches terminal)
    (endMarker : terminal = .eos eos) :
    framing.readEnvelope limits.observation.ipc input eos = .ok .eos ∧ eos + framing.prefixSize = input.len := by
  induction wire with
  | stop stop =>
    cases stop <;> simp_all
  | more _ _ _ ih => exact ih endMarker

theorem emit_readback {limits : MixedFlat.Limits} {fields : List MixedFlat.LargeUtf8.Field}
    {batches : List BatchInput} {wire : KBytes} (written : emit limits fields batches = .ok wire) :
    ∃ decoded eos, MixedFlat.LargeUtf8.Stream.read limits .modern wire = .ok decoded ∧
      Agrees fields batches decoded ∧ decoded.trace.termination = .eos eos ∧
      MixedFlat.LargeUtf8.Stream.StreamWire limits .modern wire decoded ∧
      Arrow.readEnvelope limits.observation.ipc wire eos = .ok .eos ∧ eos + 8 = wire.len := by
  cases serialized : serialize limits fields batches with
  | error => simp [emit, serialized, Bind.bind, Except.bind] at written
  | ok actual =>
    cases decoded : MixedFlat.LargeUtf8.Stream.read limits .modern actual with
    | error =>
      simp [emit, serialized, decoded, Bind.bind, Except.bind, Except.mapError] at written
    | ok result =>
      cases terminal : result.trace.termination with
      | error =>
        simp [emit, serialized, decoded, terminal, Bind.bind, Except.bind, Except.mapError] at written
      | eos eos =>
        by_cases compared : Agrees fields batches result
        · have same : actual = wire := by
            simpa [emit, serialized, decoded, terminal, compared, Bind.bind, Except.bind, Except.mapError] using written
          subst wire
          have checked := MixedFlat.LargeUtf8.Stream.read_sound decoded
          obtain ⟨_, _, _, traced⟩ := checked.2
          exact ⟨result, eos, decoded, compared, terminal, checked, trace_eos traced terminal⟩
        · simp [emit, serialized, decoded, terminal, compared, Bind.bind, Except.bind, Except.mapError] at written

end Silmaril.Proofs.Formats.Arrow.MixedFlat.LargeUtf8.Writer
