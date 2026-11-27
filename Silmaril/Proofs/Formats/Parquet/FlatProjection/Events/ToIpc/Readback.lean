module

public import Silmaril.Formats.Parquet.FlatProjection.Events.ToIpc.Defs
import Silmaril.Formats.Arrow.MixedFlat.Timestamp.Thms
import Silmaril.Formats.Arrow.MixedFlat.Timestamp.Writer.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.FlatProjection.Events.ToIpc

open Silmaril.Formats
open Silmaril.Formats.Parquet.FlatProjection.Events.ToIpc

theorem emitTrace_readback {limits : Arrow.ObservationLimits} {schema : Schema}
    {trace : Arrow.Events.Trace schema Parquet.FlatProjection.Events.Cell Parquet.FlatProjection.Events.Error}
    {wire : KBytes} (written : emitTrace limits trace = .ok wire) :
    trace.termination = .eos ∧ Arrow.MixedFlat.Timestamp.read limits wire = .ok (observation trace) := by
  cases termination : trace.termination <;> simp [emitTrace, termination] at written
  case eos =>
    cases emitted : Arrow.MixedFlat.Timestamp.Writer.emit limits (observation trace) with
    | error cause => simp [emitted, Except.mapError] at written
    | ok output =>
      simp [emitted, Except.mapError] at written
      exact ⟨rfl, Arrow.MixedFlat.Timestamp.Writer.emit_readback (written ▸ emitted)⟩

theorem convert_readback {limits : Parquet.FlatProjection.Events.Limits} {output : Arrow.ObservationLimits}
    {input : Bytes} {ordinals : Array Nat} {wire : KBytes}
    (written : convert limits output input ordinals = .ok wire) :
    ∃ (schema : Schema)
      (trace : Arrow.Events.Trace schema Parquet.FlatProjection.Events.Cell Parquet.FlatProjection.Events.Error)
      (start : Nat),
      Parquet.FlatProjection.Events.readAll limits input ordinals = .ok ⟨schema, trace⟩ ∧
      trace.termination = .eos ∧
      Arrow.MixedFlat.Timestamp.read output wire = .ok (observation trace) ∧
      Arrow.MixedFlat.Timestamp.readSchema output.ipc wire = .ok (fields schema, start) ∧
      Arrow.MixedFlat.Timestamp.BatchesWire output wire (fields schema) output.ipc.batches 0 start
        (trace.batches.map batchInput) := by
  cases read : Parquet.FlatProjection.Events.readAll limits input ordinals with
  | error cause => simp [convert, read, Except.mapError, Bind.bind, Except.bind] at written
  | ok opened =>
    obtain ⟨schema, trace⟩ := opened
    have emitted : emitTrace output trace = .ok wire := by
      simpa [convert, read, Except.mapError, Bind.bind, Except.bind] using written
    obtain ⟨eos, checked⟩ := emitTrace_readback emitted
    obtain ⟨start, header, batches⟩ := Arrow.MixedFlat.Timestamp.read_wire checked
    exact ⟨schema, trace, start, rfl, eos, checked, header, batches⟩

end Silmaril.Proofs.Formats.Parquet.FlatProjection.Events.ToIpc
