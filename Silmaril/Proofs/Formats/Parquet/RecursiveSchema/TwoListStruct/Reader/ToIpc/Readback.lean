module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.ToIpc.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.Events.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.Thms
import Silmaril.Formats.Arrow.RecursiveSchema.Stream.Events.ToIpc.Thms

namespace Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.ToIpc

open Silmaril.Formats
open Parquet
open Parquet.RecursiveSchema.TwoListStruct.Reader (Limits readAll readAll_wire)
open Parquet.RecursiveSchema.TwoListStruct.Reader.ToIpc
open Parquet.RecursiveSchema.TwoListStruct.Reader.Events (readProjected readProjected_wire)
open Parquet.Reader.Recursive (Selection)
open Arrow.RecursiveSchema.Stream.Events (Signature declarations eraseBatch)
open Arrow.RecursiveSchema.Stream.Events.ToIpc (schemaOf_exact)

public theorem convert_readback {schemaLimits : Snapshot.Limits} {limits : Limits}
    {ipc : Arrow.RecursiveSchema.Batch.Limits} {input : Bytes} {selection : Selection} {wire : KBytes}
    (written : convert schemaLimits limits ipc input selection = .ok wire) :
    Readback schemaLimits limits ipc input selection wire := by
  cases projected : readProjected schemaLimits limits input selection with
  | error cause =>
    simp [convert, projected, Arrow.RecursiveSchema.Stream.Events.ToIpc.emit] at written
  | ok selected =>
    obtain ⟨source, trace⟩ := selected
    obtain ⟨ended, certificate⟩ := Arrow.RecursiveSchema.Stream.Events.ToIpc.emit_readback
      (by simpa [convert, projected] using written)
    obtain ⟨_, originalTrace, opened, original, sourceWire, _, declared, batches, terminal⟩ :=
      readProjected_wire projected
    have groups : readAll limits opened.schema = .ok (originalTrace.batches.map eraseBatch) :=
      sourceWire.logical.completed.complete.mp (terminal.symm.trans ended)
    rw [schemaOf_exact declared, batches] at certificate
    exact ⟨opened, _, original, groups, readAll_wire groups, certificate⟩

public theorem agrees_events {schemaLimits : Snapshot.Limits} {limits : Limits}
    {ipc : Arrow.RecursiveSchema.Batch.Limits} {input : Bytes} {selection : Selection} {wire : KBytes}
    {events : Σ source : Signature, Parquet.RecursiveSchema.TwoListStruct.Reader.Events.Trace source}
    {native : Σ source : Signature, Arrow.RecursiveSchema.Stream.Events.Trace source}
    (projected : readProjected schemaLimits limits input selection = .ok events)
    (written : convert schemaLimits limits ipc input selection = .ok wire)
    (readback : Arrow.RecursiveSchema.Stream.Events.read ipc wire = .ok native) :
    declarations native.1 = declarations events.1 ∧
      native.2.batches.map eraseBatch = events.2.batches.map eraseBatch ∧ native.2.termination = .eos := by
  obtain ⟨_, _, _, _, _, _, declared, _, _⟩ := readProjected_wire projected
  have names := declared
  rw [← schemaOf_exact declared] at names
  obtain ⟨source, trace⟩ := events
  exact Arrow.RecursiveSchema.Stream.Events.ToIpc.agrees_events names
    (by simpa [convert, projected] using written) readback

end Silmaril.Proofs.Formats.Parquet.RecursiveSchema.TwoListStruct.Reader.ToIpc
