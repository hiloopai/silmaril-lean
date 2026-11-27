module

public import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.Complete.Defs
public import Silmaril.Formats.Parquet.Int32ByteArrayGroup.ToIpc.Defs
import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.RoundTrip.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.MixedV1Writer.FromIpc.Complete

open Silmaril.Formats.Parquet
open MixedV1Writer.FromIpc.Complete
open MixedV1Writer.FromIpc
open Int32ByteArrayGroup
open Silmaril.Formats.Relational.NamedTable

variable {source : MixedIpc.Limits} {sink : MixedV1Writer.Multi.Limits} {input : KBytes}
variable {observed : MixedIpc.Prepared}

/-- Equality covers both successful bytes and any original planning or sink error. -/
theorem convert_nonempty_agrees (read : MixedIpc.read source input = .ok observed)
    (nonempty : observed.batches ≠ []) :
    Complete.convert source sink input = convertOrdered source sink input := by
  cases batches : observed.batches with
  | nil => exact (nonempty batches).elim
  | cons batch tail =>
    simp [Complete.convert, convertOrdered, emitPrepared, read, batches, Except.mapError, Bind.bind, Except.bind]

/-- A checked empty record list can only produce a checked file or a sink error.
Both outcomes agree with the explicit schema-only converter. -/
theorem convert_schemaOnly_agrees (read : MixedIpc.read source input = .ok observed)
    (empty : observed.batches = []) :
    Complete.convert source sink input = (SchemaOnly.emit sink observed.descriptor).mapError .sink ∧
    SchemaOnly.convert source sink input = (SchemaOnly.emit sink observed.descriptor).mapError .sink := by
  simp [Complete.convert, SchemaOnly.convert, emitPrepared, read, empty, Except.mapError, Bind.bind, Except.bind]

theorem read_roundTrip {returned : MixedIpc.Limits}
    {reverse : File.Limits} {output : KBytes} {parquet : MixedV1Writer.Multi.Encoded}
    (original : MixedIpc.read source input = .ok observed)
    (forward : Complete.convert source sink input = .ok parquet)
    (groupLimits : reverse.group = sink.writer.readback)
    (footerLimits : reverse.group.snapshot.footer = sink.writer.footer)
    (backward : ToIpc.convertOrdered reverse returned.mixed parquet.bytes
      (field observed.descriptor.integer) (field observed.descriptor.binary) = .ok output)
    (carrier : output.len ≤ returned.inputBytes) :
    MixedIpc.read returned output = .ok observed := by
  by_cases empty : observed.batches = []
  · obtain ⟨unified, explicit⟩ := convert_schemaOnly_agrees original empty
    rw [unified] at forward
    have emitted : SchemaOnly.convert source sink input = .ok parquet := by
      rw [explicit]
      cases result : SchemaOnly.emit sink observed.descriptor with
      | error cause => simp [result, Except.mapError] at forward
      | ok candidate => simpa [result, Except.mapError] using forward
    rcases observed with ⟨descriptor, batches⟩
    change batches = [] at empty
    subst batches
    exact (RoundTrip.read_roundTripSchemaOnly original emitted groupLimits footerLimits backward carrier).1
  · have emitted : convertOrdered source sink input = .ok parquet :=
      (convert_nonempty_agrees original empty).symm.trans forward
    exact (RoundTrip.read_roundTripOrdered original emitted groupLimits footerLimits backward carrier).1

end Silmaril.Proofs.Formats.Parquet.MixedV1Writer.FromIpc.Complete
