module

public import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.Complete.Defs
public import Silmaril.Formats.Parquet.Int32ByteArrayGroup.ToIpc.Defs
import Silmaril.Proofs.Formats.Parquet.MixedV1Writer.FromIpc.Complete.Correctness

public section

namespace Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.Complete

open Int32ByteArrayGroup
open Silmaril.Formats.Relational.NamedTable

variable {source : MixedIpc.Limits} {sink : MixedV1Writer.Multi.Limits} {input : KBytes}
variable {observed : MixedIpc.Prepared}

/-- Equality covers successful bytes and all planning or sink errors for nonempty record lists. -/
theorem convert_nonempty_agrees (read : MixedIpc.read source input = .ok observed)
    (nonempty : observed.batches ≠ []) :
    convert source sink input = convertOrdered source sink input :=
  Proofs.Formats.Parquet.MixedV1Writer.FromIpc.Complete.convert_nonempty_agrees
    read nonempty

/-- The zero-batch branch agrees on the entire result, including any sink refusal. -/
theorem convert_schemaOnly_agrees (read : MixedIpc.read source input = .ok observed)
    (empty : observed.batches = []) :
    convert source sink input = (SchemaOnly.emit sink observed.descriptor).mapError .sink ∧
    SchemaOnly.convert source sink input = (SchemaOnly.emit sink observed.descriptor).mapError .sink :=
  Proofs.Formats.Parquet.MixedV1Writer.FromIpc.Complete.convert_schemaOnly_agrees
    read empty

/-- Both field orders and every batch list retain the exact descriptor and paired
slots through EOS, including every empty batch position. The reverse conversion
uses the writer certification group and footer policies and independent file,
IPC and returned carrier caps. -/
theorem read_roundTrip {returned : MixedIpc.Limits}
    {reverse : File.Limits} {output : KBytes} {parquet : MixedV1Writer.Multi.Encoded}
    (original : MixedIpc.read source input = .ok observed)
    (forward : convert source sink input = .ok parquet)
    (groupLimits : reverse.group = sink.writer.readback)
    (footerLimits : reverse.group.snapshot.footer = sink.writer.footer)
    (backward : ToIpc.convertOrdered reverse returned.mixed parquet.bytes
      (field observed.descriptor.integer) (field observed.descriptor.binary) = .ok output)
    (carrier : output.len ≤ returned.inputBytes) :
    MixedIpc.read returned output = .ok observed :=
  Proofs.Formats.Parquet.MixedV1Writer.FromIpc.Complete.read_roundTrip
    original forward groupLimits footerLimits backward carrier

/-- Exact source admission, including batch errors and carrier limits, precedes all sink work. -/
theorem convert_source_error {cause : MixedIpc.Error}
    (failed : MixedIpc.read source input = .error cause) :
    convert source sink input = .error (.source cause) ∧
    convertOrdered source sink input = .error (.source cause) ∧
    SchemaOnly.convert source sink input = .error (.source cause) := by
  simp [convert, convertOrdered, SchemaOnly.convert, failed, Except.mapError, Bind.bind, Except.bind]

end Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.Complete
