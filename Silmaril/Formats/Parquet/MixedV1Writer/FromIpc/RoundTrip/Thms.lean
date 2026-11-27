module

public import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.Defs
public import Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.SchemaOnly.Defs
public import Silmaril.Formats.Parquet.Int32ByteArrayGroup.ToIpc.Defs
import Silmaril.Proofs.Formats.Parquet.MixedV1Writer.FromIpc.RoundTrip.Correctness

/-! Observational round trip through real nonlegacy mixed Parquet bytes. -/

public section

namespace Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.RoundTrip

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Int32ByteArrayGroup
open Silmaril.Formats.Relational.NamedTable

/-- The returned checked IPC observation has exactly the original descriptor and
ordered batches, including empty batches. Both conversions must succeed. The
reverse reader uses the same group limits as writer certification and may impose
its own aggregate row cap. The returned carrier obeys its own IPC byte cap. -/
theorem read_roundTrip {source returned : MixedIpc.Limits} {sink : MixedV1Writer.Multi.Limits}
    {reverse : File.Limits} {input output : KBytes} {parquet : MixedV1Writer.Multi.Encoded}
    {observed : MixedIpc.Prepared}
    (original : MixedIpc.read source input = .ok observed)
    (forward : convert source sink input = .ok parquet)
    (groupLimits : reverse.group = sink.writer.readback)
    (backward : ToIpc.convert reverse returned.mixed parquet.bytes
      (field observed.descriptor.integer) (field observed.descriptor.binary) = .ok output)
    (carrier : output.len ≤ returned.inputBytes) :
    MixedIpc.read returned output = .ok observed :=
  Proofs.Formats.Parquet.MixedV1Writer.FromIpc.RoundTrip.read_roundTrip original forward groupLimits backward carrier

/-- Ordered IPC readback follows an exact checked footer and the supplied
logical rows at each original group ordinal. -/
theorem read_of_indexed {returned : MixedIpc.Limits} {reverse : File.Limits}
    {bytes : Bytes} {output : KBytes} {descriptor : MixedIpc.Descriptor}
    {batches : List (List MixedIpc.Pair)} {span : Footer.Span} {metadata : Footer.Metadata}
    {projection : Checked (field descriptor.integer) (field descriptor.binary)}
    (opened : Int32ByteArrayGroup.openFile reverse.group bytes
      (field descriptor.integer) (field descriptor.binary) = .ok projection)
    (count : projection.snapshot.groupCount = batches.length)
    (indexed : ∀ i : Fin batches.length,
      projection.readGroup reverse.group i.val = .ok ((batches.get i).map toRow))
    (footer : Footer.readFooter reverse.group.snapshot.footer bytes = .ok (span, metadata))
    (schema : metadata.schema = FlatInt32Writer.Compact.schemaRoot 2 ::
      (physicalOrder descriptor).columns
        (MixedV1Writer.columnIndex (field descriptor.integer) ⟨0, 0⟩).schema
        (MixedV1Writer.byteSchema (MixedV1Writer.columnIndex (field descriptor.binary) ⟨0, 0⟩)))
    (backward : ToIpc.convertOrdered reverse returned.mixed bytes
      (field descriptor.integer) (field descriptor.binary) = .ok output)
    (carrier : output.len ≤ returned.inputBytes) :
    MixedIpc.read returned output = .ok ⟨descriptor, batches⟩ :=
  Proofs.Formats.Parquet.MixedV1Writer.FromIpc.RoundTrip.read_of_indexed
    opened count indexed footer schema backward carrier

/-- Both native conversions retain the exact descriptor and every batch through EOS.
The original descriptor also fixes the actual Parquet leaf and chunk vectors.
Use the same footer parser policy for writing and reopening, and the same group
limits for certification and reopening. The reverse file-row cap and returned
IPC carrier cap are independent. -/
theorem read_roundTripOrdered {source returned : MixedIpc.Limits} {sink : MixedV1Writer.Multi.Limits}
    {reverse : File.Limits} {input output : KBytes} {parquet : MixedV1Writer.Multi.Encoded}
    {observed : MixedIpc.Prepared}
    (original : MixedIpc.read source input = .ok observed)
    (forward : convertOrdered source sink input = .ok parquet)
    (groupLimits : reverse.group = sink.writer.readback)
    (footerLimits : reverse.group.snapshot.footer = sink.writer.footer)
    (backward : ToIpc.convertOrdered reverse returned.mixed parquet.bytes
      (field observed.descriptor.integer) (field observed.descriptor.binary) = .ok output)
    (carrier : output.len ≤ returned.inputBytes) :
    MixedIpc.read returned output = .ok observed ∧
      ∃ parsed : Footer.Metadata,
        Footer.readFooter sink.writer.footer parquet.bytes = .ok (parquet.footer, parsed) ∧
        parsed.schema = FlatInt32Writer.Compact.schemaRoot 2 ::
          (physicalOrder observed.descriptor).columns
            (MixedV1Writer.columnIndex (field observed.descriptor.integer) ⟨0, 0⟩).schema
            (MixedV1Writer.byteSchema (MixedV1Writer.columnIndex (field observed.descriptor.binary) ⟨0, 0⟩)) ∧
        parsed.rowGroups.map Footer.RowGroup.columns =
          parquet.groups.map (fun pages => (physicalOrder observed.descriptor).columns
            (pages.index.ints.metadata pages.index.rows)
            (MixedV1Writer.byteChunk pages.index.octets pages.index.rows)) :=
  Proofs.Formats.Parquet.MixedV1Writer.FromIpc.RoundTrip.read_roundTripOrdered
    original forward groupLimits footerLimits backward carrier

/-- Schema-only IPC returns the same descriptor with zero batches through EOS.
The native Parquet carrier has its exact zero-group footer immediately after PAR1.
The reverse conversion uses the declared group and footer policies and the
returned bytes must fit the separate IPC carrier cap. -/
theorem read_roundTripSchemaOnly {source returned : MixedIpc.Limits} {sink : MixedV1Writer.Multi.Limits}
    {reverse : File.Limits} {input output : KBytes} {parquet : MixedV1Writer.Multi.Encoded}
    {descriptor : MixedIpc.Descriptor}
    (original : MixedIpc.read source input = .ok ⟨descriptor, []⟩)
    (forward : SchemaOnly.convert source sink input = .ok parquet)
    (groupLimits : reverse.group = sink.writer.readback)
    (footerLimits : reverse.group.snapshot.footer = sink.writer.footer)
    (backward : ToIpc.convertOrdered reverse returned.mixed parquet.bytes
      (field descriptor.integer) (field descriptor.binary) = .ok output)
    (carrier : output.len ≤ returned.inputBytes) :
    MixedIpc.read returned output = .ok ⟨descriptor, []⟩ ∧ parquet.footer.start = 4 ∧
    Footer.readFooter sink.writer.footer parquet.bytes = .ok (parquet.footer, SchemaOnly.metadata descriptor) :=
  Proofs.Formats.Parquet.MixedV1Writer.FromIpc.RoundTrip.read_roundTripSchemaOnly
    original forward groupLimits footerLimits backward carrier

end Silmaril.Formats.Parquet.MixedV1Writer.FromIpc.RoundTrip
