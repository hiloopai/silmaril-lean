module

public import Silmaril.Formats.Parquet.MixedV1Writer.Multi.Defs
import Silmaril.Proofs.Formats.Parquet.MixedV1Writer.Multi.Correctness

public section

namespace Silmaril.Formats.Parquet.MixedV1Writer.Multi

/-- Successful emission checks the requested physical order, contiguous windows and exact footer. -/
theorem emitOrdered_checked {order : Order} {limits : Limits} {input : Input} {output : Encoded}
    (written : emitOrdered order limits input = .ok output) :
    input.groups ≠ [] ∧ input.groups.length ≤ limits.maxGroups ∧
    input.totalRows ≤ limits.maxTotalRows ∧ input.Matches limits ∧ output.CheckedOrdered order limits input ∧
    certify limits input output = .ok () :=
  Proofs.Formats.Parquet.MixedV1Writer.Multi.emitOrdered_checked written

/-- The shared readback checker compares every group at its original ordinal. -/
theorem checkGroups_indexed {intField byteField : Int32ByteArrayGroup.Field}
    (limits : Int32ByteArrayGroup.Limits) (opened : Int32ByteArrayGroup.Checked intField byteField)
    (groups : List Group) (offset : Nat) (checked : checkGroups limits opened offset groups = .ok ()) :
    ∀ i : Fin groups.length, opened.readGroup limits (offset + i.val) = .ok (groups.get i).rows :=
  Proofs.Formats.Parquet.MixedV1Writer.Multi.checkGroups_indexed limits opened groups offset checked

/-- The original paired slots survive at every ordinal under either physical leaf order. -/
theorem emitOrdered_indexed {order : Order} {limits : Limits} {input : Input} {output : Encoded}
    (written : emitOrdered order limits input = .ok output) :
    ∃ opened : Int32ByteArrayGroup.Checked input.intField input.byteField,
      Int32ByteArrayGroup.openFile limits.writer.readback output.bytes input.intField input.byteField = .ok opened ∧
      opened.snapshot.groupCount = input.groups.length ∧
      ∀ i : Fin input.groups.length,
        opened.readGroup limits.writer.readback i.val = .ok (input.groups.get i).rows ∧
        Int32ByteArrayGroup.GroupWire opened limits.writer.readback i.val (input.groups.get i).rows :=
  Proofs.Formats.Parquet.MixedV1Writer.Multi.emitOrdered_indexed written

/-- An explicitly empty group occupies its original ordinal under either leaf order. -/
theorem emitOrdered_empty {order : Order} {limits : Limits} {input : Input} {output : Encoded}
    (written : emitOrdered order limits input = .ok output) (i : Fin input.groups.length)
    (empty : (input.groups.get i).rowCount = 0) :
    ∃ opened : Int32ByteArrayGroup.Checked input.intField input.byteField,
      Int32ByteArrayGroup.openFile limits.writer.readback output.bytes input.intField input.byteField = .ok opened ∧
      opened.readGroup limits.writer.readback i.val = .ok [] :=
  Proofs.Formats.Parquet.MixedV1Writer.Multi.emitOrdered_empty written i empty

/-- Read the actual footer with BYTE_ARRAY before INT32, including both ordered chunks of every group. -/
theorem emit_byteFirst_footer {limits : Limits} {input : Input} {output : Encoded}
    (written : emitOrdered .byteFirst limits input = .ok output) :
    ∃ parsed : Footer.Metadata,
      Footer.readFooter limits.writer.footer output.bytes = .ok (output.footer, parsed) ∧
      parsed.schema = [FlatInt32Writer.Compact.schemaRoot 2, byteSchema input.byteIndex, input.intIndex.schema] ∧
      parsed.rowGroups.map Footer.RowGroup.columns =
        output.groups.map (fun pages => [byteChunk pages.index.octets pages.index.rows,
          pages.index.ints.metadata pages.index.rows]) :=
  Proofs.Formats.Parquet.MixedV1Writer.Multi.emit_byteFirst_footer written

/-- Successful emission checks aggregate limits, layout, the full footer and every actual page window. -/
theorem emit_checked {limits : Limits} {input : Input} {output : Encoded}
    (written : emit limits input = .ok output) :
    input.groups ≠ [] ∧ input.groups.length ≤ limits.maxGroups ∧
    input.totalRows ≤ limits.maxTotalRows ∧ input.Matches limits ∧ output.Checked limits input ∧
    certify limits input output = .ok () :=
  emitOrdered_checked (order := .intFirst) written

/-- Every input group is recovered at its original footer ordinal, with the exact paired slots
and the corresponding checked wire chunks. -/
theorem emit_indexed {limits : Limits} {input : Input} {output : Encoded}
    (written : emit limits input = .ok output) :
    ∃ opened : Int32ByteArrayGroup.Checked input.intField input.byteField,
      Int32ByteArrayGroup.openFile limits.writer.readback output.bytes input.intField input.byteField = .ok opened ∧
      opened.snapshot.groupCount = input.groups.length ∧
      ∀ i : Fin input.groups.length,
        opened.readGroup limits.writer.readback i.val = .ok (input.groups.get i).rows ∧
        Int32ByteArrayGroup.GroupWire opened limits.writer.readback i.val (input.groups.get i).rows :=
  emitOrdered_indexed (order := .intFirst) written

/-- A zero-row input group is present and reads as an empty list at its original ordinal. -/
theorem emit_empty {limits : Limits} {input : Input} {output : Encoded}
    (written : emit limits input = .ok output) (i : Fin input.groups.length)
    (empty : (input.groups.get i).rowCount = 0) :
    ∃ opened : Int32ByteArrayGroup.Checked input.intField input.byteField,
      Int32ByteArrayGroup.openFile limits.writer.readback output.bytes input.intField input.byteField = .ok opened ∧
      opened.readGroup limits.writer.readback i.val = .ok [] :=
  emitOrdered_empty (order := .intFirst) written i empty

end Silmaril.Formats.Parquet.MixedV1Writer.Multi
