module

public import Silmaril.Formats.Arrow.MixedFlat.OrderedWriter.Defs
import Silmaril.Proofs.Formats.Arrow.MixedFlat.OrderedWriter.Correctness
import Silmaril.Formats.Arrow.BinaryView.Column.Writer.Thms

public section

namespace Silmaril.Formats.Arrow.MixedFlat.OrderedWriter

/-- Each view reads back from its own validity, view and data buffers,
with local buffer indices and the same ordered nullable octets. -/
theorem compile_binary_wire {limits : MixedFlat.Limits} {rows position : Nat} {name : String}
    {nullable : Bool} {values : List (Option KBytes)} {physical : PhysicalColumn}
    (written : (OrderedWriter.Column.binary name nullable values).compile limits rows position = .ok physical) :
    ∃ view, BinaryView.Column.Writer.emitBinary limits.view nullable values = .ok view ∧
      physical = ⟨view.node, some view.buffers.payload.data.size, Writer.viewParts view.buffers⟩ ∧
      ∃ decoded, BinaryView.Column.readBinary limits.view view.node nullable view.buffers = .ok decoded ∧
        decoded.map (Option.map KBytes.toList) = values.map (Option.map KBytes.toList) :=
  Proofs.Formats.Arrow.MixedFlat.OrderedWriter.compile_binary_wire written

/-- Each view contributes one count word. A view with no external payload
contributes an explicit zero independently of the other view fields. -/
theorem compile_binary_count {limits : MixedFlat.Limits} {rows position : Nat} {name : String}
    {nullable : Bool} {values : List (Option KBytes)} {physical : PhysicalColumn}
    (written : (Column.binary name nullable values).compile limits rows position = .ok physical) :
    physical.count = some (BinaryView.Column.Writer.dataCount
      (BinaryView.Column.Writer.longBytes KBytes.len values)) := by
  obtain ⟨view, emitted, rfl, _⟩ := compile_binary_wire written
  exact congrArg some (BinaryView.Column.Writer.emitBinary_layout emitted).variadicCount

/-- Utf8View reads back the original nullable strings from its own buffers. -/
theorem compile_utf8_wire {limits : MixedFlat.Limits} {rows position : Nat} {name : String}
    {nullable : Bool} {values : List (Option String)} {physical : PhysicalColumn}
    (written : (OrderedWriter.Column.utf8View name nullable values).compile limits rows position = .ok physical) :
    ∃ view, BinaryView.Column.Writer.emitUtf8 limits.view nullable values = .ok view ∧
      physical = ⟨view.node, some view.buffers.payload.data.size, Writer.viewParts view.buffers⟩ ∧
      BinaryView.Column.readUtf8 limits.view view.node nullable view.buffers = .ok values :=
  Proofs.Formats.Arrow.MixedFlat.OrderedWriter.compile_utf8_wire written

/-- The text count word uses encoded UTF-8 byte lengths, with an explicit
zero when every present value fits inline. -/
theorem compile_utf8_count {limits : MixedFlat.Limits} {rows position : Nat} {name : String}
    {nullable : Bool} {values : List (Option String)} {physical : PhysicalColumn}
    (written : (Column.utf8View name nullable values).compile limits rows position = .ok physical) :
    physical.count = some (BinaryView.Column.Writer.dataCount
      (BinaryView.Column.Writer.longBytes KBytes.len
        (values.map (Option.map BinaryView.Column.Writer.utf8Bytes)))) := by
  obtain ⟨view, emitted, rfl, _⟩ := compile_utf8_wire written
  exact congrArg some (BinaryView.Column.Writer.emitUtf8_layout emitted).variadicCount

/-- A checked record binds the exact input field order, an independent count
and descriptor slice for each view, and the original packed buffer bytes. -/
theorem record_wire {limits : MixedFlat.Limits} {input : BatchInput} (record : Record limits input) :
    record.output.metadata.batch.rowCount = input.rowCount ∧
    record.plan.assignment.groups.map Group.field = input.fields ∧
    record.plan.assignment.groups.filterMap Group.count = record.columns.filterMap PhysicalColumn.count ∧
    bindings record.plan record.columns ∧
    Arrow.Writer.PackedWire record.output.body.toList 0 (record.columns.flatMap PhysicalColumn.parts)
      record.output.metadata.batch.buffers :=
  Proofs.Formats.Arrow.MixedFlat.OrderedWriter.record_wire record

/-- The existing mixed reader recovers the ordered descriptors, nullable
slots and explicit counts for every record through exact EOS. -/
theorem emit_readback {limits : MixedFlat.Limits} {fields : List Field}
    {batches : List BatchInput} {shape : List MixedFlat.Field → Bool} {wire : KBytes}
    (written : emit limits fields batches shape = .ok wire) :
    ∃ decoded, Stream.read limits wire = .ok decoded ∧ decoded.fields = fields ∧
      decoded.batches.map StreamWriter.observeBatch = batches.map BatchInput.observe ∧
      wire.wf = true ∧ ∃ start,
        Stream.readSchemaFrame limits.observation.ipc wire = .ok (decoded.fields, start) ∧
        Stream.BatchesWire limits wire decoded.fields limits.observation.ipc.batches 0 start decoded.batches :=
  Proofs.Formats.Arrow.MixedFlat.OrderedWriter.emit_readback written

/-- Every input record contributes its explicit row count, even at width zero. -/
theorem emit_batch_rows {limits : MixedFlat.Limits} {fields : List Field}
    {batches : List BatchInput} {shape : List Field → Bool} {wire : KBytes}
    (written : emit limits fields batches shape = .ok wire) :
    ∃ decoded, Stream.read limits wire = .ok decoded ∧
      decoded.batches.map (·.observed.rowCount) = batches.map (·.rowCount) := by
  obtain ⟨decoded, read, _, observed, _⟩ := emit_readback written
  refine ⟨decoded, read, ?_⟩
  simpa only [List.map_map, Function.comp_def, StreamWriter.observeBatch, BatchInput.observe] using
    congrArg (List.map (fun batch : StreamWriter.BatchObservation => batch.1)) observed

end Silmaril.Formats.Arrow.MixedFlat.OrderedWriter
