module

public import Silmaril.Formats.Arrow.MixedFlat.OrderedWriter.Defs
public import Silmaril.Formats.Arrow.MixedFlat.Stream.Events.Defs
public import Mathlib.Data.List.Forall2
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

/-- Plain Utf8 has bounded signed offsets and exactly its primitive buffer
parts, with no variadic count. -/
theorem compile_plain_utf8 {limits : MixedFlat.Limits} {rows position : Nat} {name : String}
    {nullable : Bool} {values : List (Option String)} {physical : PhysicalColumn}
    (written : (OrderedWriter.Column.utf8 name nullable values).compile limits rows position = .ok physical) :
    let native := Arrow.Writer.ColumnValues.utf8 values
    values.length = rows ∧ (nullable = false → ¬values.any Option.isNone = true) ∧
      native.OffsetFits ∧ Arrow.Writer.utf8ByteCount values ≤ limits.observation.ipc.bodyBytes ∧
      physical = ⟨⟨native.length, native.nullCount⟩, none, native.emit⟩ :=
  Proofs.Formats.Arrow.MixedFlat.OrderedWriter.compile_plain_utf8 written

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

/-- An explicitly admitted stream recovers its ordered fields and exact nullable slots. -/
theorem emitWith_readback {limits : MixedFlat.Limits} {fields : List MixedFlat.Field}
    {batches : List BatchInput} {admit : List MixedFlat.Field → Bool} {wire : KBytes}
    (written : emitWith limits fields batches admit = .ok wire) :
    ∃ decoded, Stream.read limits wire = .ok decoded ∧ decoded.fields = fields ∧
      decoded.batches.map StreamWriter.observeBatch = batches.map BatchInput.observe ∧
      wire.wf = true ∧ ∃ start,
        Stream.readSchemaFrame limits.observation.ipc wire = .ok (decoded.fields, start) ∧
        Stream.BatchesWire limits wire decoded.fields limits.observation.ipc.batches 0 start decoded.batches :=
  Proofs.Formats.Arrow.MixedFlat.OrderedWriter.emitWith_readback written

/-- Decode the original Schema fields and locate EOS at the exact end of the emitted stream. -/
theorem emitWith_schema_eos {limits : MixedFlat.Limits} {fields : List Field}
    {batches : List BatchInput} {admit : List Field → Bool} {wire : KBytes}
    (written : emitWith limits fields batches admit = .ok wire) :
    ∃ (decoded : Stream.Observed) (size : Nat),
      Stream.read limits wire = .ok decoded ∧
      readEnvelope limits.observation.ipc wire 0 = .ok (.metadata size) ∧
      MixedFlat.readSchema limits.observation.ipc (wire.slice 8 size) = .ok fields ∧
      let eos := decoded.batches.foldl (fun _ batch => batch.range.next) (8 + size)
      readEnvelope limits.observation.ipc wire eos = .ok .eos ∧ eos + 8 = wire.len :=
  Proofs.Formats.Arrow.MixedFlat.OrderedWriter.emitWith_schema_eos written

/-- The native pull reader returns aligned events in emitted batch order and reaches EOS. -/
theorem emitWith_pull_exact {limits : MixedFlat.Limits} {fields : List Field}
    {batches : List BatchInput} {admit : List Field → Bool} {wire : KBytes}
    (written : emitWith limits fields batches admit = .ok wire) :
    ∃ (decoded : Stream.Observed) (trace : Stream.Events.Trace (MixedFlat.Events.schema fields)),
      Stream.read limits wire = .ok decoded ∧ decoded.fields = fields ∧
      decoded.batches.map StreamWriter.observeBatch = batches.map BatchInput.observe ∧
      Stream.Events.readAll limits wire = .ok ⟨MixedFlat.Events.schema fields, trace⟩ ∧
      trace.termination = .eos ∧
      List.Forall₂ (fun record => MixedFlat.Events.Agrees (MixedFlat.Events.schema fields) record.observed)
        decoded.batches trace.batches :=
  Proofs.Formats.Arrow.MixedFlat.OrderedWriter.emitWith_pull_exact written

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
