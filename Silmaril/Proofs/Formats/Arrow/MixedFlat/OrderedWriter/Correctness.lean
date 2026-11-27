module

public import Silmaril.Formats.Arrow.MixedFlat.OrderedWriter.Defs
import Batteries.Data.List.Lemmas
import Silmaril.Formats.Arrow.BinaryView.Column.Writer.Thms
import Silmaril.Formats.Arrow.MixedFlat.Stream.Thms
import Silmaril.Formats.Arrow.MixedFlat.Thms
import Silmaril.Formats.Arrow.Writer.Thms

public section

namespace Silmaril.Proofs.Formats.Arrow.MixedFlat.OrderedWriter

open Silmaril.Formats Silmaril.Formats.Arrow Silmaril.Formats.Arrow.MixedFlat
open Silmaril.Formats.Arrow.MixedFlat.OrderedWriter

private theorem view_wf {limits : BinaryView.Column.Limits} {nullable : Bool}
    {view : BinaryView.Column.Writer.Emitted}
    (fits : BinaryView.Column.BuffersFit limits view.node nullable view.buffers) :
    ∀ part ∈ MixedFlat.Writer.viewParts view.buffers, part.wf = true := by
  have valid := fits.2.2.2.1
  intro part member
  simp only [MixedFlat.Writer.viewParts, List.mem_cons] at member
  rcases member with rfl | rfl | member
  · exact valid.1
  · exact valid.2.1
  · obtain ⟨index, bound, eq⟩ := List.getElem_of_mem member
    rw [← eq]
    simpa using (Array.all_eq_true.mp valid.2.2) index (by simpa using bound)

theorem compile_plain_utf8 {limits : MixedFlat.Limits} {rows position : Nat} {name : String}
    {nullable : Bool} {values : List (Option String)} {physical : PhysicalColumn}
    (written : (OrderedWriter.Column.utf8 name nullable values).compile limits rows position = .ok physical) :
    let native := Arrow.Writer.ColumnValues.utf8 values
    values.length = rows ∧ (nullable = false → ¬values.any Option.isNone = true) ∧
      native.OffsetFits ∧ Arrow.Writer.utf8ByteCount values ≤ limits.observation.ipc.bodyBytes ∧
      physical = ⟨⟨native.length, native.nullCount⟩, none, native.emit⟩ := by
  by_cases rowsExact : values.length = rows
  · by_cases requiredNull : (!nullable && values.any Option.isNone) = true
    · simp [OrderedWriter.Column.compile, OrderedWriter.Column.length, rowsExact, requiredNull, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at written
    · by_cases offsets : Arrow.Writer.utf8ByteCount values ≥ 2^31
      · simp [OrderedWriter.Column.compile, OrderedWriter.Column.length, rowsExact, requiredNull, offsets, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at written
      · by_cases bytes : Arrow.Writer.utf8ByteCount values > limits.observation.ipc.bodyBytes
        · simp [OrderedWriter.Column.compile, OrderedWriter.Column.length, rowsExact, requiredNull, offsets, bytes, Functor.map, Except.map, throw, throwThe, MonadExceptOf.throw] at written
        · have exactParts := written.symm
          simp [OrderedWriter.Column.compile, OrderedWriter.Column.length, rowsExact, requiredNull, offsets, bytes, Pure.pure, Except.pure] at exactParts
          refine ⟨rowsExact, ?_, Nat.lt_of_not_ge offsets, Nat.le_of_not_gt bytes, exactParts⟩
          intro required
          simpa only [required, Bool.not_false, Bool.true_and] using requiredNull
  · simp [OrderedWriter.Column.compile, OrderedWriter.Column.length, rowsExact, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at written

private theorem column_wf {limits : MixedFlat.Limits} {rows position : Nat}
    {column : OrderedWriter.Column} {physical : PhysicalColumn}
    (written : column.compile limits rows position = .ok physical) :
    ∀ part ∈ physical.parts, part.wf = true := by
  by_cases same : column.length = rows
  · cases column with
    | int32 name nullable values =>
      simp only [OrderedWriter.Column.compile, same, ne_eq, not_true_eq_false, ↓reduceIte,
        Bind.bind, Except.bind] at written
      split at written
      · contradiction
      · cases written
        intro part member
        simp only [Arrow.Writer.ColumnValues.emit, Arrow.Writer.ColumnValues.encode, Arrow.Writer.bufferParts,
          List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> exact Arrow.Writer.emitWords_wf _ _
    | binary name nullable values =>
      cases view : BinaryView.Column.Writer.emitBinary limits.view nullable values with
      | error cause =>
        simp [OrderedWriter.Column.compile, same, view, Except.mapError, Bind.bind, Except.bind] at written
      | ok actual =>
        simp [OrderedWriter.Column.compile, same, view, Except.mapError, Bind.bind, Except.bind,
          Pure.pure, Except.pure] at written
        subst physical
        exact view_wf (BinaryView.Column.Writer.emitBinary_layout view).fits
    | utf8 name nullable values =>
      obtain ⟨_, _, _, _, rfl⟩ := compile_plain_utf8 written
      intro part member
      simp only [Arrow.Writer.ColumnValues.emit, Arrow.Writer.ColumnValues.encode, Arrow.Writer.bufferParts,
        List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> exact Arrow.Writer.emitWords_wf _ _
    | utf8View name nullable values =>
      cases view : BinaryView.Column.Writer.emitUtf8 limits.view nullable values with
      | error cause =>
        simp [OrderedWriter.Column.compile, same, view, Except.mapError, Bind.bind, Except.bind] at written
      | ok actual =>
        simp [OrderedWriter.Column.compile, same, view, Except.mapError, Bind.bind, Except.bind,
          Pure.pure, Except.pure] at written
        subst physical
        exact view_wf (BinaryView.Column.Writer.emitUtf8_layout view).fits
  · simp [OrderedWriter.Column.compile, same, Bind.bind, Except.bind, throw] at written

theorem compile_binary_wire {limits : MixedFlat.Limits} {rows position : Nat} {name : String}
    {nullable : Bool} {values : List (Option KBytes)} {physical : PhysicalColumn}
    (written : (OrderedWriter.Column.binary name nullable values).compile limits rows position = .ok physical) :
    ∃ view, BinaryView.Column.Writer.emitBinary limits.view nullable values = .ok view ∧
      physical = ⟨view.node, some view.buffers.payload.data.size, MixedFlat.Writer.viewParts view.buffers⟩ ∧
      ∃ decoded, BinaryView.Column.readBinary limits.view view.node nullable view.buffers = .ok decoded ∧
        decoded.map (Option.map KBytes.toList) = values.map (Option.map KBytes.toList) := by
  by_cases same : values.length = rows
  · cases view : BinaryView.Column.Writer.emitBinary limits.view nullable values with
    | error cause =>
      simp [OrderedWriter.Column.compile, OrderedWriter.Column.length, same, view,
        Except.mapError, Bind.bind, Except.bind] at written
    | ok actual =>
      simp [OrderedWriter.Column.compile, OrderedWriter.Column.length, same, view,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure] at written
      exact ⟨actual, rfl, written.symm, BinaryView.Column.Writer.emitBinary_roundtrip view⟩
  · simp [OrderedWriter.Column.compile, OrderedWriter.Column.length, same, Bind.bind, Except.bind, throw] at written

theorem compile_utf8_wire {limits : MixedFlat.Limits} {rows position : Nat} {name : String}
    {nullable : Bool} {values : List (Option String)} {physical : PhysicalColumn}
    (written : (OrderedWriter.Column.utf8View name nullable values).compile limits rows position = .ok physical) :
    ∃ view, BinaryView.Column.Writer.emitUtf8 limits.view nullable values = .ok view ∧
      physical = ⟨view.node, some view.buffers.payload.data.size, MixedFlat.Writer.viewParts view.buffers⟩ ∧
      BinaryView.Column.readUtf8 limits.view view.node nullable view.buffers = .ok values := by
  by_cases same : values.length = rows
  · cases view : BinaryView.Column.Writer.emitUtf8 limits.view nullable values with
    | error cause =>
      simp [OrderedWriter.Column.compile, OrderedWriter.Column.length, same, view,
        Except.mapError, Bind.bind, Except.bind] at written
    | ok actual =>
      simp [OrderedWriter.Column.compile, OrderedWriter.Column.length, same, view,
        Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure] at written
      exact ⟨actual, rfl, written.symm, BinaryView.Column.Writer.emitUtf8_roundtrip view⟩
  · simp [OrderedWriter.Column.compile, OrderedWriter.Column.length, same, Bind.bind, Except.bind, throw] at written

private theorem compiled_wf {limits : MixedFlat.Limits} {rows : Nat}
    {inputs : List (OrderedWriter.Column × Nat)} {outputs : List PhysicalColumn}
    (compiled : List.Forall₂ (fun input physical =>
      input.1.compile limits rows input.2 = .ok physical) inputs outputs) :
    ∀ part ∈ outputs.flatMap PhysicalColumn.parts, part.wf = true := by
  induction compiled with
  | nil => simp
  | cons head _ tail =>
    intro part member
    simp only [List.flatMap_cons, List.mem_append] at member
    exact member.elim (column_wf head part) (tail part)

theorem record_wire {limits : MixedFlat.Limits} {input : BatchInput} (record : Record limits input) :
    record.output.metadata.batch.rowCount = input.rowCount ∧
    record.plan.assignment.groups.map Group.field = input.fields ∧
    record.plan.assignment.groups.filterMap Group.count = record.columns.filterMap PhysicalColumn.count ∧
    bindings record.plan record.columns ∧
    Arrow.Writer.PackedWire record.output.body.toList 0 (record.columns.flatMap PhysicalColumn.parts)
      record.output.metadata.batch.buffers := by
  refine ⟨?_, record.plan.assignment.fieldsExact, ?_, record.assigned, ?_⟩
  · simp [record.packed, pack]
  · rw [record.plan.assignment.countsExact, record.packed]
    rfl
  · have wf := compiled_wf (List.mapM_eq_ok_iff_forall₂.mp record.compiled)
    rw [record.packed]
    exact Arrow.Writer.packBuffers_exact _ wf

theorem emit_readback {limits : MixedFlat.Limits} {fields : List MixedFlat.Field}
    {batches : List BatchInput} {shape : List MixedFlat.Field → Bool} {wire : KBytes}
    (written : emit limits fields batches shape = .ok wire) :
    ∃ decoded, Stream.read limits wire = .ok decoded ∧ decoded.fields = fields ∧
      decoded.batches.map StreamWriter.observeBatch = batches.map BatchInput.observe ∧
      wire.wf = true ∧ ∃ start,
        Stream.readSchemaFrame limits.observation.ipc wire = .ok (decoded.fields, start) ∧
        Stream.BatchesWire limits wire decoded.fields limits.observation.ipc.batches 0 start decoded.batches := by
  unfold emit at written
  cases serialized : serialize limits fields batches shape with
  | error => simp [serialized, Bind.bind, Except.bind] at written
  | ok bytes =>
    cases read : Stream.read limits bytes with
    | error => simp [serialized, read, Except.mapError, Bind.bind, Except.bind] at written
    | ok decoded =>
      simp only [serialized, read, Except.mapError, Bind.bind, Except.bind, Pure.pure, Except.pure] at written
      split at written
      · next agrees =>
        cases written
        exact ⟨decoded, read, agrees.1, agrees.2, (Stream.read_iff limits _ decoded).mp read⟩
      · contradiction

end Silmaril.Proofs.Formats.Arrow.MixedFlat.OrderedWriter
