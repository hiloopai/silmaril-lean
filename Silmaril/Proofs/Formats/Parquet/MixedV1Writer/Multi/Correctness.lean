module

public import Silmaril.Formats.Parquet.MixedV1Writer.Multi.Defs
import Silmaril.Formats.Parquet.MixedV1Writer.Thms
import Silmaril.Formats.Parquet.Int32ByteArrayGroup.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.MixedV1Writer.Multi

open Silmaril.Formats.Parquet Silmaril.Formats.Parquet.MixedV1Writer.Multi
open Silmaril.Formats.Parquet.MixedV1Writer (Order byteSchema byteChunk)

theorem emitOrdered_checked {order : Order} {limits : Limits} {input : Input} {output : Encoded}
    (written : emitOrdered order limits input = .ok output) :
    input.groups ≠ [] ∧ input.groups.length ≤ limits.maxGroups ∧
    input.totalRows ≤ limits.maxTotalRows ∧ input.Matches limits ∧ output.CheckedOrdered order limits input ∧
    certify limits input output = .ok () := by
  by_cases groups : input.groups = [] ∨ input.groups.length > limits.maxGroups ∨
      input.groups.length > limits.writer.footer.compact.maxCollectionSize
  · simp [emitOrdered, groups] at written
  by_cases rows : input.totalRows > limits.maxTotalRows ∨ input.totalRows ≥ 2 ^ 63
  · simp [emitOrdered, groups, rows] at written
  by_cases schema : input.Matches limits
  · cases assembled : assembleOrdered order limits input with
    | error cause => simp [emitOrdered, groups, rows, schema, assembled, Bind.bind, Except.bind] at written
    | ok candidate =>
      by_cases checked : candidate.CheckedOrdered order limits input
      · cases certified : certify limits input candidate with
        | error cause => simp [emitOrdered, groups, rows, schema, assembled, checked, certified,
            Bind.bind, Except.bind, Except.map] at written
        | ok value =>
          simp [emitOrdered, groups, rows, schema, assembled, checked, certified,
            Bind.bind, Except.bind, Except.map] at written
          subst output
          have nonempty : input.groups ≠ [] := by
            intro empty
            exact groups (.inl empty)
          have groupCap := Nat.le_of_not_gt (fun tooMany => groups (.inr (.inl tooMany)))
          have rowCap := Nat.le_of_not_gt (fun tooMany => rows (.inl tooMany))
          exact ⟨nonempty, groupCap, rowCap, schema, checked, by simpa using certified⟩
      · simp [emitOrdered, groups, rows, schema, assembled, checked, Bind.bind, Except.bind] at written
  · simp [emitOrdered, groups, rows, schema] at written

theorem checkGroups_indexed {intField byteField : Int32ByteArrayGroup.Field}
    (limits : Int32ByteArrayGroup.Limits) (opened : Int32ByteArrayGroup.Checked intField byteField)
    (groups : List Group) (offset : Nat) (checked : checkGroups limits opened offset groups = .ok ()) :
    ∀ i : Fin groups.length, opened.readGroup limits (offset + i.val) = .ok (groups.get i).rows := by
  induction groups generalizing offset with
  | nil => exact fun i => Fin.elim0 i
  | cons group rest ih =>
    cases read : opened.readGroup limits offset with
    | error cause => simp [checkGroups, read] at checked
    | ok rows =>
      by_cases same : rows = group.rows
      · have tail : checkGroups limits opened (offset + 1) rest = .ok () := by
          simpa [checkGroups, read, same] using checked
        intro i
        refine Fin.cases ?_ (fun index => ?_) i
        · simpa using read.trans (congrArg Except.ok same)
        · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (offset + 1) tail index
      · simp [checkGroups, read, same] at checked

theorem emitOrdered_indexed {order : Order} {limits : Limits} {input : Input} {output : Encoded}
    (written : emitOrdered order limits input = .ok output) :
    ∃ opened : Int32ByteArrayGroup.Checked input.intField input.byteField,
      Int32ByteArrayGroup.openFile limits.writer.readback output.bytes input.intField input.byteField = .ok opened ∧
      opened.snapshot.groupCount = input.groups.length ∧
      ∀ i : Fin input.groups.length,
        opened.readGroup limits.writer.readback i.val = .ok (input.groups.get i).rows ∧
        Int32ByteArrayGroup.GroupWire opened limits.writer.readback i.val (input.groups.get i).rows := by
  have checked := (emitOrdered_checked written).2.2.2.2.2
  unfold certify at checked
  cases opened : Int32ByteArrayGroup.openFile limits.writer.readback output.bytes input.intField input.byteField with
  | error cause => simp [opened, Except.mapError, Bind.bind, Except.bind] at checked
  | ok source =>
    by_cases count : source.snapshot.groupCount = input.groups.length
    · have all : checkGroups limits.writer.readback source 0 input.groups = .ok () := by
        simpa [opened, Except.mapError, Bind.bind, Except.bind, count] using checked
      refine ⟨source, rfl, count, fun i => ?_⟩
      have read := checkGroups_indexed limits.writer.readback source input.groups 0 all i
      exact ⟨by simpa using read, Int32ByteArrayGroup.readGroup_wire (by simpa using read)⟩
    · simp [opened, Except.mapError, Bind.bind, Except.bind, count] at checked

theorem emitOrdered_empty {order : Order} {limits : Limits} {input : Input} {output : Encoded}
    (written : emitOrdered order limits input = .ok output) (i : Fin input.groups.length)
    (empty : (input.groups.get i).rowCount = 0) :
    ∃ opened : Int32ByteArrayGroup.Checked input.intField input.byteField,
      Int32ByteArrayGroup.openFile limits.writer.readback output.bytes input.intField input.byteField = .ok opened ∧
      opened.readGroup limits.writer.readback i.val = .ok [] := by
  obtain ⟨opened, source, _, all⟩ := emitOrdered_indexed written
  have matched := (emitOrdered_checked written).2.2.2.1
  have aligned := MixedV1Writer.rows_exact (matched (input.groups.get i) (List.get_mem input.groups i)).1
  have noRows : (input.groups.get i).rows = [] :=
    List.length_eq_zero_iff.mp (aligned.1.trans empty)
  exact ⟨opened, source, noRows ▸ (all i).1⟩

theorem emit_byteFirst_footer {limits : Limits} {input : Input} {output : Encoded}
    (written : emitOrdered .byteFirst limits input = .ok output) :
    ∃ parsed : Footer.Metadata,
      Footer.readFooter limits.writer.footer output.bytes = .ok (output.footer, parsed) ∧
      parsed.schema = [FlatInt32Writer.Compact.schemaRoot 2, byteSchema input.byteIndex, input.intIndex.schema] ∧
      parsed.rowGroups.map Footer.RowGroup.columns =
        output.groups.map (fun pages => [byteChunk pages.index.octets pages.index.rows,
          pages.index.ints.metadata pages.index.rows]) := by
  have checked := (emitOrdered_checked written).2.2.2.2.1
  refine ⟨metadataOrdered .byteFirst input output.groups, checked.2.2.2.2.1, rfl, ?_⟩
  simp only [metadataOrdered, List.map_map]
  rfl

end Silmaril.Proofs.Formats.Parquet.MixedV1Writer.Multi
