module

public import Silmaril.Formats.Parquet.PlainByteArrayV1Writer.File.Defs
import Silmaril.Formats.Parquet.Plain.ByteArray.File.Thms
import Silmaril.Formats.Parquet.Snapshot.Footer.Thms
import Silmaril.Formats.Parquet.Snapshot.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.PlainByteArrayV1Writer.File

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.PlainByteArrayV1Writer.File

variable {limits : Limits} {input : Input} {output : Encoded}

private theorem assemble_wire (assembled : assemble limits input = .ok output) :
    ∃ footer : Bytes, PlainByteArrayV1Writer.emit (pageLimits limits) input.page = .ok output.page ∧
      serializeFooter input limits output.pageSpan = .ok footer ∧
      output.footer = ⟨output.pageSpan.stop, output.pageSpan.stop + footer.length⟩ ∧
      output.bytes = (((Footer.magic.append output.page.wire).append footer).append
        (Bytes.ofList (KBytes.unpack 4 footer.length))).append Footer.magic := by
  simp only [assemble, Bind.bind, Except.bind] at assembled
  split at assembled
  · contradiction
  split at assembled
  · contradiction
  cases measured : MixedV1Writer.measuredBytePage (pageLimits limits) input.page with
  | error cause => simp [measured, Except.mapError] at assembled
  | ok pageSize =>
    simp only [measured, Except.mapError] at assembled
    split at assembled
    · contradiction
    split at assembled
    · contradiction
    cases serialized : serializeFooter input limits ⟨4, 4 + pageSize⟩ with
    | error cause => simp [serialized] at assembled
    | ok footer =>
      simp only [serialized] at assembled
      cases written : PlainByteArrayV1Writer.emit (pageLimits limits) input.page with
      | error cause => simp [written] at assembled
      | ok page =>
        simp only [written] at assembled
        split at assembled
        · rename_i exactSize
          have same : wrap page footer = output := Except.ok.inj assembled
          subst output
          exact ⟨footer, rfl, by simpa only [wrap, Encoded.pageSpan, exactSize] using serialized, rfl, rfl⟩
        · contradiction

private theorem emit_steps (written : emit limits input = .ok output) :
    assemble limits input = .ok output ∧
    ∃ checked : Plain.ByteArray.File.Checked input.name input.layout,
      Plain.ByteArray.File.openFile limits output.bytes input.name input.layout = .ok checked ∧
      checked.snapshot.footer = output.footer ∧ checked.snapshot.metadata = metadata input output ∧
      checked.readGroup limits 0 = .ok input.page.slots := by
  cases assm : assemble limits input with
  | error cause => simp [emit, assm, Bind.bind, Except.bind] at written
  | ok built =>
    cases opened : Plain.ByteArray.File.openFile limits built.bytes input.name input.layout with
    | error cause => simp [emit, assm, opened, Except.mapError, Bind.bind, Except.bind] at written
    | ok checked =>
      by_cases differs : checked.snapshot.footer ≠ built.footer ∨ checked.snapshot.metadata ≠ metadata input built
      · simp [emit, assm, opened, differs, Except.mapError, Bind.bind, Except.bind,
          throw, throwThe, MonadExceptOf.throw] at written
      cases read : checked.readGroup limits 0 with
      | error cause => simp [emit, assm, opened, differs, read, Except.mapError, Bind.bind, Except.bind] at written
      | ok slots =>
        by_cases exactSlots : slots = input.page.slots
        · have exactOutput : built = output := by
            simpa [emit, assm, opened, differs, read, exactSlots, Except.mapError, Bind.bind, Except.bind,
              pure, Except.pure] using written
          subst output
          have ⟨sameFooter, sameMeta⟩ : checked.snapshot.footer = built.footer ∧
              checked.snapshot.metadata = metadata input built := by
            simpa only [not_or, not_not] using differs
          exact ⟨rfl, checked, opened, sameFooter, sameMeta, read.trans (congrArg Except.ok exactSlots)⟩
        · simp [emit, assm, opened, differs, read, exactSlots, Except.mapError, Bind.bind, Except.bind,
            throw, throwThe, MonadExceptOf.throw] at written

theorem emit_wire (written : emit limits input = .ok output) :
    ∃ footer : Bytes, PlainByteArrayV1Writer.emit (pageLimits limits) input.page = .ok output.page ∧
      serializeFooter input limits output.pageSpan = .ok footer ∧
      output.footer = ⟨output.pageSpan.stop, output.pageSpan.stop + footer.length⟩ ∧
      output.bytes = (((Footer.magic.append output.page.wire).append footer).append
        (Bytes.ofList (KBytes.unpack 4 footer.length))).append Footer.magic :=
  assemble_wire (emit_steps written).1

theorem emit_readback (written : emit limits input = .ok output) :
    output.bytes.length ≤ limits.maxFileBytes ∧
    Footer.readFooter limits.snapshot.footer output.bytes = .ok (output.footer, metadata input output) ∧
    ∃ checked : Plain.ByteArray.File.Checked input.name input.layout,
      Plain.ByteArray.File.openFile limits output.bytes input.name input.layout = .ok checked ∧
      checked.binding.columnOrdinal = 0 ∧ checked.snapshot.groupCount = 1 ∧
      checked.readGroup limits 0 = .ok input.page.slots ∧
      Plain.ByteArray.File.GroupWire checked limits 0 (rowGroup input output) input.page.slots := by
  obtain ⟨_, checked, opened, footer, shape, read⟩ := emit_steps written
  obtain ⟨snapshot, fileBound, _, _, _, _, _⟩ := Plain.ByteArray.File.openFile_wire opened
  have readFooter := Snapshot.check_footer snapshot
  rw [footer, shape] at readFooter
  obtain ⟨count, atIndex⟩ := Snapshot.check_groups snapshot
  rw [shape] at count
  have ordinal : checked.binding.columnOrdinal = 0 := by
    have leafAt := checked.binding.leafAt
    rw [shape] at leafAt
    cases atColumn : checked.binding.columnOrdinal with
    | zero => rfl
    | succ index => simp [atColumn, metadata] at leafAt
  obtain ⟨group, groupWire⟩ := Plain.ByteArray.File.readGroup_wire read
  have groupAt : checked.snapshot.groupAt 0 = some group := by
    obtain ⟨_, _, _, _, original, _⟩ := groupWire
    exact original
  rw [atIndex, shape] at groupAt
  have exactGroup : rowGroup input output = group := Option.some.inj groupAt
  subst group
  exact ⟨fileBound, readFooter, checked, opened, ordinal, count, read, groupWire⟩

end Silmaril.Proofs.Formats.Parquet.PlainByteArrayV1Writer.File
