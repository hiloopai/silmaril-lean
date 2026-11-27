module

public import Silmaril.Formats.Parquet.Plain.ByteArray.FromIpc.Defs
import Silmaril.Formats.Parquet.PlainByteArrayV1Writer.File.Thms

public section

namespace Silmaril.Proofs.Formats.Parquet.Plain.ByteArray.FromIpc

open Silmaril.Formats Silmaril.Formats.Parquet
open Silmaril.Formats.Parquet.Plain.ByteArray
open Silmaril.Formats.Parquet.Plain.ByteArray.FromIpc
open Arrow.BinaryView

variable {ipc : Arrow.Limits} {view : Column.Limits} {limits : PlainByteArrayV1Writer.File.Limits}
variable {input : KBytes} {output : PlainByteArrayV1Writer.File.Encoded}

theorem readSource_exact {source : Source}
    (read : readSource ipc view input = .ok source) :
    Stream.read ipc view input = .ok source.observed := by
  cases decoded : Stream.read ipc view input with
  | error cause => simp [readSource, decoded, Except.mapError, Bind.bind, Except.bind] at read
  | ok observed =>
    rcases observed with ⟨⟨name, nullable, kind⟩, batches⟩
    cases kind with
    | binary =>
      have same : (⟨name, nullable, batches⟩ : Source) = source := by
        simpa [readSource, decoded, Except.mapError, Bind.bind, Except.bind, pure, Except.pure] using read
      subst source
      rfl
    | utf8 =>
      simp [readSource, decoded, Except.mapError, Bind.bind, Except.bind, throw, throwThe,
        MonadExceptOf.throw] at read

private theorem convert_steps (converted : convert ipc view limits input = .ok output) :
    ∃ source prepared, readSource ipc view input = .ok source ∧
      PlainByteArrayV1Writer.File.Input.ofSlots source.name source.layout source.slots = some prepared ∧
      PlainByteArrayV1Writer.File.emit limits prepared = .ok output := by
  cases acquired : readSource ipc view input with
  | error cause => simp [convert, acquired, Bind.bind, Except.bind] at converted
  | ok source =>
    cases packed : PlainByteArrayV1Writer.File.Input.ofSlots source.name source.layout source.slots with
    | none =>
      simp [convert, acquired, packed, Bind.bind, Except.bind, throw, throwThe,
        MonadExceptOf.throw] at converted
    | some prepared =>
      refine ⟨source, prepared, rfl, packed, ?_⟩
      cases written : PlainByteArrayV1Writer.File.emit limits prepared <;>
        simp_all [convert, Except.mapError, Bind.bind, Except.bind]

theorem convert_readback (converted : convert ipc view limits input = .ok output) :
    ∃ (source : Source) (prepared : PlainByteArrayV1Writer.File.Input),
      Stream.read ipc view input = .ok source.observed ∧
      prepared.name = source.name ∧ prepared.layout = source.layout ∧ prepared.page.slots = source.slots ∧
      output.bytes.length ≤ limits.maxFileBytes ∧
      Footer.readFooter limits.snapshot.footer output.bytes =
        .ok (output.footer, PlainByteArrayV1Writer.File.metadata prepared output) ∧
      ∃ checked : File.Checked source.name source.layout,
        File.openFile limits output.bytes source.name source.layout = .ok checked ∧
        checked.binding.columnOrdinal = 0 ∧ checked.snapshot.groupCount = 1 ∧
        checked.readGroup limits 0 = .ok source.slots := by
  obtain ⟨source, prepared, acquired, packed, written⟩ := convert_steps converted
  obtain ⟨name, layout, slots⟩ := PlainByteArrayV1Writer.File.Input.ofSlots_exact packed
  have bound := (PlainByteArrayV1Writer.File.emit_readback written).1
  exact ⟨source, prepared, readSource_exact acquired, name, layout, slots, bound,
    PlainByteArrayV1Writer.File.emit_ofSlots_readback packed written⟩

end Silmaril.Proofs.Formats.Parquet.Plain.ByteArray.FromIpc
