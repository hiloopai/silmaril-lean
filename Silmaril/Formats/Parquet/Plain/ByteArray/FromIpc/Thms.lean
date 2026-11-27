module

public import Silmaril.Formats.Parquet.Plain.ByteArray.FromIpc.Defs
import Silmaril.Proofs.Formats.Parquet.Plain.ByteArray.FromIpc.Correctness

public section

namespace Silmaril.Formats.Parquet.Plain.ByteArray.FromIpc

open Arrow.BinaryView

variable {ipc : Arrow.Limits} {view : Column.Limits} {limits : PlainByteArrayV1Writer.File.Limits}
variable {input : KBytes} {output : PlainByteArrayV1Writer.File.Encoded}

/-- Preparation retains the exact declared field and every native batch
from a successful read through explicit EOS and the exact carrier extent. -/
theorem readSource_exact {source : Source} (read : readSource ipc view input = .ok source) :
    Stream.read ipc view input = .ok source.observed :=
  Proofs.Formats.Parquet.Plain.ByteArray.FromIpc.readSource_exact read

theorem Source.slots_octets (source : Source) :
    source.slots.map (Option.map Bytes.toList) =
      source.batches.flatten.map (Option.map KBytes.toList) := by
  simp [Source.slots, List.map_map, Option.map_map, Function.comp_def]

/-- The exact singleton footer and indexed group read recover the source
name, layout and all nullable octets in flattened native batch order. -/
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
        checked.readGroup limits 0 = .ok source.slots :=
  Proofs.Formats.Parquet.Plain.ByteArray.FromIpc.convert_readback converted

/-- A native source error wins before any writer check, retaining its index
and original cause. -/
theorem convert_source_error {cause : Stream.Error} (failed : Stream.read ipc view input = .error cause) :
    convert ipc view limits input = .error (.source cause) := by
  simp [convert, readSource, failed, Except.mapError, Bind.bind, Except.bind]

theorem convert_wrong_kind {name : String} {nullable : Bool} {batches : List (List (Option String))}
    (read : Stream.read ipc view input = .ok ⟨⟨name, nullable, .utf8⟩, batches⟩) :
    convert ipc view limits input = .error .expectedBinaryView := by
  simp [convert, readSource, read, Except.mapError, Bind.bind, Except.bind, throw, throwThe,
    MonadExceptOf.throw]

/-- A writer error retains its stage and original cause after exact native
source exhaustion and successful slot preparation. -/
theorem convert_writer_error {source : Source} {prepared : PlainByteArrayV1Writer.File.Input}
    {cause : PlainByteArrayV1Writer.File.Error}
    (read : readSource ipc view input = .ok source)
    (packed : PlainByteArrayV1Writer.File.Input.ofSlots source.name source.layout source.slots = some prepared)
    (failed : PlainByteArrayV1Writer.File.emit limits prepared = .error cause) :
    convert ipc view limits input = .error (.writer cause) := by
  simp [convert, read, packed, failed, Except.mapError, Bind.bind, Except.bind]

end Silmaril.Formats.Parquet.Plain.ByteArray.FromIpc
