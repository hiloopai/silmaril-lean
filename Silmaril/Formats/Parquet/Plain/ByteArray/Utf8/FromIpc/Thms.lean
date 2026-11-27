module

public import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.FromIpc.Defs
import Silmaril.Proofs.Formats.Parquet.Plain.ByteArray.Utf8.FromIpc.Correctness

public section

namespace Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.FromIpc

open Arrow.BinaryView

/-- The complete native reader determines the declared field and all ordered slots. -/
theorem readSource_exact {ipc : Arrow.Limits} {view : Column.Limits} {input : KBytes} {source : Source}
    (accepted : readSource ipc view input = .ok source) :
    Stream.read ipc view input = .ok source.observed :=
  Proofs.Formats.Parquet.Plain.ByteArray.Utf8.FromIpc.readSource_exact accepted

/-- The native writer returns a bounded annotated file with one exact group per input batch. -/
theorem emit_readback {limits : Limits} {source : Source} {wire : Bytes}
    (emitted : emit limits source = .ok wire) : SinkWire limits source wire :=
  Proofs.Formats.Parquet.Plain.ByteArray.Utf8.FromIpc.emit_readback emitted

/-- The checked original IPC stream through EOS determines every exact Parquet group and slot. -/
theorem convert_readback {ipc : Arrow.Limits} {view : Column.Limits} {limits : Limits}
    {input : KBytes} {wire : Bytes} (written : convert ipc view limits input = .ok wire) :
    ∃ source, Stream.read ipc view input = .ok source.observed ∧
      SinkWire limits source wire ∧ input.wf = true ∧ ∃ start,
        Stream.readSchema ipc input = .ok (source.observed.field, start) ∧
        Stream.BatchesWire ipc view input source.observed.field ipc.batches start source.observed.batches :=
  Proofs.Formats.Parquet.Plain.ByteArray.Utf8.FromIpc.convert_readback written

/-- Malformed IPC retains its original error before admitting any output. -/
theorem convert_source_error {ipc : Arrow.Limits} {view : Column.Limits} {limits : Limits}
    {input : KBytes} {cause : Stream.Error} (failed : Stream.read ipc view input = .error cause) :
    convert ipc view limits input = .error (.source cause) := by
  simp [convert, readSource, failed, Except.mapError, Bind.bind, Except.bind]

end Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.FromIpc
