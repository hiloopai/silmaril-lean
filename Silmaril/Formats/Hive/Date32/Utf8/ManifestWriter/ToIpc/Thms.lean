module

public import Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter.ToIpc.Defs
import Silmaril.Proofs.Formats.Hive.Date32.Utf8.ManifestWriter.ToIpc

public section

namespace Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter.ToIpc

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Int32ByteArrayGroup.File (Kind Value)
open Arrow.BinaryView

theorem projection_kind (layout : Schema) :
    (projection layout).schema.kind (0 : Fin 1) = (layout.byteName, Kind.byteArray .optional) := rfl

/-- Every retained group supplies a batch with the original row count. -/
theorem groups_rowCounts (layout : Schema) (trace : Trace layout) :
    (groups layout trace).map List.length = trace.batches.map (·.rowCount) :=
  Proofs.Formats.Hive.Date32.Utf8.ManifestWriter.ToIpc.groups_rowCounts layout trace

/-- Typed admission and non-EOS source outcomes precede any sink error. -/
theorem convert_outcome (layout : Schema) (options : PartitionPath.Options) (limits : Limits)
    (ipc : Arrow.Limits) (view : Column.Limits) (keep : Scan.Predicate layout.keys.schema.toScan Value)
    (files : List File) :
    convert layout options limits ipc view keep files =
      match readSelected layout options limits (projection layout) keep files with
      | .error cause => .error (.admission cause)
      | .ok trace =>
        match trace.termination with
        | .eos =>
          let source := binarySource layout trace
          (StreamWriter.emit ipc view source.ipcField source.batches).mapError .writer
        | outcome => .error (.source outcome) :=
  Proofs.Formats.Hive.Date32.Utf8.ManifestWriter.ToIpc.convert_outcome layout options limits ipc view keep files

/-- Exact-EOS readback preserves the nullable field and ordered octet slots
of every selected batch, including batches with no rows. -/
theorem convert_readback {layout : Schema} {options : PartitionPath.Options} {limits : Limits}
    {ipc : Arrow.Limits} {view : Column.Limits} {keep : Scan.Predicate layout.keys.schema.toScan Value}
    {files : List File} {wire : KBytes} (written : convert layout options limits ipc view keep files = .ok wire) :
    ∃ (trace : Trace layout) (batches : List (List (Option KBytes))),
      readSelected layout options limits (projection layout) keep files = .ok trace ∧
      trace.termination = .eos ∧
      Stream.read ipc view wire = .ok ⟨⟨layout.byteName, true, .binary⟩, batches⟩ ∧
      batches.map (List.map (Option.map KBytes.toList)) =
        (groups layout trace).map (List.map (Option.map Bytes.toList)) :=
  Proofs.Formats.Hive.Date32.Utf8.ManifestWriter.ToIpc.convert_readback written

end Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter.ToIpc
