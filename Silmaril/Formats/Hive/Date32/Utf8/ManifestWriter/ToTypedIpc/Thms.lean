module

public import Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter.ToTypedIpc.Defs
import Silmaril.Proofs.Formats.Hive.Date32.Utf8.ManifestWriter.ToTypedIpc

public section

namespace Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter.ToTypedIpc

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Int32ByteArrayGroup.File (Value)

/-- Checked path admission and a reached non-EOS source outcome take
precedence over conversion of text slots and IPC sink admission. -/
theorem convert_outcome (layout : Schema) (options : PartitionPath.Options) (limits : Limits)
    (ipc : ObservationLimits) (keep : Scan.Predicate layout.keys.schema.toScan Value) (files : List File) :
    convert layout options limits ipc keep files =
      match readSelected layout options limits (projection layout) keep files with
      | .error cause => .error (.admission cause)
      | .ok trace =>
        if trace.termination = .eos then
          (prepare layout trace).bind fun batches => (DateUtf8Stream.emit ipc (schema layout) batches).mapError .writer
        else .error (.source trace.termination) :=
  Proofs.Formats.Hive.Date32.Utf8.ManifestWriter.ToTypedIpc.convert_outcome layout options limits ipc keep files

/-- Exact typed readback through EOS, comparing the original signed days
and UTF-8 bytes in every retained group, including empty groups. -/
theorem convert_readback {layout : Schema} {options : PartitionPath.Options} {limits : Limits}
    {ipc : ObservationLimits} {keep : Scan.Predicate layout.keys.schema.toScan Value} {files : List File}
    {wire : KBytes} (written : convert layout options limits ipc keep files = .ok wire) :
    ∃ (trace : Trace layout) (batches : List DateUtf8Stream.Batch),
      readSelected layout options limits (projection layout) keep files = .ok trace ∧
      trace.termination = .eos ∧
      DateUtf8Stream.read ipc wire = .ok ⟨schema layout, batches⟩ ∧
      batches.map observe = trace.batches.map (observeSource layout) :=
  Proofs.Formats.Hive.Date32.Utf8.ManifestWriter.ToTypedIpc.convert_readback written

end Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter.ToTypedIpc
