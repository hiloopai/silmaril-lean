module

public import Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter.Pruning.Defs
public import Silmaril.Formats.Arrow.BinaryView.StreamWriter.Defs
public import Silmaril.Formats.Parquet.Plain.ByteArray.ToIpc.Source.Defs

/-! Export the selected opaque Hive payload as a native BinaryView IPC stream. -/

@[expose] public section

namespace Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter.ToIpc

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Int32ByteArrayGroup.File (Value)
open Arrow.BinaryView
open Plain.ByteArray.ToIpc (Source)

inductive Error where
  | admission (cause : Manifest.PrepareError Date32.Error)
  | source (cause : Events.Termination ReadError)
  | writer (cause : StreamWriter.Error)

/-- Select only the second physical leaf, regardless of the virtual key order. -/
def projection (layout : Schema) : Scan.Projection layout.toScan :=
  ⟨1, fun _ => (1 : Fin 2).castAdd layout.keys.schema.toScan.width⟩

abbrev Trace (layout : Schema) := Events.Trace (projection layout).schema Value ReadError

/-- One list of nullable opaque slots per retained batch, even at row count zero. -/
def groups (layout : Schema) (trace : Trace layout) : List (List (Option Bytes)) :=
  trace.batches.map fun batch => batch.values (0 : Fin 1)

def binarySource (layout : Schema) (trace : Trace layout) : Source :=
  ⟨⟨layout.byteName, true⟩, groups layout trace⟩

/-- Pass complete source batches to the existing exact-readback writer. -/
def encodeTrace (layout : Schema) (ipc : Arrow.Limits) (view : Column.Limits) (trace : Trace layout) :
    Except Error KBytes :=
  match trace.termination with
  | .eos =>
    let source := binarySource layout trace
    (StreamWriter.emit ipc view source.ipcField source.batches).mapError .writer
  | outcome => .error (.source outcome)

/-- Admit all paths and complete the selected scan before attempting IPC admission. -/
def convert (layout : Schema) (options : PartitionPath.Options) (limits : Limits)
    (ipc : Arrow.Limits) (view : Column.Limits) (keep : Scan.Predicate layout.keys.schema.toScan Value)
    (files : List File) : Except Error KBytes := do
  let trace ← (readSelected layout options limits (projection layout) keep files).mapError .admission
  encodeTrace layout ipc view trace

end Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter.ToIpc
