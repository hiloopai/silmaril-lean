module

public import Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter.Pruning.Defs
public import Silmaril.Formats.Arrow.DateUtf8Stream.Defs

/-! Export the selected virtual Hive DATE and UTF-8 columns through native IPC. -/

@[expose] public section

namespace Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter.ToTypedIpc

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Int32ByteArrayGroup.File (Value)

inductive Error where
  | admission (cause : Manifest.PrepareError Date32.Error)
  | source (cause : Events.Termination ReadError)
  | invalidUtf8 (batch : Nat)
  | writer (cause : DateUtf8Stream.Error)

def schema (layout : Schema) : DateUtf8Stream.Schema :=
  let order := match layout.keys.order with
    | .dateFirst => DateUtf8Stream.Order.dateFirst
    | .textFirst => DateUtf8Stream.Order.textFirst
  ⟨⟨layout.keys.date, true⟩, ⟨layout.keys.text, true⟩, order⟩

/-- Select the virtual suffix in the original declaration order. -/
def projection (layout : Schema) : Scan.Projection layout.toScan :=
  ⟨layout.keys.schema.toScan.width, fun i => i.natAdd layout.physical.width⟩

abbrev Batch (layout : Schema) := Events.Batch (projection layout).schema Value
abbrev Trace (layout : Schema) := Events.Trace (projection layout).schema Value ReadError

/-- Observe the original date and text slots by role. The descriptor fixes their wire order. -/
def slots (layout : Schema) (batch : Batch layout) : List (Option Int32) × List (Option Bytes) := by
  rcases layout with ⟨_, _, ⟨_, _, order⟩⟩
  cases order
  · exact (batch.values (0 : Fin 2), batch.values (1 : Fin 2))
  · exact (batch.values (1 : Fin 2), batch.values (0 : Fin 2))

def decodeText (value : Bytes) : Except Unit String :=
  if valid : value.data.IsValidUTF8 then .ok (String.fromUTF8 value.data valid) else .error ()

def prepareBatch (layout : Schema) (input : Batch layout) (index : Nat) : Except Error DateUtf8Stream.Batch := do
  let (dates, texts) := slots layout input
  let decoded ← (texts.mapM (Option.mapM decodeText)).mapError (fun _ => .invalidUtf8 index)
  return ⟨dates, decoded⟩

def prepare (layout : Schema) (trace : Trace layout) : Except Error (List DateUtf8Stream.Batch) :=
  trace.batches.zipIdx.mapM fun (batch, index) => prepareBatch layout batch index

/-- Compare the text observation in the source's UTF-8 byte carrier. -/
def observe (batch : DateUtf8Stream.Batch) : List (Option Int32) × List (Option ByteArray) :=
  (batch.dates, batch.texts.map (Option.map String.toUTF8))

def observeSource (layout : Schema) (batch : Batch layout) : List (Option Int32) × List (Option ByteArray) :=
  let (dates, texts) := slots layout batch
  (dates, texts.map (Option.map Bytes.data))

def encodeTrace (layout : Schema) (ipc : ObservationLimits) (trace : Trace layout) : Except Error KBytes :=
  if trace.termination = .eos then do
    let batches ← prepare layout trace
    (DateUtf8Stream.emit ipc (schema layout) batches).mapError .writer
  else .error (.source trace.termination)

/-- Complete typed admission and selection before checking sink capacity. -/
def convert (layout : Schema) (options : PartitionPath.Options) (limits : Limits)
    (ipc : ObservationLimits) (keep : Scan.Predicate layout.keys.schema.toScan Value) (files : List File) :
    Except Error KBytes := do
  let trace ← (readSelected layout options limits (projection layout) keep files).mapError .admission
  encodeTrace layout ipc trace

end Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter.ToTypedIpc
