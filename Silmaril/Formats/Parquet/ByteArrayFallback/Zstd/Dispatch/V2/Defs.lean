module

public import Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Fallback.V2.Defs

/-! Opt-in per-group dispatch over original opaque Zstandard V2 frames. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Dispatch.V2

open Arrow.BinaryView

abbrev Limits := Zstd.Fallback.V2.Limits

inductive Profile where
  | plain
  | dictionary
  | fallback
  deriving DecidableEq, Repr

def isPlainV2 (frame : Page.Frame) : Bool :=
  match frame.value.kind with
  | .dataV2 header => header.encoding == 0
  | _ => false

/-- A leading dictionary and the presence of an original V2 PLAIN tag select
the strict callback. The selected callback checks the complete schedule. -/
def profile (frames : List Page.Frame) : Profile :=
  match ByteArrayFallback.splitLeading frames with
  | (none, _) => .plain
  | (some _, data) => if data.any isPlainV2 then .fallback else .dictionary

inductive DecodeError where
  | plain (cause : Zstd.Plain.V2.DecodeError)
  | dictionary (cause : Zstd.Dictionary.V2.DecodeError)
  | fallback (cause : Zstd.Fallback.V2.DecodeError)
  deriving DecidableEq, Repr

abbrev GroupError := FlatColumn.Error DecodeError

inductive Error where
  | openFile (cause : Snappy.OpenError)
  | column (cause : GroupError)
  | writer (cause : StreamWriter.Error)
  deriving DecidableEq, Repr

/-- Lift the decoder cause while retaining the original page error shape. -/
def liftPageError {α β : Type} (lift : α → β) : FlatColumn.PageError α → FlatColumn.PageError β
  | .crcUnsupported => .crcUnsupported
  | .checksum cause => .checksum cause
  | .byteLimit => .byteLimit
  | .sizeMismatch => .sizeMismatch
  | .unsupportedKind => .unsupportedKind
  | .unsupportedVersion => .unsupportedVersion
  | .encoding actual => .encoding actual
  | .levels => .levels
  | .cardinality => .cardinality
  | .slotLimit maximum actual => .slotLimit maximum actual
  | .outputCount expected actual => .outputCount expected actual
  | .nullCount => .nullCount
  | .decode cause => .decode (lift cause)

/-- All selection and wire coordinates are copied from the strict result. -/
def liftGroupError {α β : Type} (lift : α → β) : FlatColumn.Error α → FlatColumn.Error β
  | .groupIndex group => .groupIndex group
  | .column group column name cause => .column group column name cause
  | .page group column name ordinal offset cause =>
    .page group column name ordinal offset (liftPageError lift cause)

def readFrames (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes)
    (group column : Nat) (name : String) (rows : Nat) (frames : List Page.Frame) :
    Except GroupError (List (Option Bytes)) :=
  match profile frames with
  | .plain =>
    (Zstd.Plain.V2.readFrames (Zstd.Fallback.V2.plainLimits limits) metadata source group column name rows frames)
      |>.mapError (liftGroupError .plain)
  | .dictionary =>
    (Zstd.Dictionary.V2.readFrames limits metadata source group column name rows frames)
      |>.mapError (liftGroupError .dictionary)
  | .fallback =>
    (Zstd.Fallback.V2.readFrames limits metadata source group column name rows frames)
      |>.mapError (liftGroupError .fallback)

/-- Frame the selected chunk once and pass the original list to one strict reader. -/
def readGroup {name : String} (limits : Limits) (checked : Snappy.Checked name) (index : Nat) :
    Except GroupError (List (Option Bytes)) :=
  ByteArrayFallback.readBoundGroupWithCodec .zstd limits.maxExpandedChunkBytes .rleDictionary
    checked.physical.binding limits.toPhysical.toLimits (readFrames limits) index

/-- The selected original chunk and complete frame list are attached to the same snapshot. -/
def FramedGroup {name : String} (limits : Limits) (checked : Snappy.Checked name)
    (index : Nat) (frames : List Page.Frame) : Prop :=
  ∃ group column span,
    checked.physical.snapshot.groupAt index = some group ∧
    group.columns[checked.physical.binding.columnOrdinal]? = some column ∧
    ByteArrayFallback.locateForCodec .zstd limits.maxExpandedChunkBytes .rleDictionary limits.toPhysical.toLimits
      checked.physical.binding.leaf group column.metadata checked.physical.snapshot.footer.start = .ok span ∧
    Page.readChunk limits.file.column.framing checked.physical.snapshot.bytes span = .ok frames

def FramesWire (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes) (rows : Nat)
    (frames : List Page.Frame) (slots : List (Option Bytes)) : Prop :=
  match profile frames with
  | .plain => Zstd.Plain.V2.FramesWire (Zstd.Fallback.V2.plainLimits limits) metadata source rows frames slots
  | .dictionary => Zstd.Dictionary.V2.FramesWire limits metadata source rows frames slots
  | .fallback => Zstd.Fallback.V2.FramesWire limits metadata source rows frames slots

def GroupWire {name : String} (limits : Limits) (checked : Snappy.Checked name) (index : Nat)
    (group : Footer.RowGroup) (slots : List (Option Bytes)) : Prop :=
  ByteArrayFallback.BoundGroupWireWithCodec .zstd checked.physical.binding limits.toPhysical.toLimits
    (fun metadata source rows frames output =>
      (Plain.ByteArray.Utf8.Dictionary.Snappy.storedBytes frames : Int) = metadata.totalCompressedSize ∧
      Plain.ByteArray.Utf8.Dictionary.Snappy.storedBytes frames ≤ limits.file.column.maxChunkBytes ∧
      FramesWire limits metadata source rows frames output) index group slots

abbrev schema := Zstd.Fallback.V2.schema
abbrev Value := Zstd.Fallback.V2.Value

def rowsAt {name : String} (limits : Limits) (checked : Snappy.Checked name) (index : Nat) :
    Except GroupError (Reader.RowGroup (schema name) Value) :=
  (readGroup limits checked index).map (Plain.ByteArray.File.rows name .optional)

def source {name : String} (limits : Limits) (checked : Snappy.Checked name) :
    Reader.Source Nat (schema name) Value GroupError :=
  ⟨List.range checked.physical.snapshot.groupCount, rowsAt limits checked, fun _ => .ok ()⟩

/-- Emit the original complete-group prefix and its EOS or indexed error. -/
def readAll {name : String} (limits : Limits) (checked : Snappy.Checked name) :
    Arrow.Events.EventStream String Value GroupError :=
  Reader.readAll (.ok ⟨schema name, source limits checked⟩)

/-- Publish native BinaryView after successful exhaustion of the selected source. -/
def convert (parquet : Limits) (ipc : Arrow.Limits) (view : Column.Limits) (input : Bytes)
    (name : String) : Except Error KBytes := do
  let checked ← (Snappy.openFile parquet.toPhysical input name).mapError .openFile
  let groups ← ((List.range checked.physical.snapshot.groupCount).mapM (readGroup parquet checked)).mapError .column
  let output : Plain.ByteArray.ToIpc.Source := ⟨⟨name, true⟩, groups⟩
  (StreamWriter.emit ipc view output.ipcField output.batches).mapError .writer

end Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Dispatch.V2
