module

public import Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Dictionary.V2.Defs
public import Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Plain.V2.Defs

/-! Opt-in Zstandard V2 dictionary-to-PLAIN over one flat optional unannotated BYTE_ARRAY. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Fallback.V2

open Arrow.BinaryView

abbrev Limits := Zstd.Dictionary.V2.Limits

/-- Both phases share the selected file, expansion and Zstandard limits. -/
def plainLimits (limits : Limits) : Zstd.Plain.V2.Limits :=
  ⟨limits.file, limits.maxExpandedPageBytes, limits.maxExpandedChunkBytes, limits.compression⟩

inductive DecodeError where
  | dictionary (cause : FlatColumn.PageError Zstd.Dictionary.V2.DecodeError)
  | plain (cause : FlatColumn.PageError Zstd.Plain.V2.DecodeError)
  | dictionaryAfterPlain
  | missingDictionary
  deriving DecidableEq, Repr

abbrev GroupError := FlatColumn.Error DecodeError

inductive Error where
  | openFile (cause : Snappy.OpenError)
  | column (cause : GroupError)
  | writer (cause : StreamWriter.Error)
  deriving DecidableEq, Repr

def readDictionary (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes)
    (frame : Page.Frame) : Except (FlatColumn.PageError DecodeError) (Array Bytes) :=
  (Zstd.Dictionary.V2.readDictionary limits metadata source frame).mapError (.decode ∘ .dictionary)

/-- The original V2 header selects exactly one strict decoder. -/
def decodePage (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes)
    (dictionary : Option (Array Bytes)) (frame : Page.Frame) :
    Except (FlatColumn.PageError DecodeError) (List (Option Bytes)) := do
  let some entries := dictionary | throw (.decode .missingDictionary)
  match frame.value.kind with
  | .dataV2 header =>
    if header.encoding = 0 then
      (Zstd.Plain.V2.decodePage (plainLimits limits) metadata source frame).mapError (.decode ∘ .plain)
    else
      (Zstd.Dictionary.V2.decodePage limits metadata source (some entries) frame).mapError (.decode ∘ .dictionary)
  | .dataV1 _ => throw .unsupportedVersion
  | .dictionary _ | .skipped _ => throw .unsupportedKind

def readFrames (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes)
    (group column : Nat) (name : String) (rows : Nat) (frames : List Page.Frame) :
    Except GroupError (List (Option Bytes)) := do
  Plain.ByteArray.Utf8.Dictionary.Snappy.checkExpandedChunk limits.toPhysical metadata group column name frames
  let (dictionary, data) := ByteArrayFallback.splitLeading frames
  Plain.ByteArray.Utf8.Fallback.checkPhasesWith DecodeError.dictionaryAfterPlain group column name
    (if dictionary.isSome then 1 else 0) data
  ByteArrayFallback.readFramesWith (readDictionary limits metadata source) (decodePage limits metadata source)
    metadata group column name rows frames

def readGroup {name : String} (limits : Limits) (checked : Snappy.Checked name) (index : Nat) :
    Except GroupError (List (Option Bytes)) :=
  ByteArrayFallback.readBoundGroupWithCodec .zstd limits.maxExpandedChunkBytes .rleDictionary
    checked.physical.binding limits.toPhysical.toLimits (readFrames limits) index

def PageWire (limits : Limits) (source : Bytes) (entries : Array Bytes)
    (frame : Page.Frame) (slots : List (Option Bytes)) : Prop :=
  Zstd.Dictionary.V2.PageWire limits source entries frame slots ∨
    Zstd.Plain.V2.PageWire (plainLimits limits) source frame slots

def FramesWire (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes) (rows : Nat)
    (frames : List Page.Frame) (slots : List (Option Bytes)) : Prop :=
  Plain.ByteArray.Utf8.Dictionary.Snappy.expandedBytes frames ≤ limits.maxExpandedChunkBytes ∧
  (Plain.ByteArray.Utf8.Dictionary.Snappy.expandedBytes frames : Int) = metadata.totalUncompressedSize ∧
  ∃ (dictionary : Page.Frame) (data : List Page.Frame) (entries : Array Bytes) (pages : List (List (Option Bytes))),
    frames = dictionary :: data ∧ metadata.dictionaryPageOffset = some (dictionary.header.start : Int) ∧
    data.head?.map (fun frame : Page.Frame => (frame.header.start : Int)) = some metadata.dataPageOffset ∧
    Zstd.Dictionary.V2.DictionaryWire limits source dictionary entries ∧
    Plain.ByteArray.Utf8.Fallback.Phases data ∧ List.Forall₂ (PageWire limits source entries) data pages ∧
    slots = pages.flatten ∧ slots.length = rows

def GroupWire {name : String} (limits : Limits) (checked : Snappy.Checked name) (index : Nat)
    (group : Footer.RowGroup) (slots : List (Option Bytes)) : Prop :=
  ByteArrayFallback.BoundGroupWireWithCodec .zstd checked.physical.binding limits.toPhysical.toLimits
    (fun metadata source rows frames output =>
      (Plain.ByteArray.Utf8.Dictionary.Snappy.storedBytes frames : Int) = metadata.totalCompressedSize ∧
      Plain.ByteArray.Utf8.Dictionary.Snappy.storedBytes frames ≤ limits.file.column.maxChunkBytes ∧
      FramesWire limits metadata source rows frames output) index group slots

abbrev schema (name : String) := Plain.ByteArray.File.schema name .optional
abbrev Value := Plain.ByteArray.File.Value

def rowsAt {name : String} (limits : Limits) (checked : Snappy.Checked name) (index : Nat) :
    Except GroupError (Reader.RowGroup (schema name) Value) :=
  (readGroup limits checked index).map (Plain.ByteArray.File.rows name .optional)

def source {name : String} (limits : Limits) (checked : Snappy.Checked name) :
    Reader.Source Nat (schema name) Value GroupError :=
  ⟨List.range checked.physical.snapshot.groupCount, rowsAt limits checked, fun _ => .ok ()⟩

/-- Observe completed groups and the original termination of the checked source. -/
def readAll {name : String} (limits : Limits) (checked : Snappy.Checked name) :
    Arrow.Events.EventStream String Value GroupError :=
  Reader.readAll (.ok ⟨schema name, source limits checked⟩)

/-- Emit native BinaryView only after reading every selected group successfully. -/
def convert (parquet : Limits) (ipc : Arrow.Limits) (view : Column.Limits) (input : Bytes)
    (name : String) : Except Error KBytes := do
  let checked ← (Snappy.openFile parquet.toPhysical input name).mapError .openFile
  let groups ← ((List.range checked.physical.snapshot.groupCount).mapM (readGroup parquet checked)).mapError .column
  let source : Plain.ByteArray.ToIpc.Source := ⟨⟨name, true⟩, groups⟩
  (StreamWriter.emit ipc view source.ipcField source.batches).mapError .writer

end Silmaril.Formats.Parquet.ByteArrayFallback.Zstd.Fallback.V2
