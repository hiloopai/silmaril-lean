module

public import Silmaril.Formats.Arrow.BinaryView.StreamWriter.Defs
public import Silmaril.Formats.Parquet.Plain.ByteArray.ToIpc.Source.Defs
public import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Fallback.Snappy.Defs

/-! An opt-in opaque Snappy BYTE_ARRAY fallback source and native BinaryView export. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.ByteArrayFallback.Snappy

open Plain.ByteArray
open Arrow.BinaryView
open Footer.ColumnOrder (FlatLeaf field?)

abbrev Limits := Utf8.Dictionary.Snappy.Limits

inductive OpenError where
  | physical (cause : File.Error)
  | footer (cause : Footer.ColumnOrder.Error)
  | annotation (fieldId : Int)
  deriving DecidableEq, Repr

/-- Binary BYTE_ARRAY uses neither logical nor converted annotation. -/
def checkUnannotated (leaf : FlatLeaf) : Except OpenError Unit := do
  let fields := leaf.selection.leaf.item.fields
  let .none ← (field? fields 10).mapError .footer | throw (.annotation 10)
  let .none ← (field? fields 6).mapError .footer | throw (.annotation 6)
  pure ()

structure Checked (name : String) where
  physical : File.Checked name .optional
  unannotated : ∃ limits selected, Footer.ColumnOrder.readFlat limits physical.snapshot
    physical.binding.columnOrdinal = .ok selected ∧ checkUnannotated selected = .ok ()

/-- Inspect the serialized annotation fields of the original selected flat leaf. -/
def openFile (limits : Limits) (input : Bytes) (name : String) : Except OpenError (Checked name) := do
  let physical ← (File.openFile limits.file input name .optional).mapError .physical
  match bound : Footer.ColumnOrder.readFlat limits.file.snapshot.footer physical.snapshot
      physical.binding.columnOrdinal with
  | .error cause => .error (.footer cause)
  | .ok selected =>
    match checked : checkUnannotated selected with
    | .error cause => .error cause
    | .ok () => .ok ⟨physical, limits.file.snapshot.footer, selected, bound, checked⟩

inductive DecodeError where
  | dictionary (cause : FlatColumn.PageError Utf8.Dictionary.Snappy.DecodeError)
  | plain (cause : FlatColumn.PageError Utf8.Fallback.Snappy.DecodeError)
  | dictionaryAfterPlain
  | missingDictionary
  deriving DecidableEq, Repr

abbrev GroupError := FlatColumn.Error DecodeError

inductive Error where
  | openFile (cause : OpenError)
  | column (cause : GroupError)
  | writer (cause : StreamWriter.Error)
  deriving DecidableEq, Repr

/-- Resolve typed original indices to opaque bytes and keep PLAIN fallback opaque. -/
def decodeData (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes)
    (dictionary : Option (Array Bytes)) (frame : Page.Frame) :
    Except (FlatColumn.PageError DecodeError) (List (Option Bytes)) := do
  let some entries := dictionary | throw (.decode .missingDictionary)
  match Utf8.Fallback.dataEncoding frame with
  | some 8 =>
    (Utf8.Dictionary.Snappy.decodeIndexPage limits metadata source (some entries) frame).mapError (.decode ∘ .dictionary)
  | some 0 =>
    (Utf8.Fallback.Snappy.decodePlainBytes limits metadata source frame).mapError (.decode ∘ .plain)
  | some actual => throw (.encoding actual)
  | none => throw .unsupportedKind

def readDictionary (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes) (frame : Page.Frame) :
    Except (FlatColumn.PageError DecodeError) (Array Bytes) :=
  ((Utf8.Dictionary.Snappy.readDictionaryBytes limits metadata source frame).map List.toArray).mapError
    (.decode ∘ .dictionary)

def readFrames (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes)
    (group column : Nat) (name : String) (rows : Nat) (frames : List Page.Frame) :
    Except GroupError (List (Option Bytes)) := do
  Utf8.Dictionary.Snappy.checkExpandedChunk limits metadata group column name frames
  let (dictionary, data) := ByteArrayFallback.splitLeading frames
  Utf8.Fallback.checkPhasesWith DecodeError.dictionaryAfterPlain group column name (if dictionary.isSome then 1 else 0) data
  ByteArrayFallback.readFramesWith (readDictionary limits metadata source) (decodeData limits metadata source)
    metadata group column name rows frames

def readGroup {name : String} (limits : Limits) (checked : Checked name) (index : Nat) :
    Except GroupError (List (Option Bytes)) :=
  ByteArrayFallback.readBoundGroupWithCodec .snappy limits.maxExpandedChunkBytes .rleDictionary
    checked.physical.binding limits.toLimits (readFrames limits) index

def PageWire (limits : Limits) (source : Bytes) (entries : Array Bytes)
    (frame : Page.Frame) (slots : List (Option Bytes)) : Prop :=
  (Utf8.Fallback.dataEncoding frame = some 8 ∧ Utf8.Dictionary.Snappy.IndexPageWire limits source entries frame slots) ∨
  (Utf8.Fallback.dataEncoding frame = some 0 ∧ Utf8.Fallback.Snappy.PlainBytesWire limits source frame slots)

def FramesWire (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes) (rows : Nat)
    (frames : List Page.Frame) (slots : List (Option Bytes)) : Prop :=
  Utf8.Dictionary.Snappy.expandedBytes frames ≤ limits.maxExpandedChunkBytes ∧
  (Utf8.Dictionary.Snappy.expandedBytes frames : Int) = metadata.totalUncompressedSize ∧
  ∃ (dictionary : Page.Frame) (data : List Page.Frame) (entries : Array Bytes) (pages : List (List (Option Bytes))),
    frames = dictionary :: data ∧ metadata.dictionaryPageOffset = some (dictionary.header.start : Int) ∧
    data.head?.map (fun frame : Page.Frame => (frame.header.start : Int)) = some metadata.dataPageOffset ∧
    Utf8.Dictionary.Snappy.DictionaryBytesWire limits source dictionary entries.toList ∧ Utf8.Fallback.Phases data ∧
    List.Forall₂ (PageWire limits source entries) data pages ∧ slots = pages.flatten ∧ slots.length = rows

def GroupWire {name : String} (limits : Limits) (checked : Checked name) (index : Nat)
    (group : Footer.RowGroup) (slots : List (Option Bytes)) : Prop :=
  ByteArrayFallback.BoundGroupWireWithCodec .snappy checked.physical.binding limits.toLimits
    (fun metadata source rows frames output =>
      (Utf8.Dictionary.Snappy.storedBytes frames : Int) = metadata.totalCompressedSize ∧
      Utf8.Dictionary.Snappy.storedBytes frames ≤ limits.file.column.maxChunkBytes ∧
      FramesWire limits metadata source rows frames output) index group slots

/-- Complete all selected groups before applying native BinaryView writer limits. -/
def convert (parquet : Limits) (ipc : Arrow.Limits) (view : Column.Limits) (input : Bytes)
    (name : String) : Except Error KBytes := do
  let checked ← (openFile parquet input name).mapError .openFile
  let groups ← ((List.range checked.physical.snapshot.groupCount).mapM (readGroup parquet checked)).mapError .column
  let source : ToIpc.Source := ⟨⟨name, true⟩, groups⟩
  (StreamWriter.emit ipc view source.ipcField source.batches).mapError .writer

end Silmaril.Formats.Parquet.ByteArrayFallback.Snappy
