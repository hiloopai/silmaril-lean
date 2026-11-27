module

public import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary.Defs

/-! Opt-in uncompressed STRING with an original dictionary-to-PLAIN transition. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Fallback

abbrev Limits := Dictionary.Limits
abbrev Checked (name : String) := Dictionary.Checked name

inductive DecodeError where
  | dictionary (cause : FlatColumn.PageError Dictionary.DecodeError)
  | physical (cause : FlatColumn.PageError ByteArrayFallback.DecodeError)
  | plain (cause : File.PageError)
  | invalidPlainText (slot : Nat)
  | dictionaryAfterPlain
  | missingDictionary
  deriving DecidableEq, Repr

abbrev GroupError := FlatColumn.Error DecodeError

inductive Error where
  | openFile (cause : Utf8.Error)
  | column (cause : GroupError)
  | writer (cause : Arrow.MixedFlat.OrderedWriter.Error)
  deriving DecidableEq, Repr

def dataEncoding (frame : Page.Frame) : Option Int :=
  (FlatColumn.pageParameters .optional 0 frame.value).map (·.encoding)

def isDictionaryData (frame : Page.Frame) : Bool := dataEncoding frame == some 8

def checkPlainTag (group column : Nat) (name : String) (ordinal : Nat) (frame : Page.Frame) :
    Except GroupError PUnit :=
  let fail := FlatColumn.Error.page group column name ordinal frame.header.start
  match dataEncoding frame with
  | some 0 => .ok ⟨⟩
  | some 8 => .error (fail (.decode .dictionaryAfterPlain))
  | some actual => .error (fail (.encoding actual))
  | none => .error (fail .unsupportedKind)

/-- Check the whole tag schedule on the original headers before decoding
any bodies. A missing phase is a column-level encoding refusal. -/
def checkPhases (group column : Nat) (name : String) (firstOrdinal : Nat)
    (data : List Page.Frame) : Except GroupError PUnit := do
  let dictionaryPages := data.takeWhile isDictionaryData
  let plainPages := data.dropWhile isDictionaryData
  if dictionaryPages.isEmpty || plainPages.isEmpty then throw (.column group column name .encodings)
  plainPages.zipIdx (firstOrdinal + dictionaryPages.length) |>.forM fun (frame, ordinal) =>
    checkPlainTag group column name ordinal frame

def decodePlain (limits : Limits) (leaf : Footer.SchemaElement) (metadata : Footer.ColumnMetadata)
    (source : Bytes) (frame : Page.Frame) : Except (FlatColumn.PageError DecodeError) (List (Option String)) := do
  (ByteArrayFallback.bodyLimits limits.file.column.maxPageBytes frame.value).mapError (.decode ∘ .physical)
  if !metadata.encodings.contains 0 then
    throw (.decode (.physical (.decode (.unadvertisedEncoding 0))))
  let raw ← (File.decodePage limits.file .optional leaf metadata frame.value
    (FlatColumn.frameBody source frame)).mapError (.decode ∘ .plain)
  (Utf8.decodeSlotsWith DecodeError.invalidPlainText raw).mapError .decode

/-- Dispatch from the original header. The checked phase order determines
where the chunk-local typed dictionary may be used. -/
def decodeData (limits : Limits) (leaf : Footer.SchemaElement) (metadata : Footer.ColumnMetadata)
    (source : Bytes) (dictionary : Option (Array String)) (frame : Page.Frame) :
    Except (FlatColumn.PageError DecodeError) (List (Option String)) := do
  let some entries := dictionary | throw (.decode .missingDictionary)
  match dataEncoding frame with
  | some 8 => (Dictionary.decodePage limits metadata source (some entries) frame).mapError (.decode ∘ .dictionary)
  | some 0 => decodePlain limits leaf metadata source frame
  | some actual => throw (.encoding actual)
  | none => throw .unsupportedKind

def readFrames (limits : Limits) (leaf : Footer.SchemaElement) (metadata : Footer.ColumnMetadata)
    (source : Bytes) (group column : Nat) (name : String) (rows : Nat) (frames : List Page.Frame) :
    Except GroupError (List (Option String)) := do
  let (dictionary, data) := ByteArrayFallback.splitLeading frames
  checkPhases group column name (if dictionary.isSome then 1 else 0) data
  ByteArrayFallback.readFramesWith
    (fun frame => (Dictionary.readDictionary limits metadata source frame).mapError (.decode ∘ .dictionary))
    (decodeData limits leaf metadata source) metadata group column name rows frames

def readGroup {name : String} (limits : Limits) (checked : Checked name) (index : Nat) :
    Except GroupError (List (Option String)) :=
  ByteArrayFallback.readBoundGroupWith .rleDictionary checked.physical.binding limits
    (readFrames limits checked.physical.binding.leaf) index

/-- Exact data-frame order, with both encoding phases present. -/
def Phases (data : List Page.Frame) : Prop :=
  ∃ dictionaryPages plainPages, data = dictionaryPages ++ plainPages ∧ dictionaryPages ≠ [] ∧ plainPages ≠ [] ∧
    (∀ frame ∈ dictionaryPages, dataEncoding frame = some 8) ∧ (∀ frame ∈ plainPages, dataEncoding frame = some 0)

def PlainPageWire (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes)
    (frame : Page.Frame) (slots : List (Option String)) : Prop :=
  slots.length = ByteArrayFallback.declaredSlots frame ∧
  File.PageWire limits.file .optional metadata source frame (slots.map (Option.map Dictionary.octets))

def PageWire (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes) (entries : Array String)
    (frame : Page.Frame) (slots : List (Option String)) : Prop :=
  (dataEncoding frame = some 8 ∧ Dictionary.PageWire limits source entries frame slots) ∨
    (dataEncoding frame = some 0 ∧ PlainPageWire limits metadata source frame slots)

def FramesWire (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes) (rows : Nat)
    (frames : List Page.Frame) (slots : List (Option String)) : Prop :=
  ∃ dictionary data entries pages,
    frames = dictionary :: data ∧ metadata.dictionaryPageOffset = some (dictionary.header.start : Int) ∧
    data.head?.map (fun frame : Page.Frame => (frame.header.start : Int)) = some metadata.dataPageOffset ∧
    Dictionary.DictionaryWire limits source dictionary entries ∧ Phases data ∧
    List.Forall₂ (PageWire limits metadata source entries) data pages ∧ slots = pages.flatten ∧ slots.length = rows

def GroupWire {name : String} (limits : Limits) (checked : Checked name) (index : Nat)
    (group : Footer.RowGroup) (slots : List (Option String)) : Prop :=
  ByteArrayFallback.BoundGroupWireWith checked.physical.binding limits (FramesWire limits) index group slots

/-- The complete selected source succeeds before any IPC limit is applied. -/
def convert (parquet : Limits) (ipc : Arrow.MixedFlat.Limits) (input : Bytes) (name : String) : Except Error KBytes := do
  let checked ← (Dictionary.openFile parquet input name).mapError .openFile
  let groups ← ((List.range checked.physical.snapshot.groupCount).mapM (readGroup parquet checked)).mapError .column
  (Arrow.MixedFlat.OrderedWriter.emit ipc (Utf8.fields name .optional)
    (groups.map (Utf8.batch name .optional))).mapError .writer

end Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Fallback
