module

public import Silmaril.Formats.Parquet.ByteArrayFallback.Defs
public import Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Defs

/-! Opt-in uncompressed PLAIN dictionaries with STRING RLE_DICTIONARY data pages. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary

abbrev Limits := ByteArrayFallback.Limits
abbrev Checked (name : String) := Utf8.Checked name .optional

inductive DecodeError where
  | physical (cause : FlatColumn.PageError ByteArrayFallback.DecodeError)
  | invalidEntry (ordinal : Nat)
  | missingDictionary
  | indices (cause : DictionaryIndex.Error)
  deriving DecidableEq, Repr

abbrev GroupError := FlatColumn.Error DecodeError

inductive Error where
  | openFile (cause : Utf8.Error)
  | column (cause : GroupError)
  | writer (cause : Arrow.MixedFlat.OrderedWriter.Error)
  deriving DecidableEq, Repr

def openFile (limits : Limits) (input : Bytes) (name : String) : Except Utf8.Error (Checked name) :=
  Utf8.openFile limits.file input name .optional

def octets (text : String) : Bytes := ⟨text.toByteArray⟩

def decodeEntry (entry : Bytes × Nat) : Except DecodeError String :=
  match String.fromUTF8? entry.1.data with
  | some text => .ok text
  | none => .error (.invalidEntry entry.2)

/-- Validate every entry once, in original dictionary order, before resolving
any page indices. The error retains the dictionary page and entry ordinal. -/
def readDictionary (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes)
    (frame : Page.Frame) : Except (FlatColumn.PageError DecodeError) (Array String) := do
  let raw ← (ByteArrayFallback.readDictionary limits metadata source frame).mapError (.decode ∘ .physical)
  let texts ← (raw.toList.zipIdx.mapM decodeEntry).mapError .decode
  return texts.toArray

/-- Use the dictionary selected by the original leading frame. Require the
actual data-page tag to be 8 and decode the original bounded body. -/
def decodePage (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes)
    (dictionary : Option (Array String)) (frame : Page.Frame) :
    Except (FlatColumn.PageError DecodeError) (List (Option String)) := do
  (ByteArrayFallback.bodyLimits limits.file.column.maxPageBytes frame.value).mapError (.decode ∘ .physical)
  let some params := FlatColumn.pageParameters .optional 0 frame.value | throw .unsupportedKind
  if params.encoding ≠ 8 then throw (.encoding params.encoding)
  if !metadata.encodings.contains 8 then
    throw (.decode (.physical (.decode (.unadvertisedEncoding 8))))
  let cap := min limits.file.column.maxRows (Hybrid.runLimit - 1)
  if cap < params.numValues then throw (.slotLimit cap params.numValues)
  let some entries := dictionary | throw (.decode .missingDictionary)
  (DictionaryIndex.decode entries params limits.file.scalar limits.indices
    (FlatColumn.frameBody source frame)).mapError (.decode ∘ .indices)

def readFrames (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes)
    (group column : Nat) (name : String) (rows : Nat) (frames : List Page.Frame) :
    Except GroupError (List (Option String)) :=
  ByteArrayFallback.readFramesWith (readDictionary limits metadata source)
    (decodePage limits metadata source) metadata group column name rows frames

def readGroup {name : String} (limits : Limits) (checked : Checked name) (index : Nat) :
    Except GroupError (List (Option String)) :=
  ByteArrayFallback.readBoundGroupWith .rleDictionary checked.physical.binding limits (readFrames limits) index

/-- The complete dictionary round-trips every entry to the original PLAIN
bytes, including entries unreferenced by any data page. -/
def DictionaryWire (limits : Limits) (source : Bytes) (frame : Page.Frame) (entries : Array String) : Prop :=
  ByteArrayFallback.DictionaryWire limits source frame (entries.map octets)

/-- The original frame splits into checked levels and an exact index stream.
Indices resolve against the leading typed dictionary in wire order. -/
def PageWire (limits : Limits) (source : Bytes) (entries : Array String)
    (frame : Page.Frame) (slots : List (Option String)) : Prop :=
  let body := FlatColumn.frameBody source frame
  ∃ (params : ScalarPage.Parameters) (layout : FlatPage.Layout) (page : ScalarPage.Prepared) (indices : List Nat),
    FlatColumn.pageParameters .optional 0 frame.value = some params ∧ params.encoding = 8 ∧
    ScalarPage.validateFor 8 params limits.file.scalar body = .ok layout ∧
    ScalarPage.PreparedWire params limits.file.scalar layout body page ∧
    DictionaryIndex.readIndices limits.indices (page.mask.count true) page.scalars = .ok indices ∧
    indices.map (fun index => entries[index]?) = (slots.filterMap id).map some ∧
    indices.map (fun index => (entries.map octets)[index]?) = (slots.filterMap id).map (some ∘ octets) ∧
    slots.map Option.isSome = page.mask ∧ slots.length = ByteArrayFallback.declaredSlots frame

def FramesWire (limits : Limits) (metadata : Footer.ColumnMetadata) (source : Bytes) (rows : Nat)
    (frames : List Page.Frame) (slots : List (Option String)) : Prop :=
  ∃ dictionary data entries pages,
    frames = dictionary :: data ∧ metadata.dictionaryPageOffset = some (dictionary.header.start : Int) ∧
    data.head?.map (fun frame : Page.Frame => (frame.header.start : Int)) = some metadata.dataPageOffset ∧
    DictionaryWire limits source dictionary entries ∧ List.Forall₂ (PageWire limits source entries) data pages ∧
    slots = pages.flatten ∧ slots.length = rows

def GroupWire {name : String} (limits : Limits) (checked : Checked name) (index : Nat)
    (group : Footer.RowGroup) (slots : List (Option String)) : Prop :=
  ByteArrayFallback.BoundGroupWireWith checked.physical.binding limits (FramesWire limits) index group slots

/-- Exhaust the selected dictionary source before applying the IPC writer limits. -/
def convert (parquet : Limits) (ipc : Arrow.MixedFlat.Limits) (input : Bytes)
    (name : String) : Except Error KBytes := do
  let checked ← (openFile parquet input name).mapError .openFile
  let groups ← ((List.range checked.physical.snapshot.groupCount).mapM (readGroup parquet checked)).mapError .column
  (Arrow.MixedFlat.OrderedWriter.emit ipc (Utf8.fields name .optional)
    (groups.map (Utf8.batch name .optional))).mapError .writer

end Silmaril.Formats.Parquet.Plain.ByteArray.Utf8.Dictionary
