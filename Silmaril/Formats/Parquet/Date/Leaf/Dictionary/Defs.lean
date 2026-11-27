module

public import Silmaril.Formats.Parquet.Date.Leaf.Events.Defs
public import Silmaril.Formats.Parquet.DictionaryChunk.Defs

/-! Opt-in uncompressed dictionary-only reading of a strict selected DATE leaf. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Date.Leaf.Dictionary

abbrev Limits := DictionaryChunk.Limits

inductive GroupError where
  | selection (cause : Leaf.Error)
  | chunk (cause : DictionaryChunk.Error)
  | missingDictionary
  | dictionaryEncoding
  | dataEncoding (page : Nat) (encoding : Int)
  | references (page offset : Nat) (cause : DictionaryIndex.Error)
  deriving DecidableEq, Repr

inductive Error where
  | openFailure (cause : Leaf.Error)
  | groupFailure (index : Nat) (cause : GroupError)
  deriving DecidableEq, Repr

inductive IpcError where
  | source (cause : Error)
  | closed
  | writer (cause : Arrow.DateStream.Writer.Error)
  deriving DecidableEq, Repr

/-- Check the existing selected chunk and use the shared CRC-rejecting INT32
dictionary framer within its original snapshot. -/
def frame (limits : Limits) (bound : Bound) (selection : Leaf.Chunk) :
    Except DictionaryChunk.Error DictionaryChunk.Chunk :=
  DictionaryChunk.read limits bound.snapshot.bytes bound.snapshot.footer.start bound.field
    selection.group.numRows.toNat selection.column.metadata

/-- Page zero is the chunk dictionary. Only modern RLE_DICTIONARY data is admitted. -/
def decodePage (limits : Limits) (bound : Bound) (dictionary : DictionaryChunk.Dictionary)
    (page : DictionaryChunk.DataPage) (ordinal : Nat) : Except GroupError Slots := do
  if page.params.encoding ≠ 8 then throw (.dataEncoding ordinal page.params.encoding)
  (DictionaryIndex.decode dictionary.entries page.params limits.scalar limits.indices
    (DictionaryChunk.body bound.snapshot.bytes page.frame)).mapError
    (.references ordinal page.frame.header.start)

/-- A modern data page reads the original mask and resolves its present indices
against the checked entries for this chunk. -/
def PageWire (limits : Limits) (source : Bytes) (dictionary : DictionaryChunk.Dictionary)
    (page : DictionaryChunk.DataPage) (slots : Slots) : Prop :=
  page.params.encoding = 8 ∧ DictionaryIndex.decode dictionary.entries page.params limits.scalar
    limits.indices (DictionaryChunk.body source page.frame) = .ok slots

structure CheckedGroup where
  selection : Leaf.Chunk
  chunk : DictionaryChunk.Chunk
  dictionary : DictionaryChunk.Dictionary

/-- Bind a leading modern PLAIN dictionary to its original selected chunk. -/
def checkGroup (limits : Limits) (bound : Bound) (index : Nat) : Except GroupError CheckedGroup := do
  let selection ← (selectChunk bound index).mapError .selection
  let chunk ← (frame limits bound selection).mapError .chunk
  let some dictionary := chunk.dictionary | throw .missingDictionary
  let .dictionary header := dictionary.frame.value.kind | throw .dictionaryEncoding
  if header.encoding ≠ 0 then throw .dictionaryEncoding
  return ⟨selection, chunk, dictionary⟩

/-- Decode each row group against its own leading PLAIN dictionary. -/
def readGroup (limits : Limits) (bound : Bound) (index : Nat) : Except GroupError Slots := do
  let checked ← checkGroup limits bound index
  let pages ← (checked.chunk.data.zipIdx 1).mapM fun (page, ordinal) =>
    decodePage limits bound checked.dictionary page ordinal
  return pages.flatten

/-- Framing and dictionary provenance, shared by dictionary-only and fallback reads. -/
structure GroupWire (limits : Limits) (bound : Bound) (index : Nat) (checked : CheckedGroup) : Prop where
  selected : selectChunk bound index = .ok checked.selection
  framed : frame limits bound checked.selection = .ok checked.chunk
  span : checked.chunk.span = checked.selection.span
  admitted : DictionaryChunk.Admitted limits bound.snapshot.bytes bound.snapshot.footer.start
    checked.selection.group.numRows.toNat bound.field.layout checked.selection.column.metadata checked.chunk
  chain : Page.Chain checked.selection.span checked.selection.span.start checked.selection.span.stop
    checked.chunk.frames
  payloads : ∀ page ∈ checked.chunk.frames, Page.FrameWithin checked.selection.span page.header.start page ∧
    (DictionaryChunk.body bound.snapshot.bytes page).length = page.value.compressedSize
  leading : checked.chunk.dictionary = some checked.dictionary
  plainDictionary : ∃ header, checked.dictionary.frame.value.kind = .dictionary header ∧ header.encoding = 0

def trace (limits : Limits) (bound : Bound) :
    Arrow.Events.Trace (Events.schema bound) Date.Events.Cell Error :=
  Events.traceWith bound (readGroup limits bound) .groupFailure

def readAll (input : Snapshot.Limits) (limits : Limits) (ordinal : Nat) (bytes : Bytes) :
    Arrow.Events.EventStream String Date.Events.Cell Error :=
  ((openLeaf input bytes ordinal).mapError .openFailure).map fun bound =>
    ⟨Events.schema bound, trace limits bound⟩

/-- Emit complete native IPC only after all selected groups decode through EOF. -/
def toIpc (input : Snapshot.Limits) (limits : Limits) (output : Arrow.ObservationLimits)
    (ordinal : Nat) (bytes : Bytes) : Except IpcError KBytes := do
  let bound ← (openLeaf input bytes ordinal).mapError (.source ∘ .openFailure)
  Events.emitWith output bound .source .closed .writer (trace limits bound)

end Silmaril.Formats.Parquet.Date.Leaf.Dictionary
