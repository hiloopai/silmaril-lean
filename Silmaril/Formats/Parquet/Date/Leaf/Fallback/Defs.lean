module

public import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Defs

/-! Opt-in PLAIN fallback after a nonempty dictionary-coded prefix. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Date.Leaf.Fallback

open DictionaryChunk (DataPage)

abbrev Limits := Dictionary.Limits

inductive GroupError where
  | dictionary (cause : Dictionary.GroupError)
  | missingReferences
  | missingPlain
  | prefixEncoding (page offset : Nat) (encoding : Int)
  | suffixEncoding (page offset : Nat) (encoding : Int)
  | plain (page offset : Nat) (cause : ScalarPage.Error)
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

def isReference (page : DataPage) : Bool :=
  page.params.encoding == 8

/-- The original ordered data frames have two nonempty encoding phases. -/
def Ordered (data : List DataPage) : Prop :=
  ∃ references plain, data = references ++ plain ∧ references ≠ [] ∧ plain ≠ [] ∧
    (∀ page ∈ references, page.params.encoding = 8) ∧
    (∀ page ∈ plain, page.params.encoding = 0)

/-- The leading dictionary is page zero. Check the complete data sequence
before decoding, retaining original indices and absolute offsets. -/
def checkSequence (data : List DataPage) : Except GroupError Unit := do
  let first :: _ := data | throw .missingReferences
  if !isReference first then throw (.prefixEncoding 1 first.frame.header.start first.params.encoding)
  let suffix := data.dropWhile isReference
  if suffix.isEmpty then throw .missingPlain
  let firstPlain := data.length - suffix.length + 1
  match (suffix.zipIdx firstPlain).find? (fun (page, _) => page.params.encoding != 0) with
  | none => return ()
  | some (page, ordinal) => throw (.suffixEncoding ordinal page.frame.header.start page.params.encoding)

def checkGroup (limits : Limits) (bound : Bound) (index : Nat) :
    Except GroupError Dictionary.CheckedGroup := do
  let checked ← (Dictionary.checkGroup limits bound index).mapError .dictionary
  checkSequence checked.chunk.data
  return checked

def decodePage (limits : Limits) (bound : Bound) (dictionary : DictionaryChunk.Dictionary)
    (page : DataPage) (ordinal : Nat) : Except GroupError Slots :=
  if page.params.encoding = 0 then
    (ScalarPage.decode .int32 page.params limits.scalar
      (DictionaryChunk.body bound.snapshot.bytes page.frame)).mapError
      (.plain ordinal page.frame.header.start)
  else
    (Dictionary.decodePage limits bound dictionary page ordinal).mapError .dictionary

/-- The declared encoding selects the decoder for the original payload. -/
def PageWire (limits : Limits) (source : Bytes) (dictionary : DictionaryChunk.Dictionary)
    (page : DataPage) (slots : Slots) : Prop :=
  slots.length = page.params.numValues ∧
    (Dictionary.PageWire limits source dictionary page slots ∨
      (page.params.encoding = 0 ∧ ScalarPage.decode .int32 page.params limits.scalar
        (DictionaryChunk.body source page.frame) = .ok slots))

def readGroup (limits : Limits) (bound : Bound) (index : Nat) : Except GroupError Slots := do
  let checked ← checkGroup limits bound index
  let pages ← (checked.chunk.data.zipIdx 1).mapM fun (page, ordinal) =>
    decodePage limits bound checked.dictionary page ordinal
  return pages.flatten

def trace (limits : Limits) (bound : Bound) :
    Arrow.Events.Trace (Events.schema bound) Date.Events.Cell Error :=
  Events.traceWith bound (readGroup limits bound) .groupFailure

def readAll (input : Snapshot.Limits) (limits : Limits) (ordinal : Nat) (bytes : Bytes) :
    Arrow.Events.EventStream String Date.Events.Cell Error :=
  ((openLeaf input bytes ordinal).mapError .openFailure).map fun bound =>
    ⟨Events.schema bound, trace limits bound⟩

/-- Only a complete footer-order source trace can emit native IPC. -/
def toIpc (input : Snapshot.Limits) (limits : Limits) (output : Arrow.ObservationLimits)
    (ordinal : Nat) (bytes : Bytes) : Except IpcError KBytes := do
  let bound ← (openLeaf input bytes ordinal).mapError (.source ∘ .openFailure)
  Events.emitWith output bound .source .closed .writer (trace limits bound)

end Silmaril.Formats.Parquet.Date.Leaf.Fallback
