module

public import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Zstd.V2.Defs

/-! Opt-in Zstandard DATE with a leading PLAIN dictionary and two nonempty
V2 phases, RLE_DICTIONARY followed by PLAIN. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Date.Leaf.Fallback.Zstd.V2

open DictionaryChunk (DataPage)

abbrev Limits := Dictionary.Zstd.V2.Limits
abbrev CheckedGroup := Dictionary.Zstd.V2.CheckedGroup
abbrev HeaderError := Dictionary.Zstd.V2.HeaderError

inductive GroupError where
  | dictionary (cause : Dictionary.Zstd.V2.GroupError)
  | header (page offset : Nat) (cause : HeaderError)
  | sequence (cause : Fallback.GroupError)
  | plain (cause : Leaf.Zstd.GroupError)
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

def planData (bound : Bound) (frame : Page.Frame) : Except HeaderError DataPage := do
  let .dataV2 header := frame.value.kind | throw .expectedV2
  if header.encoding ≠ 8 ∧ header.encoding ≠ 0 then throw (.encoding header.encoding)
  let some params := FlatColumn.pageParameters (Leaf.Zstd.columnLayout bound) Payload.Codec.zstd.id frame.value |
    throw .expectedV2
  return ⟨frame, params⟩

def planPages (bound : Bound) (frames : List Page.Frame) : Except GroupError (List DataPage) :=
  Fallback.planPagesWith (planData bound) (fun ordinal frame => GroupError.header ordinal frame.header.start)
    id .sequence frames

def checkGroup (limits : Limits) (bound : Bound) (index : Nat) : Except GroupError CheckedGroup :=
  Dictionary.Snappy.checkGroupWithDictionary .zstd (.dictionary ∘ Dictionary.Zstd.V2.GroupError.chunk)
    (fun frame cause => .dictionary (.dictionary frame.header.start cause))
    (Dictionary.Zstd.V2.readEntries limits) (planPages bound) limits.toChunkLimits bound index

abbrev GroupWire (limits : Limits) (bound : Bound) (index : Nat) (checked : CheckedGroup) :=
  Dictionary.Snappy.GroupWireWith limits.toChunkLimits bound index checked .zstd
    (Dictionary.Zstd.V2.readEntries limits) (fun page => planData bound page.frame = .ok page)

/-- Use the existing checked reader for the planned encoding and original frame. -/
def decodePage (limits : Limits) (bound : Bound) (metadata : Footer.ColumnMetadata)
    (entries : Array Int32) (page : DataPage) (ordinal : Nat) : Except GroupError Slots :=
  if page.params.encoding = 0 then
    (Leaf.Zstd.decodePage (Dictionary.Zstd.V2.scalarLimits limits) bound metadata
      ⟨page.frame, page.params⟩ ordinal).mapError .plain
  else
    (Dictionary.Zstd.V2.decodePage limits bound.snapshot.bytes entries page ordinal).mapError .dictionary

def readGroup (limits : Limits) (bound : Bound) (index : Nat) : Except GroupError Slots := do
  let checked ← checkGroup limits bound index
  let entries := checked.entries.toArray
  let pages ← (checked.data.zipIdx 1).mapM fun (page, ordinal) =>
    decodePage limits bound checked.selection.column.metadata entries page ordinal
  return pages.flatten

def trace (limits : Limits) (bound : Bound) :
    Arrow.Events.Trace (Events.schema bound) Date.Events.Cell Error :=
  Events.traceWith bound (readGroup limits bound) .groupFailure

def readAll (input : Snapshot.Limits) (limits : Limits) (ordinal : Nat) (bytes : Bytes) :
    Arrow.Events.EventStream String Date.Events.Cell Error :=
  ((openLeaf input bytes ordinal).mapError .openFailure).map fun bound =>
    ⟨Events.schema bound, trace limits bound⟩

/-- Emit complete Date32 IPC after the checked source reaches EOS. -/
def toIpc (input : Snapshot.Limits) (limits : Limits) (output : Arrow.ObservationLimits)
    (ordinal : Nat) (bytes : Bytes) : Except IpcError KBytes := do
  let bound ← (openLeaf input bytes ordinal).mapError (.source ∘ .openFailure)
  Events.emitWith output bound .source .closed .writer (trace limits bound)

/-- Each phase retains the exact raw levels, stored CRC, flag-specific suffix
and signed nullable slots established by the existing physical reader. -/
inductive PageWire (limits : Limits) (source : Bytes) (entries : Array Int32) (page : DataPage)
    (slots : Slots) : Prop where
  | reference (tag : page.params.encoding = 8)
      (wire : Dictionary.Zstd.V2.PageWire limits source entries page slots)
  | plain (tag : page.params.encoding = 0)
      (wire : Leaf.Zstd.V2.PageWire (Dictionary.Zstd.V2.scalarLimits limits) source
        ⟨page.frame, page.params⟩ slots)

end Silmaril.Formats.Parquet.Date.Leaf.Fallback.Zstd.V2
