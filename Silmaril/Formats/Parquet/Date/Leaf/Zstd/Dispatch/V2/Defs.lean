module

public import Silmaril.Formats.Parquet.Date.Leaf.Fallback.Zstd.V2.Defs

/-! Opt-in per-group dispatch across the three checked Zstandard DATE V2 profiles. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Date.Leaf.Zstd.Dispatch.V2

abbrev Limits := Dictionary.Zstd.V2.Limits
abbrev CheckedGroup := Dictionary.Zstd.V2.CheckedGroup

inductive Route where
  | plain
  | dictionaryBacked
  deriving DecidableEq, Repr

inductive DictionaryProfile where
  | dictionary
  | fallback
  deriving DecidableEq, Repr

inductive GroupError where
  | selection (cause : Leaf.Error)
  | plain (cause : Leaf.Zstd.V2.GroupError)
  | dictionaryBacked (cause : Fallback.Zstd.V2.GroupError)
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

/-- Read the dictionary offset from the selected original footer column. -/
def route (bound : Bound) (index : Nat) : Except Leaf.Error Route := do
  let some group := bound.snapshot.groupAt index | throw (.groupIndex index)
  let some column := group.columns[bound.ordinal]? | throw (.chunkIndex bound.ordinal)
  return if column.metadata.dictionaryPageOffset.isSome then .dictionaryBacked else .plain

def isPlainV2 (frame : Page.Frame) : Bool :=
  match frame.value.kind with
  | .dataV2 header => header.encoding == 0
  | _ => false

/-- Route on the original framed headers. The chosen strict planner validates the sequence. -/
def profile (frames : List Page.Frame) : DictionaryProfile :=
  if frames.any isPlainV2 then .fallback else .dictionary

def planPages (bound : Bound) (frames : List Page.Frame) :
    Except Fallback.Zstd.V2.GroupError (List DictionaryChunk.DataPage) :=
  match profile frames with
  | .dictionary => (Dictionary.Zstd.V2.planPages bound frames).mapError .dictionary
  | .fallback => Fallback.Zstd.V2.planPages bound frames

/-- Frame the selected dictionary-backed chunk once and use that same chain
for route selection, strict planning and decoding. -/
def checkDictionaryGroup (limits : Limits) (bound : Bound) (index : Nat) :
    Except Fallback.Zstd.V2.GroupError CheckedGroup :=
  Dictionary.Snappy.checkGroupWithDictionary .zstd
    (Fallback.Zstd.V2.GroupError.dictionary ∘ Dictionary.Zstd.V2.GroupError.chunk)
    (fun frame cause => .dictionary (.dictionary frame.header.start cause))
    (Dictionary.Zstd.V2.readEntries limits) (planPages bound) limits.toChunkLimits bound index

def readDictionaryGroup (limits : Limits) (bound : Bound) (index : Nat) :
    Except Fallback.Zstd.V2.GroupError Slots :=
  checkDictionaryGroup limits bound index >>= Fallback.Zstd.V2.decodeGroup limits bound

/-- Execute the selected path and return its first failure directly. -/
def readGroup (limits : Limits) (bound : Bound) (index : Nat) : Except GroupError Slots := do
  match ← (route bound index).mapError .selection with
  | .plain => (Leaf.Zstd.V2.readGroup (Dictionary.Zstd.V2.scalarLimits limits) bound index).mapError .plain
  | .dictionaryBacked => (readDictionaryGroup limits bound index).mapError .dictionaryBacked

def trace (limits : Limits) (bound : Bound) :
    Arrow.Events.Trace (Events.schema bound) Date.Events.Cell Error :=
  Events.traceWith bound (readGroup limits bound) .groupFailure

def readAll (input : Snapshot.Limits) (limits : Limits) (ordinal : Nat) (bytes : Bytes) :
    Arrow.Events.EventStream String Date.Events.Cell Error :=
  ((openLeaf input bytes ordinal).mapError .openFailure).map fun bound =>
    ⟨Events.schema bound, trace limits bound⟩

/-- Emit native Date32 IPC after the original footer-order source reaches EOS. -/
def toIpc (input : Snapshot.Limits) (limits : Limits) (output : Arrow.ObservationLimits)
    (ordinal : Nat) (bytes : Bytes) : Except IpcError KBytes := do
  let bound ← (openLeaf input bytes ordinal).mapError (.source ∘ .openFailure)
  Events.emitWith output bound .source .closed .writer (trace limits bound)

/-- A framed dictionary position and its actual following frames from the checked snapshot. -/
def FramedGroup (limits : Limits) (bound : Bound) (index : Nat) (frames : List Page.Frame) : Prop :=
  ∃ selected dictionary, selectChunk bound index = .ok selected ∧
    Page.readChunk limits.page bound.snapshot.bytes selected.span = .ok (dictionary :: frames)

def Phase : DictionaryProfile → List DictionaryChunk.DataPage → Prop
  | .dictionary, data => ∀ page ∈ data, page.params.encoding = 8
  | .fallback, data => Fallback.Ordered data

def PagesWire (limits : Limits) (source : Bytes) (choice : DictionaryProfile) (checked : CheckedGroup)
    (pages : List Slots) : Prop :=
  match choice with
  | .dictionary => List.Forall₂
      (Dictionary.Zstd.V2.PageWire limits source checked.entries.toArray) checked.data pages
  | .fallback => List.Forall₂
      (Fallback.Zstd.V2.PageWire limits source checked.entries.toArray) checked.data pages

/-- Each group retains the original selected frame chain and the exact
physical page evidence for its chosen strict profile. -/
inductive GroupWire (limits : Limits) (bound : Bound) (index : Nat) (slots : Slots) : Prop where
  | plain {checked : Gzip.CheckedGroup} {pages : List Slots}
      (routed : route bound index = .ok .plain)
      (accepted : Leaf.Zstd.V2.checkGroup (Dictionary.Zstd.V2.scalarLimits limits) bound index = .ok checked)
      (chunk : Leaf.Zstd.V2.GroupWire (Dictionary.Zstd.V2.scalarLimits limits) bound index checked)
      (decoded : List.Forall₂
        (Leaf.Zstd.V2.PageWire (Dictionary.Zstd.V2.scalarLimits limits) bound.snapshot.bytes) checked.data pages)
      (ordered : slots = pages.flatten) (count : slots.length = checked.selection.group.numRows.toNat)
  | dictionaryBacked {checked : CheckedGroup} {pages : List Slots}
      (routed : route bound index = .ok .dictionaryBacked)
      (accepted : checkDictionaryGroup limits bound index = .ok checked)
      (chunk : Fallback.Zstd.V2.GroupWire limits bound index checked)
      (dictionary : Dictionary.Zstd.V2.DictionaryWire limits bound.snapshot.bytes checked.dictionary checked.entries)
      (nonempty : checked.data ≠ [])
      (phase : Phase (profile (checked.data.map (·.frame))) checked.data)
      (decoded : PagesWire limits bound.snapshot.bytes (profile (checked.data.map (·.frame))) checked pages)
      (ordered : slots = pages.flatten) (count : slots.length = checked.selection.group.numRows.toNat)

end Silmaril.Formats.Parquet.Date.Leaf.Zstd.Dispatch.V2
