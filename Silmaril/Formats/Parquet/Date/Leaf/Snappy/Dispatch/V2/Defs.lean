module

public import Silmaril.Formats.Parquet.Date.Leaf.Snappy.V2.Defs
public import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Snappy.V2.Defs

/-! Opt-in per-group dispatch across the three strict Snappy DATE V2 profiles. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Date.Leaf.Snappy.Dispatch.V2

abbrev Limits := Dictionary.Snappy.Limits
abbrev DictionaryProfile := Dictionary.Snappy.V2.Profile

/-- Share the same framing, scalar, row and chunk caps in both routes. -/
def plainLimits (limits : Limits) : Leaf.Snappy.V2.Limits :=
  ⟨limits.page, limits.scalar, limits.maxRows, limits.maxChunkBytes, limits.maxExpandedChunkBytes⟩

inductive Route where
  | plain
  | dictionaryBacked
  deriving DecidableEq, Repr

inductive GroupError where
  | selection (cause : Leaf.Error)
  | plain (cause : Leaf.Snappy.V2.GroupError)
  | dictionaryBacked (cause : Dictionary.Snappy.V2.GroupError)
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

/-- Route using the dictionary offset in the original selected footer column. -/
def route (bound : Bound) (index : Nat) : Except Leaf.Error Route := do
  let some group := bound.snapshot.groupAt index | throw (.groupIndex index)
  let some column := group.columns[bound.ordinal]? | throw (.chunkIndex bound.ordinal)
  return if column.metadata.dictionaryPageOffset.isSome then .dictionaryBacked else .plain

def isPlainV2 (frame : Page.Frame) : Bool :=
  match frame.value.kind with
  | .dataV2 header => header.encoding == 0
  | _ => false

/-- A PLAIN V2 data header selects the strict fallback planner. -/
def profile (frames : List Page.Frame) : DictionaryProfile :=
  if frames.any isPlainV2 then .fallback else .dictionaryOnly

def planPages (bound : Bound) (frames : List Page.Frame) :
    Except Dictionary.Snappy.V2.GroupError (List DictionaryChunk.DataPage) :=
  Dictionary.Snappy.V2.planPages (profile frames) bound frames

/-- The shared checker frames the chunk once. Its planner chooses from those
same headers, and the checked plan supplies the dictionary and data decoder. -/
def checkDictionaryGroup (limits : Limits) (bound : Bound) (index : Nat) :
    Except Dictionary.Snappy.V2.GroupError Dictionary.Snappy.CheckedGroup :=
  Dictionary.Snappy.checkGroupWith .chunk (planPages bound) limits bound index

def readDictionaryGroup (limits : Limits) (bound : Bound) (index : Nat) :
    Except Dictionary.Snappy.V2.GroupError Slots :=
  checkDictionaryGroup limits bound index >>= Dictionary.Snappy.V2.decodeGroup limits bound.snapshot.bytes

/-- Execute one strict route and return its result directly. -/
def readGroup (limits : Limits) (bound : Bound) (index : Nat) : Except GroupError Slots := do
  match ← (route bound index).mapError .selection with
  | .plain => (Leaf.Snappy.V2.readGroup (plainLimits limits) bound index).mapError .plain
  | .dictionaryBacked => (readDictionaryGroup limits bound index).mapError .dictionaryBacked

def trace (limits : Limits) (bound : Bound) :
    Arrow.Events.Trace (Events.schema bound) Date.Events.Cell Error :=
  Events.traceWith bound (readGroup limits bound) .groupFailure

def readAll (input : Snapshot.Limits) (limits : Limits) (ordinal : Nat) (bytes : Bytes) :
    Arrow.Events.EventStream String Date.Events.Cell Error :=
  ((openLeaf input bytes ordinal).mapError .openFailure).map fun bound =>
    ⟨Events.schema bound, trace limits bound⟩

/-- Emit native Date32 IPC only after source EOS. -/
def toIpc (input : Snapshot.Limits) (limits : Limits) (output : Arrow.ObservationLimits)
    (ordinal : Nat) (bytes : Bytes) : Except IpcError KBytes := do
  let bound ← (openLeaf input bytes ordinal).mapError (.source ∘ .openFailure)
  Events.emitWith output bound .source .closed .writer (trace limits bound)

/-- The selected original frame chain begins at the dictionary position. -/
def FramedGroup (limits : Limits) (bound : Bound) (index : Nat) (frames : List Page.Frame) : Prop :=
  ∃ selected dictionary, selectChunk bound index = .ok selected ∧
    Page.readChunk limits.page bound.snapshot.bytes selected.span = .ok (dictionary :: frames)

/-- A successful dispatch retains the chosen strict reader's original physical evidence. -/
inductive GroupWire (limits : Limits) (bound : Bound) (index : Nat) (slots : Slots) : Prop where
  | plain
      (routed : route bound index = .ok .plain)
      (decoded : Leaf.Snappy.V2.readGroup (plainLimits limits) bound index = .ok slots)
      (wire : Leaf.Snappy.V2.SlotsWire (plainLimits limits) bound index slots)
  | dictionaryBacked {frames : List Page.Frame}
      (routed : route bound index = .ok .dictionaryBacked)
      (original : FramedGroup limits bound index frames)
      (decoded : Dictionary.Snappy.V2.readGroup (profile frames) limits bound index = .ok slots)
      (wire : Dictionary.Snappy.V2.SlotsWire (profile frames) limits bound index slots)

end Silmaril.Formats.Parquet.Date.Leaf.Snappy.Dispatch.V2
