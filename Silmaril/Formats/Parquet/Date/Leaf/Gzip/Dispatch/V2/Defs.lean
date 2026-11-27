module

public import Silmaril.Formats.Parquet.Date.Leaf.Dictionary.Gzip.V2.Defs

/-! Opt-in per-group dispatch for the dictionary-only and dictionary-to-PLAIN
GZIP DATE profiles with V2 data pages. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V2

abbrev Limits := Fallback.Gzip.Limits
abbrev CheckedGroup := Fallback.Gzip.CheckedGroup
abbrev GroupError := Fallback.Gzip.V2.GroupError
abbrev Error := Fallback.Gzip.V2.Error
abbrev IpcError := Fallback.Gzip.V2.IpcError

inductive Profile where
  | dictionary
  | fallback
  deriving DecidableEq, Repr

def isPlainV2 (frame : Page.Frame) : Bool :=
  match frame.value.kind with
  | .dataV2 header => header.encoding == 0
  | _ => false

/-- Choose the planner from the original framed data headers. The chosen
planner independently validates the version, tags and sequence. -/
def profile (frames : List Page.Frame) : Profile :=
  if frames.any isPlainV2 then .fallback else .dictionary

def dictionaryError : Dictionary.Gzip.V2.GroupError → GroupError
  | .chunk cause => .chunk cause
  | .header ordinal offset cause => .header ordinal offset cause

def planPages (bound : Bound) (frames : List Page.Frame) : Except GroupError (List DictionaryChunk.DataPage) :=
  match profile frames with
  | .dictionary => (Dictionary.Gzip.V2.planPages bound frames).mapError dictionaryError
  | .fallback => Fallback.Gzip.V2.planPages bound frames

/-- Frame the selected chunk once, run the chosen planner, and decode the
leading dictionary from the same snapshot. -/
def checkGroup (limits : Limits) (bound : Bound) (index : Nat) : Except GroupError CheckedGroup :=
  Dictionary.Snappy.checkGroupWithCodec .gzip .chunk (Fallback.Gzip.readEntries limits)
    (planPages bound) limits.toDictionaryLimits bound index

/-- Both plans supply the same checked page parameters to the existing GZIP
decoder. A decoder error terminates the group immediately. -/
def readGroup (limits : Limits) (bound : Bound) (index : Nat) : Except GroupError Slots :=
  Fallback.Gzip.readGroupWith (checkGroup limits bound) (Fallback.Gzip.V2.decodePage limits) bound index

def trace (limits : Limits) (bound : Bound) :
    Arrow.Events.Trace (Events.schema bound) Date.Events.Cell Error :=
  Events.traceWith bound (readGroup limits bound) .groupFailure

def readAll (input : Snapshot.Limits) (limits : Limits) (ordinal : Nat) (bytes : Bytes) :
    Arrow.Events.EventStream String Date.Events.Cell Error :=
  ((openLeaf input bytes ordinal).mapError .openFailure).map fun bound =>
    ⟨Events.schema bound, trace limits bound⟩

/-- Emit native Date32 IPC after the checked source reaches EOF. -/
def toIpc (input : Snapshot.Limits) (limits : Limits) (output : Arrow.ObservationLimits)
    (ordinal : Nat) (bytes : Bytes) : Except IpcError KBytes := do
  let bound ← (openLeaf input bytes ordinal).mapError (.source ∘ .openFailure)
  Events.emitWith output bound .source .closed .writer (trace limits bound)

/-- The original selected chunk has a framed dictionary position and
these ordered data frames. Further group or body checks can still fail. -/
def FramedGroup (limits : Limits) (bound : Bound) (index : Nat) (frames : List Page.Frame) : Prop :=
  ∃ selected dictionary, selectChunk bound index = .ok selected ∧
    Page.readChunk limits.page bound.snapshot.bytes selected.span = .ok (dictionary :: frames)

def Phase : Profile → List DictionaryChunk.DataPage → Prop
  | .dictionary, data => ∀ page ∈ data, page.params.encoding = 8
  | .fallback, data => Fallback.Ordered data

abbrev GroupWire (limits : Limits) (bound : Bound) (index : Nat) (checked : CheckedGroup) : Prop :=
  Dictionary.Snappy.GroupWireWith limits.toDictionaryLimits bound index checked .gzip
    (Fallback.Gzip.readEntries limits) (fun page => Fallback.Gzip.V2.planData bound page.frame = .ok page)

/-- The selected profile provides its original physical page witnesses. -/
def PagesWire (limits : Limits) (source : Bytes) (choice : Profile) (checked : CheckedGroup)
    (pages : List Slots) : Prop :=
  match choice with
  | .dictionary =>
    List.Forall₂ (Dictionary.Gzip.V2.PageWire limits source checked.entries.toArray) checked.data pages
  | .fallback =>
    List.Forall₂ (Fallback.Gzip.V2.PageWire limits source checked.entries.toArray) checked.data pages

end Silmaril.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V2
