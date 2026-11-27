module

public import Silmaril.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V2.Defs
public import Silmaril.Formats.Parquet.Date.Leaf.Gzip.V2.Defs

/-! Opt-in GZIP DATE V2 dispatch across PLAIN-only, dictionary-only, and
dictionary-to-PLAIN row groups in one checked snapshot. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V2.WithPlain

abbrev Limits := Fallback.Gzip.Limits

/-- The PLAIN and dictionary routes share bounds for frames, scalars, rows
and stored and expanded chunk bytes. Dictionary and index caps apply to
dictionary-backed groups. -/
def plainLimits (limits : Limits) : Date.Leaf.Gzip.V2.Limits :=
  ⟨limits.page, limits.scalar, limits.maxRows, limits.maxChunkBytes, limits.maxExpandedChunkBytes⟩

inductive Route where
  | plain
  | dictionaryBacked
  deriving DecidableEq, Repr

inductive GroupError where
  | selection (cause : Leaf.Error)
  | plain (cause : Date.Leaf.Gzip.V2.GroupError)
  | dictionaryBacked (cause : Date.Leaf.Gzip.Dispatch.V2.GroupError)
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

/-- Look up the original footer group and selected physical column. The
chosen reader checks the full column association, range and layout. -/
def route (bound : Bound) (index : Nat) : Except Leaf.Error Route := do
  let some group := bound.snapshot.groupAt index | throw (.groupIndex index)
  let some column := group.columns[bound.ordinal]? | throw (.chunkIndex bound.ordinal)
  return if column.metadata.dictionaryPageOffset.isSome then .dictionaryBacked else .plain

/-- Dispatch on the original dictionary offset. The dictionary-backed
reader chooses between its two profiles from the original framed headers. -/
def readGroup (limits : Limits) (bound : Bound) (index : Nat) : Except GroupError Slots := do
  match ← (route bound index).mapError .selection with
  | .plain => (Date.Leaf.Gzip.V2.readGroup (plainLimits limits) bound index).mapError .plain
  | .dictionaryBacked => (Date.Leaf.Gzip.Dispatch.V2.readGroup limits bound index).mapError .dictionaryBacked

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

/-- An admitted group retains the selected reader's original frame and page witnesses. -/
inductive GroupWire (limits : Limits) (bound : Bound) (index : Nat) (slots : Slots) : Prop where
  | plain {checked : Date.Leaf.Gzip.CheckedGroup} {pages : List Slots}
      (routed : route bound index = .ok .plain)
      (accepted : Date.Leaf.Gzip.V2.checkGroup (plainLimits limits) bound index = .ok checked)
      (chunk : Date.Leaf.Gzip.GroupWire (plainLimits limits) bound index checked
        (fun page => ∃ ordinal, Date.Leaf.Gzip.V2.planData bound page.frame ordinal = .ok page))
      (decoded : List.Forall₂ (Date.Leaf.Gzip.PageWire (plainLimits limits) bound.snapshot.bytes)
        checked.data pages)
      (ordered : slots = pages.flatten) (count : slots.length = checked.selection.group.numRows.toNat)
  | dictionaryBacked {checked : Date.Leaf.Gzip.Dispatch.V2.CheckedGroup} {pages : List Slots}
      (routed : route bound index = .ok .dictionaryBacked)
      (accepted : Date.Leaf.Gzip.Dispatch.V2.checkGroup limits bound index = .ok checked)
      (chunk : Date.Leaf.Gzip.Dispatch.V2.GroupWire limits bound index checked)
      (nonempty : checked.data ≠ [])
      (phase : Date.Leaf.Gzip.Dispatch.V2.Phase
        (Date.Leaf.Gzip.Dispatch.V2.profile (checked.data.map (·.frame))) checked.data)
      (decoded : Date.Leaf.Gzip.Dispatch.V2.PagesWire limits bound.snapshot.bytes
        (Date.Leaf.Gzip.Dispatch.V2.profile (checked.data.map (·.frame))) checked pages)
      (ordered : slots = pages.flatten) (count : slots.length = checked.selection.group.numRows.toNat)

end Silmaril.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V2.WithPlain
