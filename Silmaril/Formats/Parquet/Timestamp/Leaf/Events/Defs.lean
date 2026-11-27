module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Defs
public import Silmaril.Formats.Parquet.Reader.Defs

/-! # Typed Arrow TIMESTAMP events from one checked Parquet leaf -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Events

open Silmaril.Relational Silmaril.Numeric.Timestamp

structure Kind where
  metadata : ColumnarTimestamp.Arrow.Metadata
  nullable : Bool
  deriving DecidableEq

abbrev Cell (kind : Kind) := Ticks kind.metadata.kind kind.metadata.unit

inductive Error where
  | openFailure (cause : Leaf.Error)
  | groupFailure (index : Nat) (cause : Leaf.Error)
  deriving DecidableEq, Repr

/-- Keep the original unit. The Arrow timezone annotation is UTC for an
adjusted Parquet timestamp and absent for a local reading. -/
def metadata (bound : Bound) : ColumnarTimestamp.Arrow.Metadata :=
  let descriptor := bound.binding.descriptor
  descriptor.arrow descriptor.unit.tickUnit

/-- One Arrow field with the selected Parquet leaf's name and nullability. -/
def schema (bound : Bound) : Scan.Schema String Kind :=
  ⟨1, fun _ => (bound.binding.leaf.name,
    ⟨metadata bound, bound.binding.leaf.repetition == some .optional⟩)⟩

/-- Each slot contributes one row with the same nullable signed count. -/
def rows (bound : Bound) (slots : Slots bound) : Reader.RowGroup (schema bound) Cell :=
  slots.map fun slot _ => slot.map fun tick => ⟨tick.ticks⟩

def rowsAtWith (bound : Bound) (read : Nat → Except Leaf.Error (Slots bound)) (index : Nat) :
    Except Error (Reader.RowGroup (schema bound) Cell) :=
  (read index).map (rows bound) |>.mapError (.groupFailure index)

def rowsAt (limits : Leaf.Limits) (bound : Bound) :=
  rowsAtWith bound (Leaf.readGroup limits bound)

/-- Pull the selected leaf once per footer row group, in ordinal order. -/
def groupSourceWith (bound : Bound) (read : Nat → Except Leaf.Error (Slots bound)) :
    Reader.Source Nat (schema bound) Cell Error :=
  ⟨List.range bound.snapshot.groupCount, rowsAtWith bound read, fun _ => .ok ()⟩

def groupSource (limits : Leaf.Limits) (bound : Bound) :=
  groupSourceWith bound (Leaf.readGroup limits bound)

/-- Read events from an already checked leaf using its selected group decoder. -/
def readBoundWith (bound : Bound) (read : Nat → Except Leaf.Error (Slots bound)) :
    Arrow.Events.EventStream String Cell Error :=
  Reader.readAll (.ok ⟨schema bound, groupSourceWith bound read⟩)

def readBound (limits : Leaf.Limits) (bound : Bound) :=
  readBoundWith bound (Leaf.readGroup limits bound)

/-- The input ordinal is the serialized schema-node index, with root at zero. -/
def openSource (snapshotLimits : Snapshot.Limits) (limits : Leaf.Limits) (ordinal : Nat)
    (input : Bytes) : Reader.OpenResult Nat String Cell Error :=
  ((Leaf.openLeaf snapshotLimits input ordinal).mapError .openFailure).map fun bound =>
    ⟨schema bound, groupSource limits bound⟩

def batchReader (snapshotLimits : Snapshot.Limits) (limits : Leaf.Limits) (ordinal : Nat) :
    Arrow.Events.BatchReader Bytes String Cell Error (fun s => Reader.Source Nat s Cell Error) :=
  Reader.batchReader (openSource snapshotLimits limits ordinal)

/-- Emit one batch for every successful group, including an admitted empty
group. A group failure keeps the preceding batches and terminates the trace. -/
def readAll (snapshotLimits : Snapshot.Limits) (limits : Leaf.Limits) (ordinal : Nat)
    (input : Bytes) : Arrow.Events.EventStream String Cell Error :=
  Reader.readAll (openSource snapshotLimits limits ordinal input)

/-- The reference reads the checked binder directly and stops at the first error. -/
def referenceGroupsWith {bound : Bound} (read : Nat → Except Leaf.Error (Slots bound)) :
    List Nat → List (Slots bound) × Arrow.Events.Termination Error
  | [] => ([], .eos)
  | index :: rest =>
    match read index with
    | .error cause => ([], .readError (.groupFailure index cause))
    | .ok slots =>
      let (following, outcome) := referenceGroupsWith read rest
      (slots :: following, outcome)

def referenceGroups (limits : Leaf.Limits) (bound : Bound) :=
  referenceGroupsWith (Leaf.readGroup limits bound)

end Silmaril.Formats.Parquet.Timestamp.Leaf.Events
