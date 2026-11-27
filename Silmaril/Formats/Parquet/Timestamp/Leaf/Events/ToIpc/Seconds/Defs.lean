module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Defs

/-! Exact native Arrow seconds from a checked single-field Parquet millis file. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds

open Silmaril.Numeric.Timestamp (Ticks)

inductive Error where
  | source (cause : ToIpc.Error)
  | fieldCount (actual : Nat)
  | expectedMillis
  | nonintegral (group slot : Nat) (millis : Int)
  | writer (cause : Arrow.TimestampStream.Writer.Error)
  deriving DecidableEq, Repr

/-- Preserve the original name and nullability, with the canonical annotation
for the Parquet adjusted flag and exactly the seconds unit. -/
def binding (bound : Bound) : Arrow.TimestampBatch.Binding :=
  ⟨bound.binding.leaf.name, bound.binding.leaf.repetition == some .optional,
    bound.binding.descriptor.arrow .second⟩

/-- Exhaust the original PLAIN group reads before rescaling or sink work. -/
def readGroups (limits : Leaf.Limits) (bound : Bound) : Except Error (List (Slots bound)) :=
  (List.range bound.snapshot.groupCount).mapM fun index =>
    (Leaf.readGroup limits bound index).mapError fun cause => .source (.source (.groupFailure index cause))

namespace Internal

def rescaleSlot (bound : Bound) (group slot : Nat) (value : Option (Timestamp.Page.Value bound.binding)) :
    Except Error (Option (Arrow.TimestampBatch.Value (binding bound))) :=
  value.mapM fun millis =>
    match Ticks.rescale millis .second with
    | some seconds => .ok ⟨seconds.ticks⟩
    | none => .error (.nonintegral group slot millis.ticks)

def rescaleGroup (bound : Bound) (index : Nat) (slots : Slots bound) :
    Except Error (Arrow.TimestampBatch.Column (binding bound)) :=
  slots.zipIdx.mapM fun (value, slot) => rescaleSlot bound index slot value

end Internal

def rescaleGroups (bound : Bound) (groups : List (Slots bound)) :
    Except Error (List (Arrow.TimestampBatch.Column (binding bound))) :=
  if bound.snapshot.metadata.schema.length ≠ 2 then
    .error (.fieldCount (bound.snapshot.metadata.schema.length - 1))
  else if bound.binding.descriptor.unit ≠ .millis then .error .expectedMillis
  else groups.zipIdx.mapM fun (slots, group) => Internal.rescaleGroup bound group slots

/-- The strict modern binder selects field one. Every original group is read
before the opt-in exact rescale and native IPC writer. -/
def convert (inputLimits : ToIpc.Limits) (outputLimits : Arrow.ObservationLimits) (input : Bytes) :
    Except Error KBytes := do
  let bound ← (ToIpc.openBound inputLimits input 1).mapError .source
  let original ← readGroups inputLimits.leaf bound
  let batches ← rescaleGroups bound original
  (Arrow.TimestampStream.Writer.emit outputLimits (binding bound) batches).mapError .writer

end Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc.Seconds
