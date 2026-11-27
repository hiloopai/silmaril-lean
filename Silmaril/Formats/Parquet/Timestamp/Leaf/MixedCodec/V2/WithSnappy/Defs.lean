module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.Defs
public import Silmaril.Formats.Parquet.Timestamp.Leaf.Snappy.Dispatch.V2.Defs

/-! Opt-in Snappy, GZIP and Zstandard V2 groups for one selected modern TIMESTAMP leaf. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithSnappy


structure Limits where
  snappy : Leaf.Dictionary.Limits := {}
  twoCodec : V2.Limits := {}

inductive GroupError where
  | snappy (cause : Leaf.Error)
  | twoCodec (cause : V2.GroupError)
  deriving DecidableEq, Repr

inductive SourceError where
  | groupFailure (index : Nat) (cause : GroupError)
  deriving DecidableEq, Repr

inductive Error where
  | openFailure (cause : Events.ToIpc.Error)
  | source (cause : SourceError)
  | closed
  | writer (cause : Arrow.TimestampStream.Writer.Error)
  deriving DecidableEq, Repr

def SourceError.ofTwoCodec : V2.SourceError → SourceError
  | .groupFailure index cause => .groupFailure index (.twoCodec cause)

def Error.ofTwoCodec : V2.Error → Error
  | .openFailure cause => .openFailure cause
  | .source cause => .source (SourceError.ofTwoCodec cause)
  | .closed => .closed
  | .writer cause => .writer cause

/-- Preserve the exact previous trace outcome under the added error constructor. -/
def terminationOfTwoCodec : Arrow.Events.Termination V2.SourceError → Arrow.Events.Termination SourceError
  | .eos => .eos
  | .closed => .closed
  | .readError cause => .readError (SourceError.ofTwoCodec cause)
  | .closeError cause => .closeError (SourceError.ofTwoCodec cause)

/-- Read the selected original footer codec ID once, then invoke its strict dispatcher. -/
def readGroup (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except GroupError (Slots bound) := do
  let codec ← (V2.selectedCodec bound index).mapError (.twoCodec ∘ .selection)
  if codec = Payload.Codec.snappy.id then
    (Snappy.Dispatch.V2.readGroup limits.snappy leafLimits bound index).mapError .snappy
  else
    (V2.readGroupForCodec limits.twoCodec leafLimits bound index codec).mapError .twoCodec

def trace (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) :
    Arrow.Events.Trace (Events.schema bound) Events.Cell SourceError :=
  V2.traceUsing bound (readGroup limits leafLimits bound) .groupFailure

/-- Open a modern selected leaf and emit its original group batches through native IPC EOS. -/
def convert (limits : Limits) (inputLimits : Events.ToIpc.Limits) (output : Arrow.ObservationLimits)
    (input : Bytes) (ordinal : Nat) : Except Error KBytes := do
  let bound ← (Events.ToIpc.openBound inputLimits input ordinal).mapError .openFailure
  V2.emitUsing output bound (trace limits inputLimits.leaf bound) .source .closed .writer

/-- Each admitted codec retains the strict wire evidence over the original snapshot. -/
inductive GroupWire (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (index : Nat) (slots : Slots bound) : Prop where
  | snappy (selected : V2.selectedCodec bound index = .ok Payload.Codec.snappy.id)
      (wire : Snappy.Dispatch.V2.GroupWire limits.snappy leafLimits bound index slots)
  | twoCodec (wire : V2.GroupWire limits.twoCodec leafLimits bound index slots)

end Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithSnappy
