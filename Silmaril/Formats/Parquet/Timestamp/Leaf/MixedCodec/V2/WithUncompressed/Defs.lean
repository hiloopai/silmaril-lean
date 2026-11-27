module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithSnappy.Defs
public import Silmaril.Formats.Parquet.Timestamp.Leaf.Uncompressed.Dispatch.V2.Defs

/-! Opt-in codec-0, Snappy, GZIP and Zstandard V2 groups for one modern TIMESTAMP leaf. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithUncompressed

structure Limits where
  uncompressed : Leaf.Dictionary.Limits := {}
  threeCodec : WithSnappy.Limits := {}

inductive GroupError where
  | uncompressed (cause : Leaf.Error)
  | threeCodec (cause : WithSnappy.GroupError)
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

def SourceError.ofThreeCodec : WithSnappy.SourceError → SourceError
  | .groupFailure index cause => .groupFailure index (.threeCodec cause)

def Error.ofThreeCodec : WithSnappy.Error → Error
  | .openFailure cause => .openFailure cause
  | .source cause => .source (SourceError.ofThreeCodec cause)
  | .closed => .closed
  | .writer cause => .writer cause

def terminationOfThreeCodec : Arrow.Events.Termination WithSnappy.SourceError → Arrow.Events.Termination SourceError
  | .eos => .eos
  | .closed => .closed
  | .readError cause => .readError (SourceError.ofThreeCodec cause)
  | .closeError cause => .closeError (SourceError.ofThreeCodec cause)

/-- Read the original selected footer codec once and pass it to the chosen dispatcher. -/
def readGroup (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except GroupError (Slots bound) := do
  let codec ← (V2.selectedCodec bound index).mapError (.threeCodec ∘ .twoCodec ∘ .selection)
  if codec = Payload.Codec.uncompressed.id then
    (Uncompressed.Dispatch.V2.readGroup limits.uncompressed leafLimits bound index).mapError .uncompressed
  else
    (WithSnappy.readGroupForCodec limits.threeCodec leafLimits bound index codec).mapError .threeCodec

def trace (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) :
    Arrow.Events.Trace (Events.schema bound) Events.Cell SourceError :=
  V2.traceUsing bound (readGroup limits leafLimits bound) .groupFailure

/-- Emit the selected original footer groups through native IPC EOS. -/
def convert (limits : Limits) (inputLimits : Events.ToIpc.Limits) (output : Arrow.ObservationLimits)
    (input : Bytes) (ordinal : Nat) : Except Error KBytes := do
  let bound ← (Events.ToIpc.openBound inputLimits input ordinal).mapError .openFailure
  V2.emitUsing output bound (trace limits inputLimits.leaf bound) .source .closed .writer

/-- Each route retains the strict wire evidence over the same bound snapshot. -/
inductive GroupWire (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (index : Nat) (slots : Slots bound) : Prop where
  | uncompressed (selected : V2.selectedCodec bound index = .ok Payload.Codec.uncompressed.id)
      (wire : Uncompressed.Dispatch.V2.GroupWire limits.uncompressed leafLimits bound index slots)
  | threeCodec (wire : WithSnappy.GroupWire limits.threeCodec leafLimits bound index slots)

end Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithUncompressed
