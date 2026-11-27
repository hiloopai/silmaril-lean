module

public import Silmaril.Formats.Parquet.Date.Leaf.MixedCodec.V2.Defs
public import Silmaril.Formats.Parquet.Date.Leaf.Snappy.Dispatch.V2.Defs

/-! Opt-in GZIP, Zstandard and Snappy V2 groups for one selected flat DATE leaf. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Date.Leaf.MixedCodec.V2.WithSnappy

structure Limits extends toTwoCodecLimits : MixedCodec.V2.Limits where
  snappy : Snappy.Dispatch.V2.Limits := {}

inductive GroupError where
  | twoCodec (cause : MixedCodec.V2.GroupError)
  | snappy (cause : Snappy.Dispatch.V2.GroupError)
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

/-- One lookup on the original selected footer determines the sole codec path. -/
def readGroup (limits : Limits) (bound : Bound) (index : Nat) : Except GroupError Slots := do
  let actual ← (MixedCodec.V2.selectedCodec bound index).mapError (.twoCodec ∘ .selection)
  if actual = Payload.Codec.snappy.id then
    (Snappy.Dispatch.V2.readGroup limits.snappy bound index).mapError .snappy
  else
    (MixedCodec.V2.readWithCodec limits.toTwoCodecLimits bound index actual).mapError .twoCodec

def trace (limits : Limits) (bound : Bound) :
    Arrow.Events.Trace (Events.schema bound) Date.Events.Cell Error :=
  Events.traceWith bound (readGroup limits bound) .groupFailure

def readAll (input : Snapshot.Limits) (limits : Limits) (ordinal : Nat) (bytes : Bytes) :
    Arrow.Events.EventStream String Date.Events.Cell Error :=
  ((openLeaf input bytes ordinal).mapError .openFailure).map fun bound =>
    ⟨Events.schema bound, trace limits bound⟩

/-- Emit native Date32 IPC after the checked source reaches EOS. -/
def toIpc (input : Snapshot.Limits) (limits : Limits) (output : Arrow.ObservationLimits)
    (ordinal : Nat) (bytes : Bytes) : Except IpcError KBytes := do
  let bound ← (openLeaf input bytes ordinal).mapError (.source ∘ .openFailure)
  Events.emitWith output bound .source .closed .writer (trace limits bound)

/-- The selected codec keeps its exact checked frame and CRC witnesses. -/
inductive GroupWire (limits : Limits) (bound : Bound) (index : Nat) (slots : Slots) : Prop where
  | twoCodec (wire : MixedCodec.V2.GroupWire limits.toTwoCodecLimits bound index slots)
  | snappy (selected : MixedCodec.V2.selectedCodec bound index = .ok Payload.Codec.snappy.id)
      (wire : Snappy.Dispatch.V2.GroupWire limits.snappy bound index slots)

end Silmaril.Formats.Parquet.Date.Leaf.MixedCodec.V2.WithSnappy
