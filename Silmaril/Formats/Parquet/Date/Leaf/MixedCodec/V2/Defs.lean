module

public import Silmaril.Formats.Parquet.Date.Leaf.Gzip.Dispatch.V2.WithPlain.Defs
public import Silmaril.Formats.Parquet.Date.Leaf.Zstd.Dispatch.V2.Defs

/-! Opt-in mixed GZIP and Zstandard V2 groups for one selected flat DATE leaf. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Date.Leaf.MixedCodec.V2

structure Limits where
  gzip : Gzip.Dispatch.V2.WithPlain.Limits := {}
  zstd : Zstd.Dispatch.V2.Limits := {}

inductive GroupError where
  | selection (cause : Leaf.Error)
  | unsupportedCodec (actual : Int)
  | gzip (cause : Gzip.Dispatch.V2.WithPlain.GroupError)
  | zstd (cause : Zstd.Dispatch.V2.GroupError)
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

/-- Read the original codec ID from the selected physical column at this footer index. -/
def selectedCodec (bound : Bound) (index : Nat) : Except Leaf.Error Int := do
  let some group := bound.snapshot.groupAt index | throw (.groupIndex index)
  let some column := group.columns[bound.ordinal]? | throw (.chunkIndex bound.ordinal)
  return column.metadata.codec

/-- Choose exactly one V2 dispatcher by codec ID. Its existing checks own the
selected chunk, frame chain and payload. -/
def readGroup (limits : Limits) (bound : Bound) (index : Nat) : Except GroupError Slots := do
  let actual ← (selectedCodec bound index).mapError .selection
  if actual = Payload.Codec.gzip.id then
    (Gzip.Dispatch.V2.WithPlain.readGroup limits.gzip bound index).mapError .gzip
  else if actual = Payload.Codec.zstd.id then
    (Zstd.Dispatch.V2.readGroup limits.zstd bound index).mapError .zstd
  else
    .error (.unsupportedCodec actual)

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

/-- Each successful codec route retains its existing physical frame and
payload witness over the same checked snapshot. -/
inductive GroupWire (limits : Limits) (bound : Bound) (index : Nat) (slots : Slots) : Prop where
  | gzip (selected : selectedCodec bound index = .ok Payload.Codec.gzip.id)
      (wire : Gzip.Dispatch.V2.WithPlain.GroupWire limits.gzip bound index slots)
  | zstd (selected : selectedCodec bound index = .ok Payload.Codec.zstd.id)
      (wire : Zstd.Dispatch.V2.GroupWire limits.zstd bound index slots)

end Silmaril.Formats.Parquet.Date.Leaf.MixedCodec.V2
