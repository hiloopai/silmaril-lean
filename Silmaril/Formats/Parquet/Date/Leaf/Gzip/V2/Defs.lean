module

public import Silmaril.Formats.Parquet.Date.Leaf.Gzip.Defs

/-! Opt-in selected GZIP PLAIN DATE data page V2. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Date.Leaf.Gzip.V2

abbrev Limits := Gzip.Limits

inductive GroupError where
  | gzip (cause : Gzip.GroupError)
  | expectedV2 (ordinal offset : Nat)
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

/-- Keep the V2 compression flag and original level lengths. -/
def planData (bound : Bound) (frame : Page.Frame) (ordinal : Nat) :
    Except GroupError DataPage := do
  let .dataV2 header := frame.value.kind | throw (.expectedV2 ordinal frame.header.start)
  if header.encoding ≠ 0 then throw (.gzip (atFrame ordinal frame (.encoding header.encoding)))
  let some params := FlatScan.int32PageParameters bound.field frame.value |
    throw (.expectedV2 ordinal frame.header.start)
  return ⟨frame, { params with codec := Payload.Codec.gzip.id }⟩

/-- Reuse the original chunk extent, offsets, row count and both chunk caps. -/
def checkGroup (limits : Limits) (bound : Bound) (index : Nat) : Except GroupError CheckedGroup :=
  Gzip.checkGroupWith .gzip (planData bound) limits bound index

/-- The original stored payload is CRC-checked before the V2 scalar decoder
separates the raw levels and resolves the compression flag. -/
def decodePage (limits : Limits) (source : Bytes) (page : DataPage) (ordinal : Nat) :
    Except GroupError Slots :=
  (Gzip.decodePage limits source page ordinal).mapError .gzip

def readGroup (limits : Limits) (bound : Bound) (index : Nat) : Except GroupError Slots := do
  let checked ← checkGroup limits bound index
  let pages ← checked.data.zipIdx.mapM fun (page, ordinal) =>
    decodePage limits bound.snapshot.bytes page ordinal
  return pages.flatten

def trace (limits : Limits) (bound : Bound) :
    Arrow.Events.Trace (Events.schema bound) Date.Events.Cell Error :=
  Events.traceWith bound (readGroup limits bound) .groupFailure

def readAll (input : Snapshot.Limits) (limits : Limits) (ordinal : Nat) (bytes : Bytes) :
    Arrow.Events.EventStream String Date.Events.Cell Error :=
  ((openLeaf input bytes ordinal).mapError .openFailure).map fun bound =>
    ⟨Events.schema bound, trace limits bound⟩

/-- Publish a complete Date32 stream after the checked source reaches EOF. -/
def toIpc (input : Snapshot.Limits) (limits : Limits) (output : Arrow.ObservationLimits)
    (ordinal : Nat) (bytes : Bytes) : Except IpcError KBytes := do
  let bound ← (openLeaf input bytes ordinal).mapError (.source ∘ .openFailure)
  Events.emitWith output bound .source .closed .writer (trace limits bound)

end Silmaril.Formats.Parquet.Date.Leaf.Gzip.V2
