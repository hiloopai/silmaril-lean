module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Gzip.Dispatch.V2.Defs
public import Silmaril.Formats.Parquet.Timestamp.Leaf.Zstd.Dispatch.V2.Defs

/-! Opt-in GZIP and Zstandard V2 groups for one selected modern TIMESTAMP leaf. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2

open Silmaril.Relational

structure Limits where
  gzip : Gzip.Dispatch.V2.Limits := {}
  zstd : Zstd.Dispatch.V2.Limits := {}

inductive GroupError where
  | selection (cause : Leaf.Error)
  | unsupportedCodec (actual : Int)
  | gzip (cause : Leaf.Error)
  | zstd (cause : Zstd.V2.GroupError)
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

/-- The flat leaf's serialized schema ordinal is one greater than its chunk index. -/
def selectedCodec (bound : Bound) (index : Nat) : Except Leaf.Error Int := do
  let some group := bound.snapshot.groupAt index | throw (.groupIndex index)
  let columnIndex := bound.ordinal - 1
  let some column := group.columns[columnIndex]? | throw (.chunkIndex columnIndex)
  return column.metadata.codec

/-- Decode a selected group after its original footer codec has been read. -/
def readGroupForCodec (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) (index : Nat)
    (codec : Int) : Except GroupError (Slots bound) :=
  if codec = Payload.Codec.gzip.id then
    (Gzip.Dispatch.V2.readGroup limits.gzip leafLimits bound index).mapError .gzip
  else if codec = Payload.Codec.zstd.id then
    (Zstd.Dispatch.V2.readGroup limits.zstd leafLimits bound index).mapError .zstd
  else
    .error (.unsupportedCodec codec)

/-- Route by the selected column's original footer codec. Only that dispatcher
checks and decodes the original chunk. -/
def readGroup (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except GroupError (Slots bound) := do
  let codec ← (selectedCodec bound index).mapError .selection
  readGroupForCodec limits leafLimits bound index codec

def rowsAtUsing {ε δ : Type} (bound : Bound) (read : Nat → Except ε (Slots bound)) (tag : Nat → ε → δ)
    (index : Nat) : Except δ (Reader.RowGroup (Events.schema bound) Events.Cell) :=
  ((read index).map (Events.rows bound)).mapError (tag index)

def rowsAt (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except SourceError (Reader.RowGroup (Events.schema bound) Events.Cell) :=
  rowsAtUsing bound (readGroup limits leafLimits bound) .groupFailure index

/-- Collect one batch per original group up to source EOS or the first typed error. -/
def traceUsing {ε δ : Type} (bound : Bound) (read : Nat → Except ε (Slots bound)) (tag : Nat → ε → δ) :
    Arrow.Events.Trace (Events.schema bound) Events.Cell δ :=
  let groups := Reader.denoteGroups (rowsAtUsing bound read tag) (List.range bound.snapshot.groupCount)
  ⟨groups.1.map AlignedColumns.ofRows, groups.2⟩

def trace (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) :
    Arrow.Events.Trace (Events.schema bound) Events.Cell SourceError :=
  traceUsing bound (readGroup limits leafLimits bound) .groupFailure

/-- Only an EOS trace from the bound leaf can reach IPC writer admission. -/
def emitUsing {ε δ : Type} (output : Arrow.ObservationLimits) (bound : Bound)
    (events : Arrow.Events.Trace (Events.schema bound) Events.Cell ε)
    (sourceError : ε → δ) (closed : δ) (writerError : Arrow.TimestampStream.Writer.Error → δ) :
    Except δ KBytes :=
  match events.termination with
  | .readError cause | .closeError cause => .error (sourceError cause)
  | .closed => .error closed
  | .eos =>
    let batches := events.batches.map fun batch => batch.values ⟨0, Nat.zero_lt_one⟩
    (Arrow.TimestampStream.Writer.emit output (Events.ToIpc.selectedBinding bound) batches).mapError writerError

/-- Read the checked modern leaf through source EOS before admitting the native IPC writer. -/
def convert (limits : Limits) (inputLimits : Events.ToIpc.Limits) (output : Arrow.ObservationLimits)
    (input : Bytes) (ordinal : Nat) : Except Error KBytes := do
  let bound ← (Events.ToIpc.openBound inputLimits input ordinal).mapError .openFailure
  emitUsing output bound (trace limits inputLimits.leaf bound) .source .closed .writer

/-- A completed route retains the strict codec witness on the same bound leaf. -/
inductive GroupWire (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (index : Nat) (slots : Slots bound) : Prop where
  | gzip (selected : selectedCodec bound index = .ok Payload.Codec.gzip.id)
      (wire : Gzip.Dispatch.V2.GroupWire limits.gzip leafLimits bound index slots)
  | zstd (selected : selectedCodec bound index = .ok Payload.Codec.zstd.id)
      (wire : Zstd.Dispatch.V2.GroupWire limits.zstd leafLimits bound index slots)

end Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2
