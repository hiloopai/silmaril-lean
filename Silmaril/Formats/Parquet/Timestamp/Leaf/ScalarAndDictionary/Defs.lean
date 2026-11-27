module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarDispatch.Defs
public import Silmaril.Formats.Parquet.Timestamp.Leaf.MixedCodec.V2.WithUncompressed.Defs
public import Mathlib.Data.List.Forall2

/-! One checked modern INT64 TIMESTAMP leaf with scalar or strict V2 dictionary groups. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary

open Silmaril.Relational
open Silmaril.Numeric.Timestamp (Ticks)

structure Limits where
  scalar : ScalarDispatch.Limits := {}
  dictionary : MixedCodec.V2.WithUncompressed.Limits := {}

inductive Codec where
  | uncompressed | snappy | gzip | zstd
  deriving DecidableEq, Repr

def Codec.id : Codec → Int
  | .uncompressed => 0
  | .snappy => 1
  | .gzip => 2
  | .zstd => 6

def Codec.ofId (id : Int) : Option Codec :=
  if id = 0 then some .uncompressed
  else if id = 1 then some .snappy
  else if id = 2 then some .gzip
  else if id = 6 then some .zstd
  else none

inductive Branch where
  | scalar (codec : Codec)
  | dictionary (codec : Codec)
  deriving DecidableEq, Repr

inductive UnsupportedProfile where
  | codec (actual : Int)
  | dictionaryEncodings (declared : List Int)
  deriving DecidableEq, Repr

inductive GroupError where
  | selection (cause : Leaf.Error)
  | unsupported (profile : UnsupportedProfile)
  | scalar (cause : Leaf.Error)
  | uncompressedDictionary (cause : Leaf.Error)
  | snappyDictionary (cause : Leaf.Error)
  | gzipDictionary (cause : Leaf.Error)
  | zstdDictionary (cause : Zstd.V2.GroupError)
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

def dictionaryEncodings (encodings : List Int) : Bool :=
  encodings.contains 8 && encodings.all (fun tag => tag == 0 || tag == 3 || tag == 8)

def Branch.Matches (metadata : Footer.ColumnMetadata) : Branch → Prop
  | .scalar codec => metadata.codec = codec.id ∧ metadata.dictionaryPageOffset = none
  | .dictionary codec =>
    metadata.codec = codec.id ∧ metadata.dictionaryPageOffset.isSome = true ∧
      dictionaryEncodings metadata.encodings = true

/-- Decide using only the selected footer. Each dictionary arm plans its own original frames. -/
def classify (metadata : Footer.ColumnMetadata) : Except UnsupportedProfile Branch :=
  match Codec.ofId metadata.codec with
  | none => .error (.codec metadata.codec)
  | some codec =>
    match metadata.dictionaryPageOffset with
    | none => .ok (.scalar codec)
    | some _ =>
      if dictionaryEncodings metadata.encodings then .ok (.dictionary codec)
      else .error (.dictionaryEncodings metadata.encodings)

def selectedColumn (bound : Bound) (index : Nat) : Except Leaf.Error Footer.ColumnChunk := do
  let some group := bound.snapshot.groupAt index | throw (.groupIndex index)
  let columnIndex := bound.ordinal - 1
  let some column := group.columns[columnIndex]? | throw (.chunkIndex columnIndex)
  return column

def route (bound : Bound) (index : Nat) : Except GroupError Branch := do
  let column ← (selectedColumn bound index).mapError .selection
  (classify column.metadata).mapError .unsupported

/-- Once routed, preserve the complete chosen branch result and configured limits. -/
def readSelected (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Branch → Except GroupError (Slots bound)
  | .scalar _ =>
    (ScalarDispatch.readGroup limits.scalar leafLimits bound index).mapError .scalar
  | .dictionary .uncompressed =>
    (Uncompressed.Dispatch.V2.readDictionary limits.dictionary.uncompressed leafLimits bound index).mapError
      .uncompressedDictionary
  | .dictionary .snappy =>
    (Snappy.Dispatch.V2.readDictionary limits.dictionary.threeCodec.snappy leafLimits bound index).mapError
      .snappyDictionary
  | .dictionary .gzip =>
    (Gzip.Dispatch.V2.readDictionary limits.dictionary.threeCodec.twoCodec.gzip leafLimits bound index).mapError
      .gzipDictionary
  | .dictionary .zstd =>
    (Zstd.Dispatch.V2.readDictionary limits.dictionary.threeCodec.twoCodec.zstd leafLimits bound index).mapError
      .zstdDictionary

def readGroup (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) (index : Nat) :
    Except GroupError (Slots bound) := do
  let branch ← route bound index
  readSelected limits leafLimits bound index branch

def trace (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound) :
    Arrow.Events.Trace (Events.schema bound) Events.Cell SourceError :=
  MixedCodec.V2.traceUsing bound (readGroup limits leafLimits bound) .groupFailure

/-- Bind the modern leaf once and emit native IPC only after complete source EOS. -/
def convert (limits : Limits) (inputLimits : Events.ToIpc.Limits) (output : Arrow.ObservationLimits)
    (input : Bytes) (ordinal : Nat) : Except Error KBytes := do
  let bound ← (Events.ToIpc.openBound inputLimits input ordinal).mapError .openFailure
  MixedCodec.V2.emitUsing output bound (trace limits inputLimits.leaf bound) .source .closed .writer

/-- Each successful branch carries the existing original-frame and ordered-slot witness. -/
def GroupWire (limits : Limits) (leafLimits : Leaf.Limits) (bound : Bound)
    (index : Nat) (slots : Slots bound) : Prop :=
  ∃ branch, route bound index = .ok branch ∧
    match branch with
    | .scalar _ =>
      ∃ group pages, ScalarDispatch.checkGroup leafLimits bound index = .ok group ∧
        List.Forall₂ (ScalarDispatch.PageWire limits.scalar leafLimits.page bound
          group.chunk.column.metadata.codec group.chunk.column.metadata.encodings) group.frames pages ∧
        slots = pages.flatten.map (Option.map bound.binding.descriptor.decode) ∧
        slots.map (Option.map Ticks.ticks) = pages.flatten.map (Option.map Int64.toInt) ∧
        slots.length = group.chunk.group.numRows.toNat
    | .dictionary .uncompressed =>
      ∃ plan, Uncompressed.Dispatch.V2.planDictionary limits.dictionary.uncompressed leafLimits bound index = .ok plan ∧
        Uncompressed.Dispatch.V2.DictionaryWire limits.dictionary.uncompressed leafLimits bound index plan slots
    | .dictionary .snappy =>
      ∃ plan, Snappy.Dispatch.V2.planDictionary limits.dictionary.threeCodec.snappy leafLimits bound index = .ok plan ∧
        Snappy.Dispatch.V2.DictionaryWire limits.dictionary.threeCodec.snappy leafLimits bound index plan slots
    | .dictionary .gzip =>
      ∃ plan, Gzip.Dispatch.V2.planDictionary limits.dictionary.threeCodec.twoCodec.gzip leafLimits bound index = .ok plan ∧
        Gzip.Dispatch.V2.DictionaryWire limits.dictionary.threeCodec.twoCodec.gzip leafLimits bound index plan slots
    | .dictionary .zstd =>
      ∃ plan, Zstd.Dispatch.V2.planDictionary limits.dictionary.threeCodec.twoCodec.zstd leafLimits bound index = .ok plan ∧
        Zstd.Dispatch.V2.DictionaryWire limits.dictionary.threeCodec.twoCodec.zstd leafLimits bound index plan slots

end Silmaril.Formats.Parquet.Timestamp.Leaf.ScalarAndDictionary
