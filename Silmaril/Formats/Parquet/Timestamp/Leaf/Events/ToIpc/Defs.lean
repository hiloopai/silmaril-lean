module

public import Silmaril.Formats.Parquet.Timestamp.Leaf.Events.Defs
public import Silmaril.Formats.Arrow.TimestampStream.Writer.Defs

/-! One checked Parquet TIMESTAMP leaf to native Arrow V5 IPC. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc

open Silmaril.Relational

structure Limits where
  snapshot : Snapshot.Limits := {}
  leaf : Leaf.Limits := {}
  maxFileBytes : Nat := 256 * 1024 * 1024
  maxGroups : Nat := 4096
  maxTotalRows : Nat := 1024 * 1024

abbrev Source := Arrow.Events.EventStream String Cell Events.Error

inductive Error where
  | fileByteLimit (maximum actual : Nat)
  | groupLimit (maximum actual : Nat)
  | rowLimit (maximum actual : Nat)
  | source (cause : Events.Error)
  | closed
  | fieldCount (actual : Nat)
  | writer (cause : Arrow.TimestampStream.Writer.Error)
  deriving DecidableEq, Repr

/-- Bound the entire source before pulling rows from the checked selection. -/
def openBoundUsing (limits : Limits) (input : Bytes) (bind : Bytes → Except Leaf.Error Leaf.Bound) :
    Except Error Leaf.Bound :=
  if limits.maxFileBytes < input.length then .error (.fileByteLimit limits.maxFileBytes input.length)
  else do
    let bound ← (bind input).mapError (.source ∘ .openFailure)
    let groups := bound.snapshot.groupCount
    let rows := bound.snapshot.metadata.numRows.toNat
    if limits.maxGroups < groups then .error (.groupLimit limits.maxGroups groups)
    else if limits.maxTotalRows < rows then .error (.rowLimit limits.maxTotalRows rows)
    else .ok bound

def openBoundWith (profile : AnnotationProfile) (limits : Limits) (input : Bytes) (ordinal : Nat) :
    Except Error Leaf.Bound :=
  openBoundUsing limits input (fun bytes => Leaf.openLeafWith profile limits.snapshot bytes ordinal)

def openBound (limits : Limits) (input : Bytes) (ordinal : Nat) : Except Error Leaf.Bound :=
  openBoundWith .modernOnly limits input ordinal

def boundEvents (limits : Leaf.Limits) (bound : Leaf.Bound) : Source :=
  Events.readBound limits bound

/-- Use the source descriptor itself, retaining its original unit and epoch interpretation. -/
def bindingAt (schema : Scan.Schema String Kind) (column : Fin schema.width) : Arrow.TimestampBatch.Binding :=
  let field := schema.kind column
  ⟨field.1, field.2.nullable, field.2.metadata⟩

def selectedBinding (bound : Leaf.Bound) : Arrow.TimestampBatch.Binding :=
  bindingAt (Events.schema bound) ⟨0, Nat.zero_lt_one⟩

def batchesAt {schema : Scan.Schema String Kind} (trace : Arrow.Events.Trace schema Cell Events.Error)
    (column : Fin schema.width) : List (Arrow.TimestampBatch.Column (bindingAt schema column)) :=
  trace.batches.map fun batch => batch.values column

/-- Source failures retain their original cause and preclude destination emission.
Each successful event batch contributes one record, including a zero-row batch. -/
def emit (limits : Arrow.ObservationLimits) (source : Source) : Except Error KBytes :=
  match source with
  | .error cause => .error (.source cause)
  | .ok ⟨schema, trace⟩ =>
    match trace.termination with
    | .readError cause | .closeError cause => .error (.source cause)
    | .closed => .error .closed
    | .eos =>
      if one : schema.width = 1 then
        let column : Fin schema.width := ⟨0, by omega⟩
        (Arrow.TimestampStream.Writer.emit limits (bindingAt schema column) (batchesAt trace column)).mapError .writer
      else .error (.fieldCount schema.width)

/-- Pull the checked source once in footer order and emit only after EOS. -/
def convertGroupsUsing (opened : Except Error Leaf.Bound) (outputLimits : Arrow.ObservationLimits)
    (read : (bound : Leaf.Bound) → Nat → Except Leaf.Error (Leaf.Slots bound)) : Except Error KBytes := do
  let bound ← opened
  emit outputLimits (Events.readBoundWith bound (read bound))

/-- Bind the checked source once, then run the selected group reader. -/
def convertGroups (profile : AnnotationProfile) (inputLimits : Limits)
    (outputLimits : Arrow.ObservationLimits) (input : Bytes) (ordinal : Nat)
    (read : (bound : Leaf.Bound) → Nat → Except Leaf.Error (Leaf.Slots bound)) : Except Error KBytes :=
  convertGroupsUsing (openBoundWith profile inputLimits input ordinal) outputLimits read

/-- Select the serialized footer leaf ordinal and read its PLAIN data pages. -/
def convertWith (profile : AnnotationProfile) (inputLimits : Limits) (outputLimits : Arrow.ObservationLimits)
    (input : Bytes) (ordinal : Nat) : Except Error KBytes :=
  convertGroups profile inputLimits outputLimits input ordinal (Leaf.readGroup inputLimits.leaf)

/-- Convert a TIMESTAMP leaf with a modern logical annotation. -/
def convert (inputLimits : Limits) (outputLimits : Arrow.ObservationLimits)
    (input : Bytes) (ordinal : Nat) : Except Error KBytes :=
  convertWith .modernOnly inputLimits outputLimits input ordinal

end Silmaril.Formats.Parquet.Timestamp.Leaf.Events.ToIpc
