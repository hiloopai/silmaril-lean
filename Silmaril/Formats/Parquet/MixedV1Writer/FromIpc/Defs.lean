module

public import Silmaril.Formats.Parquet.MixedV1Writer.Multi.Defs
public import Silmaril.Formats.Relational.NamedTable.MixedIpc.Defs

/-! Checked native Arrow IPC V5 to one mixed Parquet row group per RecordBatch. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.MixedV1Writer.FromIpc

open Silmaril.Formats.Relational.NamedTable
open Int32ByteArrayGroup (Field Row)

inductive PlanError where
  | fieldOrder
  | noBatches
  | requiredNull (group : Nat) (column : Int32ByteArrayGroup.Selection)
  deriving DecidableEq, Repr

inductive Error where
  | source (cause : MixedIpc.Error)
  | plan (cause : PlanError)
  | sink (cause : Multi.Error)
  deriving DecidableEq, Repr

def field (label : MixedIpc.Label) : Field :=
  ⟨label.1, if label.2 then .optional else .required⟩

def toRow (pair : MixedIpc.Pair) : Row :=
  (pair.1, pair.2.map Bytes.ofList)

def prepareInt (nullable : Bool) (ordinal : Nat) (slots : List (Option Int32)) :
    Except PlanError PlainV1Writer.Input :=
  if nullable then .ok (.optional slots)
  else match slots.mapM id with
  | some values => .ok (.required values)
  | none => .error (.requiredNull ordinal .int32)

def prepareBytes (nullable : Bool) (ordinal : Nat) (slots : List (Option Bytes)) :
    Except PlanError PlainByteArrayV1Writer.Input :=
  if nullable then .ok (.optional slots)
  else match slots.mapM id with
  | some values => .ok (.required values)
  | none => .error (.requiredNull ordinal .byteArray)

def prepareGroup (descriptor : MixedIpc.Descriptor) (ordinal : Nat) (pairs : List MixedIpc.Pair) :
    Except PlanError Multi.Group := do
  let integers ← prepareInt descriptor.integer.2 ordinal (pairs.map Prod.fst)
  let octets ← prepareBytes descriptor.binary.2 ordinal (pairs.map fun pair => pair.2.map Bytes.ofList)
  return ⟨integers, octets⟩

def prepareGroups (descriptor : MixedIpc.Descriptor) :
    Nat → List (List MixedIpc.Pair) → Except PlanError (List Multi.Group)
  | _, [] => .ok []
  | ordinal, pairs :: rest => do
    let group ← prepareGroup descriptor ordinal pairs
    let groups ← prepareGroups descriptor (ordinal + 1) rest
    return group :: groups

def physicalOrder (descriptor : MixedIpc.Descriptor) : Order :=
  if descriptor.viewFirst then .byteFirst else .intFirst

/-- Retain every record boundary. A schema-only stream has no group to write.
An explicit zero-row RecordBatch has one. -/
def prepareOrdered (source : MixedIpc.Prepared) : Except PlanError Multi.Input :=
  if source.batches = [] then .error .noBatches
  else (prepareGroups source.descriptor 0 source.batches).map fun groups =>
    ⟨field source.descriptor.integer, field source.descriptor.binary, groups⟩

/-- The original entry point admits INT32-first streams. -/
def prepare (source : MixedIpc.Prepared) : Except PlanError Multi.Input :=
  if source.descriptor.viewFirst then .error .fieldOrder else prepareOrdered source

/-- Plan and emit a nonempty record list from a checked IPC observation. -/
def emitOrderedPrepared (sink : Multi.Limits) (observed : MixedIpc.Prepared) :
    Except Error Multi.Encoded := do
  let plan ← (prepareOrdered observed).mapError .plan
  (Multi.emitOrdered (physicalOrder observed.descriptor) sink plan).mapError .sink

/-- Exhaust native IPC and emit the two Parquet leaves in descriptor order. -/
def convertOrdered (source : MixedIpc.Limits) (sink : Multi.Limits) (input : KBytes) :
    Except Error Multi.Encoded := do
  let observed ← (MixedIpc.read source input).mapError .source
  emitOrderedPrepared sink observed

/-- Finish exact native IPC exhaustion before planning or invoking the sink.
Only a complete, checked Parquet file is returned. -/
def convert (source : MixedIpc.Limits) (sink : Multi.Limits) (input : KBytes) :
    Except Error Multi.Encoded := do
  let observed ← (MixedIpc.read source input).mapError .source
  let plan ← (prepare observed).mapError .plan
  (Multi.emit sink plan).mapError .sink

end Silmaril.Formats.Parquet.MixedV1Writer.FromIpc
