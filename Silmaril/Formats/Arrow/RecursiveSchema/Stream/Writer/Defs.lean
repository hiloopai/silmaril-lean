module

public import Silmaril.Formats.Arrow.RecursiveSchema.Writer.Defs
public import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Writer.Defs

/-! Native V5 streams for the recursive signed integer, Struct and List
profile, with checked schema, ordered batches and one exact modern EOS. -/

namespace Silmaril.Formats.Arrow.RecursiveSchema.Stream.Writer

@[expose] public section

abbrev Observation := Batch.Rows.Observation

inductive Error where
  | batchLimit (actual limit : Nat)
  | schema (original : RecursiveSchema.Writer.Error)
  | batch (ordinal : Nat) (original : Batch.Writer.Error)
  | readback (original : Stream.Error)
  | readbackMismatch
  deriving DecidableEq, Repr

def writeRecords (limits : Batch.Limits) (schema : Schema) :
    Nat → List Observation → Except (Nat × Batch.Writer.Error) (List KBytes)
  | _, [] => .ok []
  | ordinal, batch :: batches =>
    match Batch.Writer.serialize limits schema batch with
    | .error cause => .error (ordinal, cause)
    | .ok frame => (writeRecords limits schema (ordinal + 1) batches).map (frame :: ·)

def assemble (schemaFrame : KBytes) (frames : List KBytes) : KBytes :=
  schemaFrame ++ frames.foldr (· ++ ·) StreamWriter.eos

/-- Reject an excessive batch count before asking either writer to build
bytes. Each RecordBatch keeps its own explicit logical row count. -/
def serialize (limits : Batch.Limits) (schema : Schema) (batches : List Observation) :
    Except Error KBytes :=
  if batches.length > limits.schema.ipc.batches then
    .error (.batchLimit batches.length limits.schema.ipc.batches)
  else do
    let header ← (RecursiveSchema.Writer.serializeFrame limits.schema schema).mapError .schema
    let records ← (writeRecords limits schema 0 batches).mapError fun (index, cause) => .batch index cause
    return assemble header records

def agrees (depth : Nat) (schema : Schema) (batches : List Observation) (trace : Stream.Trace) :
    Bool :=
  RecursiveSchema.Writer.equalFields (RecursiveSchema.Writer.equalField depth)
    schema.fields trace.schema.fields &&
    batches.isEqv (trace.batches.map Completed.observed) (Batch.Writer.agrees depth)

/-- Certify the assembled carrier with one strict native stream read. The
individual schema and batch logical readback checks need not be repeated. -/
def emit (limits : Batch.Limits) (schema : Schema) (batches : List Observation) :
    Except Error KBytes := do
  let wire ← serialize limits schema batches
  let trace ← (Stream.read limits wire).mapError .readback
  if agrees limits.schema.depth schema batches trace then .ok wire
  else .error .readbackMismatch

def RecordsWire (limits : Batch.Limits) (schema : Schema) :
    List Observation → List KBytes → Prop :=
  List.Forall₂ fun batch frame => Batch.Writer.serialize limits schema batch = .ok frame

/-- The reached error uses the original ordinal and the batch writer's
own typed cause. Every earlier observation has a complete serialized frame. -/
structure RecordFailure (limits : Batch.Limits) (schema : Schema) (start : Nat)
    (batches : List Observation) (ordinal : Nat) (cause : Batch.Writer.Error) : Prop where
  failure : ∃ earlier batch later frames,
    batches = earlier ++ batch :: later ∧
    ordinal = start + earlier.length ∧ RecordsWire limits schema earlier frames ∧
    Batch.Writer.serialize limits schema batch = .error cause

/-- Construction binds the exact bodyless native header and all ordered
batch frames to their original writer calls. -/
structure Construction (limits : Batch.Limits) (schema : Schema) (batches : List Observation)
    (wire : KBytes) : Prop where
  batchLimit : batches.length ≤ limits.schema.ipc.batches
  pieces : ∃ budget records,
    RecursiveSchema.Writer.plan limits.schema schema = .ok budget ∧
    budget.bytes = (RecursiveSchema.Writer.Wire.metadata schema).len ∧
    budget.bytes < 2^31 ∧ budget.bytes ≤ limits.schema.ipc.metadataBytes ∧
    RecordsWire limits schema batches records ∧
    wire = assemble (StreamWriter.envelopeBytes budget.bytes ++
      RecursiveSchema.Writer.Wire.metadata schema) records

/-- A successful runtime certificate binds the exact original schema and
logical batches to the strict cursor chain, including the final EOS byte. -/
structure Readback (limits : Batch.Limits) (schema : Schema) (batches : List Observation)
    (wire : KBytes) : Prop where
  result : ∃ trace offset,
    Stream.read limits wire = .ok trace ∧ Stream.TraceWire limits wire trace ∧
    trace.schema = schema ∧ trace.batches.map Completed.observed = batches ∧
    trace.terminal = .eos batches.length offset ∧
    EnvelopeWire limits.schema.ipc wire.toList offset .eos ∧ offset + 8 = wire.len

end

end Silmaril.Formats.Arrow.RecursiveSchema.Stream.Writer
