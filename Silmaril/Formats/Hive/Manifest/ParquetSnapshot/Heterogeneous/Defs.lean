module

public import Silmaril.Formats.Hive.Manifest.ParquetSnapshot.Int32ByteArray.Ingress.Defs
public import Silmaril.Formats.Parquet.FlatProjection.Events.Defs
import Mathlib.Data.List.OfFn

/-! A supplied ordered Hive manifest over the checked heterogeneous Parquet Events profile. -/

@[expose] public section

namespace Silmaril.Formats.Hive.Manifest.Heterogeneous

open Silmaril.Relational
open Parquet.FlatProjection.Events (Kind Cell)
open TypedPartitions (PartitionSchema)

structure PhysicalField where
  ordinal : Nat
  name : String
  kind : Kind

/-- Declare one fixed physical schema in selected order and one virtual schema. -/
structure Schema where
  fields : Array PhysicalField
  partitions : PartitionSchema Kind

abbrev Schema.physical (schema : Schema) : Scan.Schema String Kind :=
  ⟨schema.fields.size, fun i => (schema.fields[i].name, schema.fields[i].kind)⟩

abbrev Schema.output (schema : Schema) : Scan.Schema String Kind :=
  schema.partitions.extend schema.physical

def Schema.ordinals (schema : Schema) : Array Nat := schema.fields.map PhysicalField.ordinal

structure Entry where
  path : String
  bytes : Bytes

inductive CastError where
  | int32 (cause : Int32ByteArray.Ingress.CastError)
  | unsupportedTimestamp
  deriving BEq, Repr

inductive FileError where
  | path (cause : PrepareError CastError)
  | requiredNull (field : String)
  | openParquet (cause : Parquet.FlatProjection.Events.Error)
  | nonFlatSchema
  | reservedPartition (name : String)
  | physicalSchema
  | readParquet (cause : Parquet.FlatProjection.Events.Error)
  deriving Repr

inductive Error where
  | schema (cause : TypedPartitions.Error CastError)
  | unsupportedPartition (name : String)
  | file (index : Nat) (path : String) (cause : FileError)
  deriving Repr

def convertCell : TypedPartitions.Convert Cell CastError := fun field text =>
  match field.kind with
  | .int32 nullable =>
    let layout : Parquet.FlatColumn.Layout := if nullable then .optional else .required
    (Int32ByteArray.Ingress.convert ⟨field.name, .int32 layout, field.missing⟩ text).mapError .int32
  | .utf8 _ => .ok text
  | .timestamp _ => .error .unsupportedTimestamp

def nullable : Kind → Bool
  | .int32 nullable | .utf8 nullable => nullable
  | .timestamp kind => kind.nullable

def checkSchema (schema : Schema) : Except Error Unit := do
  (TypedPartitions.checkSchema schema.physical schema.partitions).mapError .schema
  if let some field := schema.partitions.fields.toList.find? (fun field =>
    match field.kind with | .timestamp _ => true | _ => false) then
    throw (.unsupportedPartition field.name)

def prepareFile (partitions : PartitionSchema Kind) (options : PartitionPath.Options) (path : String) :
    Except FileError (File partitions Cell) := do
  let file ← (Manifest.prepareFile partitions options convertCell path).mapError .path
  if let some position := (List.finRange partitions.toScan.width).find? (fun i =>
      !nullable (partitions.toScan.kind i).2 && (file.cells i).isNone) then
    throw (.requiredNull (partitions.toScan.kind position).1)
  return file

def labels (schema : Scan.Schema String Kind) : List (String × Kind) := List.ofFn schema.kind

theorem schema_eq_of_labels {left right : Scan.Schema String Kind} (same : labels left = labels right) :
    left = right :=
  congrArg (fun p : Σ n, Fin n → String × Kind => (⟨p.1, p.2⟩ : Scan.Schema String Kind))
    (List.ofFn_inj'.mp same)

structure BoundFile (schema : Schema) where
  partition : File schema.partitions Cell
  physical : Parquet.FlatProjection.Events.Checked
  schemaExact : physical.schema = schema.physical

/-- Bind the literal path first, then open the supplied bytes once. Check
reserved names across every original leaf, including unselected leaves. -/
def bindFile (schema : Schema) (options : PartitionPath.Options)
    (limits : Parquet.FlatProjection.Events.Limits) (entry : Entry) : Except FileError (BoundFile schema) := do
  let partition ← prepareFile schema.partitions options entry.path
  let checked ← (Parquet.FlatProjection.Events.openFile limits entry.bytes schema.ordinals).mapError .openParquet
  let root :: leaves := checked.snapshot.metadata.schema | throw .nonFlatSchema
  if !Parquet.Footer.ColumnOrder.isFlat root leaves then throw .nonFlatSchema
  if let some leaf := leaves.find? (fun leaf => schema.partitions.keys.contains leaf.name) then
    throw (.reservedPartition leaf.name)
  if exact : labels checked.schema = labels schema.physical then
    return ⟨partition, checked, schema_eq_of_labels exact⟩
  else throw .physicalSchema

abbrev PhysicalTrace (schema : Schema) := Arrow.Events.Trace schema.physical Cell Parquet.FlatProjection.Events.Error
abbrev Trace (schema : Schema) := Arrow.Events.Trace schema.output Cell Error

def atFile (entry : Entry × Nat) :
    Arrow.Events.Termination Parquet.FlatProjection.Events.Error → Arrow.Events.Termination Error
  | .eos => .eos
  | .closed => .closed
  | .readError cause => .readError (.file entry.2 entry.1.path (.readParquet cause))
  | .closeError cause => .closeError (.file entry.2 entry.1.path (.readParquet cause))

def extend {schema : Schema} (entry : Entry × Nat) (cells : Scan.Row schema.partitions.toScan Cell)
    (physical : PhysicalTrace schema) : Trace schema :=
  ParquetScan.extendTrace ⟨physical.batches, atFile entry physical.termination⟩ cells

def BoundFile.trace {schema : Schema} (bound : BoundFile schema) (limits : Parquet.FlatProjection.Events.Limits) :
    PhysicalTrace schema :=
  cast (congrArg (fun physical => Arrow.Events.Trace physical Cell Parquet.FlatProjection.Events.Error)
    bound.schemaExact) (bound.physical.trace limits)

def readFile (schema : Schema) (options : PartitionPath.Options)
    (limits : Parquet.FlatProjection.Events.Limits) (entry : Entry × Nat) : Trace schema :=
  match bindFile schema options limits entry.1 with
  | .error cause => ⟨[], .readError (.file entry.2 entry.1.path cause)⟩
  | .ok bound => extend entry bound.partition.cells (bound.trace limits)

/-- An independent per-file observation names the direct typed read and its literal partition tuple. -/
def FileBatches (schema : Schema) (options : PartitionPath.Options) (limits : Parquet.FlatProjection.Events.Limits)
    (entry : Entry × Nat) (batches : List (Scan.Columns schema.output Cell)) : Prop :=
  ∃ (bound : BoundFile schema),
    Manifest.prepareFile schema.partitions options convertCell entry.1.path = .ok bound.partition ∧
    Parquet.FlatProjection.Events.readAll limits entry.1.bytes schema.ordinals =
      .ok ⟨bound.physical.schema, bound.physical.trace limits⟩ ∧
    (bound.physical.trace limits).termination = .eos ∧
    batches = (extend entry bound.partition.cells (bound.trace limits)).batches

def read (schema : Schema) (options : PartitionPath.Options)
    (limits : Parquet.FlatProjection.Events.Limits) (manifest : List Entry) : Except Error (Trace schema) :=
  (checkSchema schema).map fun _ => ParquetScan.assemble (readFile schema options limits) manifest.zipIdx

/-- The dataset declares its schema even when the supplied manifest is empty. -/
def readAll (schema : Schema) (options : PartitionPath.Options)
    (limits : Parquet.FlatProjection.Events.Limits) (manifest : List Entry) :
    Arrow.Events.EventStream String Cell Error :=
  (read schema options limits manifest).map fun trace => ⟨schema.output, trace⟩

/-- Logical projection of each reached file. Physical selections still follow
the declared schema, so projection also preserves errors in omitted columns. -/
def project (schema : Schema) (options : PartitionPath.Options)
    (limits : Parquet.FlatProjection.Events.Limits) (manifest : List Entry)
    (projection : Scan.Projection schema.output) :
    Except Error (Arrow.Events.Trace projection.schema Cell Error) :=
  (checkSchema schema).map fun _ =>
    ParquetScan.assemble (fun entry => (readFile schema options limits entry).scan projection (fun _ => some true))
      manifest.zipIdx

end Silmaril.Formats.Hive.Manifest.Heterogeneous
