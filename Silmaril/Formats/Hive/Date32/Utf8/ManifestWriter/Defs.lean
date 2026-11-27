module

public import Silmaril.Formats.Hive.Date32.Utf8.Render.Defs
public import Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups.Defs
public import Silmaril.Formats.Parquet.MixedV1Writer.Multi.Defs
import Mathlib.Data.List.OfFn

/-! A bounded native Hive manifest with two physical leaves and DATE/UTF-8 keys. -/

@[expose] public section

namespace Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter

open Silmaril.Relational Silmaril.Formats.Arrow Silmaril.Formats.Parquet
open Int32ByteArrayGroup.File (Kind Value)
open WritePlan.FlatInt32 (filePath filename)
open WritePlan.FlatInt32.RowGroups (Policy CutError planCuts splitSlots)

structure Schema where
  intName : String
  byteName : String
  keys : Keys

def Schema.intField (schema : Schema) : Int32ByteArrayGroup.Field := ⟨schema.intName, .optional⟩
def Schema.byteField (schema : Schema) : Int32ByteArrayGroup.Field := ⟨schema.byteName, .optional⟩

def Schema.physical (schema : Schema) : Scan.Schema String Kind :=
  Int32ByteArrayGroup.File.schema schema.intField schema.byteField

def Schema.toScan (schema : Schema) : Scan.Schema String Kind := schema.keys.schema.extend schema.physical

structure Limits where
  cuts : Policy
  writer : MixedV1Writer.Multi.Limits

def Limits.reader (limits : Limits) : Int32ByteArrayGroup.File.Limits :=
  ⟨limits.writer.writer.readback, limits.cuts.maxRowsPerFile⟩

structure File where
  path : String
  groupRows : List Nat
  bytes : Bytes

abbrev Bucket (schema : Schema) := WritePlan.Bucket schema.physical Value

abbrev ReadError := Manifest.FileError (Manifest.Int32ByteArray.Error Unit)

inductive Error where
  | missingName
  | schemaMismatch
  | physicalKeys (cause : PartitionPath.Error)
  | routing (cause : WritePlan.Error EncodeError)
  | policy (cause : CutError)
  | path (path : String) (cause : Manifest.PathError)
  | pathMismatch (path : String)
  | cuts (path : String) (cause : CutError)
  | parquet (path : String) (cause : MixedV1Writer.Multi.Error)
  | reference (cause : WritePlan.RestoreError Date32.Error)
  | ingress (cause : Manifest.PrepareError Date32.Error)
  | source (cause : Events.Termination ReadError)
  | groupCounts
  | values

variable {Name : Type*}

/-- Match the ordered names and types of the actual packed named table. -/
def namedRows (db : Silmaril.Formats.Relational.NamedTable.Packed Name String Value) (name : Name)
    (schema : Schema) : Except Error (Scan.Table schema.toScan Value) :=
  match Scan.observePacked db name with
  | none => .error .missingName
  | some stored =>
    if same : List.ofFn schema.toScan.kind = List.ofFn stored.schema.kind then
      have equal : stored.schema = schema.toScan := by
        generalize schema.toScan = expected at same ⊢
        generalize stored.schema = actual at same ⊢
        rcases actual with ⟨width, labels⟩
        rcases expected with ⟨width', labels'⟩
        have widths : width' = width := by simpa using congrArg List.length same
        subst width'
        exact congrArg (PositionalSchema.mk width) (List.ofFn_injective same.symm)
      .ok (equal ▸ stored.rows)
    else .error .schemaMismatch

/-- Take consecutive cuts of the routed physical rows. Both columns use the
same row list for each group, including its nullable and opaque slots. -/
def fileInput (schema : Schema) (sizes : List Nat)
    (rows : Scan.Table schema.physical Value) : MixedV1Writer.Multi.Input :=
  ⟨schema.intField, schema.byteField, (splitSlots sizes rows).map fun group =>
    ⟨.optional (group.map fun row => row (0 : Fin 2)),
      .optional (group.map fun row => row (1 : Fin 2))⟩⟩

/-- The literal path and consecutive cuts for one routed bucket, with native
emission from that exact physical input. -/
structure FileMatches (schema : Schema) (limits : Limits) (bucket : Bucket schema) (file : File) : Prop where
  path : file.path = filePath bucket.directory
  split : Manifest.splitFile file.path = .ok (bucket.directory, filename)
  planned : planCuts limits.cuts bucket.rows.length = .ok file.groupRows
  encoded : ∃ output, MixedV1Writer.Multi.emit limits.writer (fileInput schema file.groupRows bucket.rows) = .ok output ∧
    file.bytes = output.bytes

def emitBucket (schema : Schema) (limits : Limits) (bucket : Bucket schema) : Except Error File := do
  let path := filePath bucket.directory
  let split ← (Manifest.splitFile path).mapError (.path path)
  if split ≠ (bucket.directory, filename) then throw (.pathMismatch path)
  let sizes ← (planCuts limits.cuts bucket.rows.length).mapError (.cuts path)
  let output ← (MixedV1Writer.Multi.emit limits.writer (fileInput schema sizes bucket.rows)).mapError (.parquet path)
  return ⟨path, sizes, output.bytes⟩

/-- Reopen the returned bytes by exact literal path through the existing
paired ingress, with the full typed schema and no row filter. -/
def readManifest (schema : Schema) (options : PartitionPath.Options) (limits : Limits) (files : List File) :
    Except (Manifest.PrepareError Date32.Error) (Events.Trace schema.toScan Value ReadError) :=
  scanPaths (int32 := schema.intField) (byteArray := schema.byteField) (keys := schema.keys) options limits.reader
    (fun path => match files.find? (fun file => file.path == path) with
      | none => .error ()
      | some file => .ok file.bytes)
    ⟨schema.toScan.width, id⟩ (fun _ => some true) (files.map (·.path))

/-- Check the actual ordered readback against the restored route plan.
The comparison checks the typed rows and each actual group boundary. -/
def certify (schema : Schema) (options : PartitionPath.Options) (limits : Limits)
    (buckets : List (Bucket schema)) (files : List File) : Except Error Unit := do
  let expected ← (WritePlan.restore schema.physical schema.keys.schema options convert buckets).mapError .reference
  let trace ← (readManifest schema options limits files).mapError .ingress
  if trace.termination ≠ .eos then throw (.source trace.termination)
  if trace.batches.map (·.rowCount) ≠ files.flatMap (·.groupRows) then throw .groupCounts
  let decideCell (kind : Kind) : DecidableEq (Option (Value kind)) := by cases kind <;> infer_instance
  let decideRow : DecidableEq (Scan.Row schema.toScan Value) := fun left right =>
    letI (i : Fin schema.toScan.width) : Decidable (left i = right i) :=
      decideCell (schema.toScan.kind i).2 (left i) (right i)
    decidable_of_iff (∀ i, left i = right i) funext_iff.symm
  letI : Decidable (trace.rows = expected) := @List.hasDecEq _ decideRow trace.rows expected
  if trace.rows = expected then pure () else throw .values

/-- Route all admitted rows before emitting files. A returned manifest has
passed the strict paired reader against the route plan. -/
def emit (db : Silmaril.Formats.Relational.NamedTable.Packed Name String Value) (name : Name)
    (schema : Schema) (options : PartitionPath.Options) (limits : Limits) : Except Error (List File) := do
  let rows ← namedRows db name schema
  (PartitionPath.validateKeys [schema.intName, schema.byteName]).mapError .physicalKeys
  let buckets ← (WritePlan.plan schema.physical schema.keys.schema options encode rows).mapError .routing
  if limits.cuts.rowsPerGroup = 0 then throw (.policy .zeroRowsPerGroup)
  let files ← buckets.mapM (emitBucket schema limits)
  certify schema options limits buckets files
  return files

end Silmaril.Formats.Hive.Date32.Utf8.ManifestWriter
