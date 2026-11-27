module

public import Silmaril.Formats.Hive.WritePlan.FlatInt32.Defs
public import Silmaril.Formats.Parquet.FlatInt32Writer.RowGroups.Defs
public import Silmaril.Formats.Parquet.Footer.ColumnOrder.Defs

/-! Bounded deterministic row groups for native INT32 Hive manifests. -/

@[expose] public section

namespace Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups

open Silmaril.Relational Silmaril.Formats.Parquet
open TypedPartitions (PartitionSchema Convert TypedPartition)
open Snapshot.FlatInt32 (Cell)

structure Policy where
  rowsPerGroup : Nat
  maxGroupsPerFile : Nat
  maxRowsPerFile : Nat

inductive CutError where
  | zeroRowsPerGroup
  | rowLimit (rows : Nat)
  | groupLimit
  deriving DecidableEq, Repr

/-- Take consecutive full groups and then the final short group. Fuel is the
available group budget. No group is emitted for an empty suffix. -/
def cuts (width : Nat) : Nat → Nat → List Nat
  | 0, _ => []
  | _ + 1, 0 => []
  | fuel + 1, rows + 1 => min width (rows + 1) :: cuts width fuel (rows + 1 - width)

def planCuts (policy : Policy) (rows : Nat) : Except CutError (List Nat) :=
  if policy.rowsPerGroup = 0 then .error .zeroRowsPerGroup
  else if rows > policy.maxRowsPerFile then .error (.rowLimit rows)
  else
    let sizes := cuts policy.rowsPerGroup policy.maxGroupsPerFile rows
    if sizes.sum = rows then .ok sizes else .error .groupLimit

/-- Split a slot list at the admitted sizes without reordering any slots. -/
def splitSlots {α : Type*} : List Nat → List α → List (List α)
  | [], _ => []
  | size :: sizes, rows => rows.take size :: splitSlots sizes (rows.drop size)

structure File where
  path : String
  rowCount : Nat
  groupRows : List Nat
  bytes : Bytes

abbrev Slots := List (List (Option Int32))

inductive PayloadError where
  | cuts (reason : CutError)
  | dimensions
  | fileLimit
  | wireSchema
  | schemaFields (reason : Footer.ColumnOrder.Error)
  | parquet (reason : SnapshotError)
  deriving DecidableEq, Repr

inductive EmitError (Failure : Type*) where
  | source (reason : FlatInt32.EmitError Failure)
  | policy (reason : CutError)
  | cuts (path : String) (reason : CutError)
  | parquet (path : String) (reason : FlatInt32Writer.RowGroups.Error)
  | readback (path : String) (reason : PayloadError)
  | values (path : String)
  deriving BEq, Repr

inductive FileError (Failure : Type*) where
  | path (reason : FlatInt32.ReadError Failure)
  | partition (reason : RestoreError Failure)
  | payload (reason : PayloadError)
  deriving BEq

inductive ReadError (Failure : Type*) where
  | schema (reason : TypedPartitions.Error Failure)
  | policy (reason : CutError)
  | file (index : Nat) (path : String) (reason : FileError Failure)
  deriving BEq

/-- Check dimensions and the exact optional, unannotated INT32 wire schema
before decoding any row group. -/
def openPayload (policy : Policy) (limits : FlatInt32Writer.Limits) (leaf : String) (file : File) :
    Except PayloadError Snapshot.Checked := do
  let sizes ← (planCuts policy file.rowCount).mapError .cuts
  if sizes.isEmpty || file.groupRows ≠ sizes then throw .dimensions
  if file.bytes.length > FlatInt32Writer.RowGroups.fileLimit limits then throw .fileLimit
  let snapshot ← (Snapshot.check (Failure := Snapshot.FlatInt32.Error Unit) ⟨limits.footer, 2⟩ file.bytes).mapError .parquet
  let expected := [FlatInt32Writer.Compact.schemaRoot 1,
    (⟨leaf, true, ⟨0, 0⟩⟩ : FlatInt32Writer.Compact.ColumnIndex).schema]
  if snapshot.metadata.schema ≠ expected then throw .wireSchema
  let raw ← (Footer.ColumnOrder.readSelection limits.footer snapshot 0).mapError .schemaFields
  if raw.leaf.item.fields.any (fun field => field.id == 6 || field.id == 10) then throw .wireSchema
  if snapshot.metadata.numRows ≠ Int.ofNat file.rowCount ∨
      snapshot.metadata.rowGroups.map Footer.RowGroup.numRows ≠ sizes.map Int.ofNat then throw .dimensions
  return snapshot

/-- The checked footer and strict INT32 binding supply the original indexed source. -/
def openGroupSource (policy : Policy) (limits : FlatInt32Writer.Limits) (leaf : String) (file : File) :
    Except PayloadError (Reader.Source Nat (physical leaf) Cell SnapshotError) := do
  let snapshot ← openPayload policy limits leaf file
  let readerLimits := readLimits limits policy.rowsPerGroup
  let decode ← (Snapshot.FlatInt32.bind (InputFailure := Unit) readerLimits
    (physical leaf) snapshot.metadata).mapError (PayloadError.parquet ∘ Snapshot.Error.schema)
  return snapshot.source decode

def physicalSlots {leaf : String} (rows : Scan.Table (physical leaf) Cell) : List (Option Int32) :=
  rows.map fun row => row (0 : Fin 1)

def readSlots {leaf : String} (source : Reader.Source Nat (physical leaf) Cell SnapshotError)
    (index : Nat) : Except PayloadError (List (Option Int32)) :=
  ((source.readGroup index).map physicalSlots).mapError .parquet

/-- Visit every checked footer ordinal in order. The snapshot decoder's
indexed errors survive, including a failure after earlier successful groups. -/
def readPayload (policy : Policy) (limits : FlatInt32Writer.Limits) (leaf : String) (file : File) :
    Except PayloadError Slots := do
  let source ← openGroupSource policy limits leaf file
  source.groups.mapM (readSlots source)

/-- The literal path, admitted cut vector, and all actual decoded groups for
one emitted occurrence. -/
structure FileMatches (policy : Policy) (limits : FlatInt32Writer.Limits) (leaf : String)
    (bucket : Bucket (physical leaf) Cell) (file : File) : Prop where
  path : file.path = filePath bucket.directory
  split : Manifest.splitFile file.path = .ok (bucket.directory, filename)
  count : file.rowCount = bucket.rows.length
  planned : planCuts policy bucket.rows.length = .ok file.groupRows
  read : readPayload policy limits leaf file = .ok (splitSlots file.groupRows (physicalSlots bucket.rows))

/-- Return only a certified file, using the same bounded reader as restore. -/
def emitBucket {Failure : Type*} (policy : Policy) (limits : FlatInt32Writer.Limits) (leaf : String)
    (bucket : Bucket (physical leaf) Cell) : Except (EmitError Failure) File := do
  let path := filePath bucket.directory
  let split ← (Manifest.splitFile path).mapError (EmitError.source ∘ FlatInt32.EmitError.path path)
  if split ≠ (bucket.directory, filename) then throw (.source (.pathMismatch path))
  let sizes ← (planCuts policy bucket.rows.length).mapError (.cuts path)
  let groups := splitSlots sizes (physicalSlots bucket.rows)
  let bytes ← (FlatInt32Writer.RowGroups.assemble limits leaf groups).mapError (.parquet path)
  let file := ⟨path, bucket.rows.length, sizes, bytes⟩
  let observed ← (readPayload policy limits leaf file).mapError (.readback path)
  if observed = groups then return file else throw (.values path)

/-- Route in first-seen directory order before checking the cut policy and
emitting any files. The empty successful plan yields an empty manifest. -/
def emit {Name Failure : Type*} (db : Database Name) (name : Name) (leaf : String)
    (schema : PartitionSchema Unit) (options : PartitionPath.Options) (encode : Encode Cell Failure)
    (policy : Policy) (limits : FlatInt32Writer.Limits) : Except (EmitError Failure) (List File) := do
  let rows ← (namedRows db name (schema.extend (physical leaf))).mapError .source
  let buckets ← (WritePlan.plan (physical leaf) schema options encode rows).mapError (.source ∘ .routing)
  if policy.rowsPerGroup = 0 then throw (.policy .zeroRowsPerGroup)
  buckets.mapM (emitBucket policy limits leaf)

/-- Check the literal path and bind the typed directory before pruning. -/
def bindFileCells {Failure : Type*} (schema : PartitionSchema Unit) (options : PartitionPath.Options)
    (decode : Convert Cell Failure) (file : File) : Except (FileError Failure) (Scan.Row schema.toScan Cell) := do
  let directory ← (checkFilePath file.path).mapError .path
  (decodeDirectory schema options decode directory).mapError .partition

/-- Bind the path before evaluating the partition predicate. A rejected
occurrence supplies zero rows and its payload is never opened. -/
def readPart {Failure : Type*} (leaf : String) (schema : PartitionSchema Unit)
    (options : PartitionPath.Options) (decode : Convert Cell Failure) (policy : Policy)
    (limits : FlatInt32Writer.Limits) (predicate : Scan.Predicate schema.toScan Cell) (entry : File × Nat) :
    Except (ReadError Failure) (TypedPartition (physical leaf) schema Cell) :=
  let (file, index) := entry
  let read : Except (FileError Failure) _ := do
    let cells ← bindFileCells schema options decode file
    if (predicate cells).getD false then
      let slots ← (readPayload policy limits leaf file).mapError .payload
      return ⟨cells, slots.flatten.map fun cell _ => cell⟩
    else return ⟨cells, []⟩
  read.mapError (.file index file.path)

def checkRead {Failure : Type*} (leaf : String) (schema : PartitionSchema Unit)
    (policy : Policy) : Except (ReadError Failure) Unit :=
  match TypedPartitions.checkSchema (physical leaf) schema with
  | .error reason => .error (.schema reason)
  | .ok () => if policy.rowsPerGroup = 0 then .error (.policy .zeroRowsPerGroup) else .ok ()

/-- Validate schema and cut width before the manifest. Validate each path
before testing its typed value. False and unknown skip the file payload.
Return the original occurrence and indexed snapshot cause on failure. -/
def restorePruned {Failure : Type*} (leaf : String) (schema : PartitionSchema Unit)
    (options : PartitionPath.Options) (decode : Convert Cell Failure) (policy : Policy)
    (limits : FlatInt32Writer.Limits) (predicate : Scan.Predicate schema.toScan Cell) (files : List File) :
    Except (ReadError Failure) (Scan.Table (schema.extend (physical leaf)) Cell) := do
  checkRead leaf schema policy
  (files.zipIdx.mapM (readPart leaf schema options decode policy limits predicate)).map TypedPartitions.materialize

/-- Read every manifest occurrence under the same bounded row-group policy. -/
def restore {Failure : Type*} (leaf : String) (schema : PartitionSchema Unit)
    (options : PartitionPath.Options) (decode : Convert Cell Failure) (policy : Policy)
    (limits : FlatInt32Writer.Limits) (files : List File) :
    Except (ReadError Failure) (Scan.Table (schema.extend (physical leaf)) Cell) :=
  restorePruned leaf schema options decode policy limits (fun _ => some true) files

end Silmaril.Formats.Hive.WritePlan.FlatInt32.RowGroups
