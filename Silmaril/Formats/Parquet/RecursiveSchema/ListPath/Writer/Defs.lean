module

public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Reader.Events.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Writer.Schema.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.Defs
public import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Writer.Defs
import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Rows.Thms
import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Writer.Schema.Thms

/-! Bounded native Parquet for one signed leaf under a canonical LIST path.
Each group is one unindexed UNCOMPRESSED PLAIN V1 page of complete rows. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Writer

open Arrow.RecursiveSchema.Batch.Rows (Observation)
open Arrow.RecursiveSchema.Stream.Events (Signature declarations eraseBatch fieldName)
open Repeated.Writer
open Repeated.Chunk.Writer (encodeSection sectionSize wordOctets)

@[expose] public section

structure Limits where
  schema : Schema.Limits := {}
  chunk : Chunk.Limits := {}
  maxGroups : Nat := 1024
  maxTotalRows : Nat := 1024 * 1024
  maxTotalSlots : Nat := 4 * 1024 * 1024

structure Input where
  schema : Arrow.RecursiveSchema.Schema
  groups : List Observation
  checksum : Bool := false

inductive Error where
  | declaration
  | schema (cause : Schema.Error)
  | groupLimit (actual : Nat)
  | totalRowLimit (actual : Nat)
  | rowCount (group expected actual : Nat)
  | rowLimit (group actual : Nat)
  | pageLimit (group : Nat)
  | slotLimit (group actual : Nat)
  | totalSlotLimit (group actual : Nat)
  | levelLimit (group : Nat)
  | projection (group : Nat)
  | bodyLimit (group : Nat)
  | headerInteger (group : Nat)
  | headerLimit (group : Nat)
  | chunkLimit (group : Nat)
  | measureMismatch (group : Nat)
  | openReadback (cause : ListPath.Error)
  | events (cause : Reader.Events.Error)
  | readbackMismatch
  deriving DecidableEq, Repr

end

/-- Charge one physical node for a leaf and two for each LIST and its wrapper. -/
private def planField (nameBytes : Nat) :
    Nat → Nat → List String → Arrow.RecursiveSchema.Field → Except Error (List Schema.Entry)
  | 0, _, parent, _ => .error (.schema (.depth parent))
  | _ + 1, 0, _, _ => .error (.schema .fieldLimit)
  | depth + 1, fields + 1, parent, .node name nullable kind children => do
    let some name := name | throw .declaration
    let path := parent ++ [name]
    if name.utf8ByteSize > nameBytes then throw (.schema (.nameBudget path))
    match kind, children with
    | .list, [child] =>
      let nextDepth + 1 := depth | throw (.schema (.depth path))
      let nextFields + 1 := fields | throw (.schema .fieldLimit)
      let entries ← planField nameBytes nextDepth nextFields (path ++ ["list"]) child
      return .list name nullable :: .wrapper :: entries
    | .int32, [] => return [.leaf name nullable .int32]
    | .int64, [] => return [.leaf name nullable .int64]
    | _, _ => throw .declaration

public def planSchema (limits : Schema.Limits) (schema : Arrow.RecursiveSchema.Schema) :
    Except Error Schema.Plan := do
  let [field@(.node _ _ .list [_])] := schema.fields | throw .declaration
  let compact := limits.snapshot.footer.compact
  if "schema".utf8ByteSize > compact.maxBinaryBytes then throw (.schema (.nameBudget []))
  let entries ← planField compact.maxBinaryBytes (limits.snapshot.maxSchemaDepth - 1)
    (min limits.maxFields compact.maxCollectionSize - 1) [] field
  return ⟨1, entries⟩

@[expose] public section

def groupBudget (limits : Limits) : Nat :=
  min limits.maxGroups limits.schema.snapshot.footer.compact.maxCollectionSize

def totalRows (input : Input) : Nat := (input.groups.map (·.rowCount)).sum

def slotBudget (limits : Limits) : Nat :=
  min limits.chunk.maxSlots (min limits.chunk.levels.values (Hybrid.runLimit - 1))

def frameBudget (limits : Limits) (offset : Nat) : Nat :=
  min limits.chunk.maxChunkBytes (limits.schema.fileBytes - offset - 8)

def body (plan : Plan) (atoms : List Rows.Atom) : Bytes :=
  let reps := encodeSection plan.shape.repetitions (atoms.map (·.repetition))
  let defs := encodeSection plan.shape.definitions (atoms.map (·.definition))
  (reps.append defs).append (Plain.encodeWords wordOctets (atoms.filterMap (·.word)))

def pageHeader (checksum : Bool) (count : Nat) (body : Bytes) : Page.Header :=
  ⟨body.length, body.length, if checksum then some (Compression.Checksum.crc32.digest body.toList) else none,
    .dataV1 ⟨count, 0, 3, 3⟩⟩

structure WrittenGroup where
  offset : Nat
  rows : Nat
  slots : Nat
  page : PlainV1Writer.Encoded

def WrittenGroup.index (plan : Plan) (group : WrittenGroup) : Schema.GroupIndex :=
  let (leaf, kind) := plan.shape.leaf
  ⟨group.rows, [⟨kind, leaf.location.path, group.slots, group.offset, group.page.wire.length⟩]⟩

structure GroupWire (limits : Limits) (checksum : Bool) (plan : Plan) (offset priorSlots : Nat)
    (input : Observation) (output : WrittenGroup) : Prop where
  canonical : ∃ atoms, Rows.Relation plan atoms input.rows ∧ output.slots = atoms.length ∧
    output.page.body = body plan atoms
  atOffset : output.offset = offset
  rows : output.rows = input.rowCount
  rowCount : input.rowCount = input.rows.length
  header : output.page.header = pageHeader checksum output.slots output.page.body
  compact : PlainV1Writer.encodeHeaderWithChecksum output.slots output.page.body.length
    output.page.header.crc = some output.page.headerBytes
  pageCap : 1 ≤ limits.chunk.framing.maxPages
  rowCap : output.rows ≤ limits.chunk.maxRows
  slotCap : output.slots ≤ slotBudget limits
  totalSlotCap : priorSlots + output.slots ≤ limits.maxTotalSlots
  levelCap : max (sectionSize plan.shape.repetitions output.slots)
    (sectionSize plan.shape.definitions output.slots) ≤ 4 + limits.chunk.levels.bytes
  bodyCap : output.page.body.length < 2 ^ 31 ∧ output.page.body.length ≤ limits.chunk.maxBodyBytes
  headerCap : output.page.headerBytes.length ≤ limits.chunk.framing.maxHeaderBytes
  frameCap : output.page.wire.length ≤ frameBudget limits offset

inductive GroupsWire (limits : Limits) (checksum : Bool) (plan : Plan) :
    Nat → Nat → List Observation → List WrittenGroup → Prop where
  | nil (offset priorSlots : Nat) : GroupsWire limits checksum plan offset priorSlots [] []
  | cons {offset priorSlots input inputs output outputs} :
      GroupWire limits checksum plan offset priorSlots input output →
      GroupsWire limits checksum plan (offset + output.page.wire.length)
        (priorSlots + output.slots) inputs outputs →
      GroupsWire limits checksum plan offset priorSlots (input :: inputs) (output :: outputs)

end

private def require (condition : Prop) [Decidable condition] (error : Error) :
    Except Error (PLift condition) :=
  if accepted : condition then .ok ⟨accepted⟩ else .error error

private def checked {α ε : Type} (result : Except ε α) (report : ε → Error) :
    Except Error {value // result = .ok value} :=
  match result with
  | .ok value => .ok ⟨value, rfl⟩
  | .error cause => .error (report cause)

/-- Count and check a whole group before allocating its level or word bytes. -/
public def writeGroup (limits : Limits) (checksum : Bool) (plan : Plan) (ordinal offset priorSlots : Nat)
    (input : Observation) : Except Error {output // GroupWire limits checksum plan offset priorSlots input output} := do
  let ⟨rowCount⟩ ← require (input.rowCount = input.rows.length) (.rowCount ordinal input.rowCount input.rows.length)
  let ⟨rowCap⟩ ← require (input.rowCount ≤ limits.chunk.maxRows) (.rowLimit ordinal input.rowCount)
  let ⟨pageCap⟩ ← require (1 ≤ limits.chunk.framing.maxPages) (.pageLimit ordinal)
  let slots := Rows.slotDemand plan input.rows
  let ⟨slotCap⟩ ← require (slots ≤ slotBudget limits) (.slotLimit ordinal slots)
  let ⟨totalCap⟩ ← require (priorSlots + slots ≤ limits.maxTotalSlots) (.totalSlotLimit ordinal (priorSlots + slots))
  let reps := plan.shape.repetitions
  let defs := plan.shape.definitions
  let repSize := sectionSize reps slots
  let defSize := sectionSize defs slots
  if max (Repeated.Chunk.bitWidth reps) (Repeated.Chunk.bitWidth defs) > 32 then throw (.levelLimit ordinal)
  let ⟨levelCap⟩ ← require (max repSize defSize ≤ 4 + limits.chunk.levels.bytes) (.levelLimit ordinal)
  match projected : Rows.Projection.trace plan input.rows with
  | none => throw (.projection ordinal)
  | some atoms =>
    let words := atoms.countP (fun atom => atom.word.isSome)
    let size := repSize + defSize + words * RecursiveSchema.Chunk.wordWidth plan.shape.leaf.2
    let ⟨bodyCap⟩ ← require (size < 2 ^ 31 ∧ size ≤ limits.chunk.maxBodyBytes) (.bodyLimit ordinal)
    if size > frameBudget limits offset then throw (.bodyLimit ordinal)
    let payload := body plan atoms
    let ⟨measured⟩ ← require (payload.length = size) (.measureMismatch ordinal)
    let header := pageHeader checksum slots payload
    match encoded : PlainV1Writer.encodeHeaderWithChecksum slots payload.length header.crc with
    | none => throw (.headerInteger ordinal)
    | some headerBytes =>
      let ⟨headerCap⟩ ← require (headerBytes.length ≤ limits.chunk.framing.maxHeaderBytes) (.headerLimit ordinal)
      let page : PlainV1Writer.Encoded := ⟨header, headerBytes, payload⟩
      let ⟨frameCap⟩ ← require (page.wire.length ≤ frameBudget limits offset) (.chunkLimit ordinal)
      return ⟨⟨offset, input.rowCount, slots, page⟩, ⟨
        ⟨atoms, projected, Rows.Relation.slotDemand projected, rfl⟩, rfl, rfl, rowCount, rfl, encoded,
        pageCap, rowCap, slotCap, totalCap, levelCap, measured.symm ▸ bodyCap, headerCap, frameCap⟩⟩

private def pack (limits : Limits) (checksum : Bool) (plan : Plan) :
    (inputs : List Observation) → (ordinal offset priorSlots : Nat) →
      Except Error {outputs // GroupsWire limits checksum plan offset priorSlots inputs outputs}
  | [], _, offset, priorSlots => .ok ⟨[], .nil offset priorSlots⟩
  | input :: rest, ordinal, offset, priorSlots => do
    let ⟨group, wire⟩ ← writeGroup limits checksum plan ordinal offset priorSlots input
    let ⟨groups, tail⟩ ← pack limits checksum plan rest (ordinal + 1)
      (offset + group.page.wire.length) (priorSlots + group.slots)
    return ⟨group :: groups, .cons wire tail⟩

@[expose] public section

def payload (groups : List WrittenGroup) : Bytes :=
  groups.foldl (fun bytes group => bytes.append group.page.wire) .empty

structure Output where
  bytes : Bytes
  footer : Footer.Span
  metadata : Footer.Metadata

structure Construction (limits : Limits) (input : Input) (output : Output) : Prop where
  groupCap : input.groups.length ≤ groupBudget limits
  rowCap : totalRows input < 2 ^ 63 ∧ totalRows input ≤ limits.maxTotalRows
  original : ∃ declared schemaOnly source groups,
    planSchema limits.schema input.schema = .ok declared ∧
    Schema.wrap limits.schema .empty declared [] = .ok schemaOnly ∧
    ListPath.openFile limits.schema.snapshot schemaOnly.bytes = .ok source ∧
    source.schema.plan.arrow = input.schema ∧
    GroupsWire limits input.checksum source.schema.plan 4 0 input.groups groups ∧
    let indices := groups.map (WrittenGroup.index source.schema.plan)
    Schema.wrap limits.schema (payload groups) declared indices = .ok ⟨output.bytes, output.footer⟩ ∧
    output.metadata = Schema.metadata declared indices

end

/-- Compile the emitted schema to obtain the original path and thresholds,
then use the canonical projection for each complete group. -/
public def build (limits : Limits) (input : Input) : Except Error {output // Construction limits input output} := do
  let ⟨groupCap⟩ ← require (input.groups.length ≤ groupBudget limits) (.groupLimit input.groups.length)
  let rows := totalRows input
  let ⟨rowCap⟩ ← require (rows < 2 ^ 63 ∧ rows ≤ limits.maxTotalRows) (.totalRowLimit rows)
  let ⟨declared, planned⟩ ← checked (planSchema limits.schema input.schema) id
  let ⟨schemaOnly, envelope⟩ ← checked (Schema.wrap limits.schema .empty declared []) .schema
  let ⟨source, compiled⟩ ← checked (ListPath.openFile limits.schema.snapshot schemaOnly.bytes) .openReadback
  let ⟨exactSchema⟩ ← require
    (Schema.equal limits.schema.snapshot.maxSchemaDepth source.schema.plan.arrow input.schema = true)
    .readbackMismatch
  let ⟨groups, packed⟩ ← pack limits input.checksum source.schema.plan input.groups 0 4 0
  let indices := groups.map (WrittenGroup.index source.schema.plan)
  let ⟨framed, original⟩ ← checked (Schema.wrap limits.schema (payload groups) declared indices) .schema
  return ⟨⟨framed.bytes, framed.footer, Schema.metadata declared indices⟩, ⟨groupCap, rowCap,
    declared, schemaOnly, source, groups, planned, envelope, compiled,
    Schema.equal_exact exactSchema, packed, original, rfl⟩⟩

@[expose] public section

def serialize (limits : Limits) (input : Input) : Except Error Output :=
  (build limits input).map Subtype.val

def agrees (limits : Limits) (input : Input) (output : Output)
    (source : Source limits.schema.snapshot output.bytes) : Bool :=
  Schema.equal limits.schema.snapshot.maxSchemaDepth source.schema.plan.arrow input.schema &&
    decide (source.snapshot.footer = output.footer ∧ source.snapshot.metadata = output.metadata ∧
      source.snapshot.groupCount = input.groups.length)

/-- Read the emitted native envelope and every original group, and
compare the exact declaration and ordered observations through EOS. -/
def certify (limits : Limits) (input : Input) (output : Output) : Except Error Unit := do
  let source ← (ListPath.openFile limits.schema.snapshot output.bytes).mapError .openReadback
  if !agrees limits input output source then throw .readbackMismatch
  let ⟨_, trace⟩ ← (Reader.Events.readSource limits.chunk source.schema).mapError .events
  match trace.termination with
  | .eos =>
    let equal := Arrow.RecursiveSchema.Batch.Writer.agrees limits.schema.snapshot.maxSchemaDepth
    if (trace.batches.map eraseBatch).isEqv input.groups equal then return () else throw .readbackMismatch
  | .readError cause => throw (.events cause)
  | _ => throw .readbackMismatch

def emit (limits : Limits) (input : Input) : Except Error Output := do
  let output ← serialize limits input
  certify limits input output
  return output

structure Readback (limits : Limits) (input : Input) (output : Output) : Prop where
  original : ∃ (source : Source limits.schema.snapshot output.bytes)
      (events : Σ signature : Signature, Reader.Events.Trace signature),
    ListPath.openFile limits.schema.snapshot output.bytes = .ok source ∧
    source.snapshot.bytes = output.bytes ∧ source.snapshot.footer = output.footer ∧
    source.snapshot.metadata = output.metadata ∧ source.schema.plan.arrow = input.schema ∧
    source.snapshot.groupCount = input.groups.length ∧
    Reader.Events.read limits.schema.snapshot limits.chunk output.bytes = .ok events ∧
    declarations events.1 = input.schema.fields.map (fun field => (fieldName field, field)) ∧
    events.2.termination = .eos ∧ events.2.batches.map eraseBatch = input.groups ∧
    Reader.readAll limits.chunk source.schema = .ok input.groups ∧
    List.Forall₂ (Reader.GroupWire limits.chunk source.schema)
      (List.range source.snapshot.groupCount) input.groups

end

end Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Writer
