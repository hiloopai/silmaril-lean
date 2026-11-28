module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Rows.Events.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Writer.Schema.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.Defs
public import Silmaril.Formats.Arrow.RecursiveSchema.Batch.Writer.Defs

/-! Bounded native Parquet for the canonical signed two-LIST declaration.
Each original group gets one UNCOMPRESSED PLAIN V1 page of complete rows. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Writer

open Arrow.RecursiveSchema.Batch.Rows (Observation Row)
open Arrow.RecursiveSchema.Stream.Events (Signature declarations eraseBatch fieldName)

@[expose] public section

structure Limits where
  schema : Repeated.Writer.Schema.Limits := {}
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
  | schema (original : Repeated.Writer.Schema.Error)
  | groupLimit (actual : Nat)
  | totalRowLimit (actual : Nat)
  | rowCount (group expected actual : Nat)
  | projection (group : Nat)
  | pageLimit (group : Nat)
  | rowLimit (group actual : Nat)
  | slotLimit (group actual : Nat)
  | totalSlotLimit (group actual : Nat)
  | levelLimit (group : Nat)
  | bodyLimit (group : Nat)
  | headerLimit (group : Nat)
  | chunkLimit (group : Nat)
  | headerInteger (group : Nat)
  | measureMismatch (group : Nat)
  | openReadback (original : TwoList.Error)
  | events (original : Rows.Events.Error)
  | readbackMismatch
  deriving DecidableEq, Repr

/-- Emit the ordinary LIST and repeated-wrapper entries for the exact shape. -/
def planSchema (limits : Repeated.Writer.Schema.Limits) (schema : Arrow.RecursiveSchema.Schema) :
    Except Error Repeated.Writer.Schema.Plan := do
  let [.node (some outer) outerNullable .list
    [.node (some inner) innerNullable .list [.node (some leaf) leafNullable signed []]]] := schema.fields
    | throw .declaration
  let kind ← match signed with
    | .int32 => pure RecursiveSchema.Kind.int32
    | .int64 => pure RecursiveSchema.Kind.int64
    | _ => throw .declaration
  let compact := limits.snapshot.footer.compact
  if min limits.maxFields compact.maxCollectionSize < 6 then throw (.schema .fieldLimit)
  if ["schema", outer, "list", inner, leaf].any (fun name => name.utf8ByteSize > compact.maxBinaryBytes) then
    throw (.schema (.nameBudget []))
  return ⟨1, [.list outer outerNullable, .wrapper, .list inner innerNullable, .wrapper,
    .leaf leaf leafNullable kind]⟩

def checkInput (limits : Limits) (input : Input) : Except Error Unit := do
  if input.groups.length > min limits.maxGroups limits.schema.snapshot.footer.compact.maxCollectionSize then
    throw (.groupLimit input.groups.length)
  let total := (input.groups.map (·.rowCount)).sum
  if total > limits.maxTotalRows || total ≥ 2 ^ 63 then throw (.totalRowLimit total)

/-- Count the slots of a row before allocating its projected levels and words. -/
def slotDemand : Row → Nat
  | [outer] =>
    max 1 ((Rows.elements outer).foldl (fun count inner => count + max 1 (Rows.elements inner).length) 0)
  | _ => 0

def encodeBody (plan : Plan) (atoms : List Rows.Atom) : Bytes :=
  let reps := Repeated.Chunk.Writer.encodeSection 2 (atoms.map (·.repetition))
  let defs := Repeated.Chunk.Writer.encodeSection plan.maxDefinition (atoms.map (·.definition))
  (reps.append defs).append (Plain.encodeWords Repeated.Chunk.Writer.wordOctets (atoms.filterMap (·.word)))

def pageHeader (checksum : Bool) (slots : Nat) (body : Bytes) : Page.Header :=
  ⟨body.length, body.length, if checksum then some (Compression.Checksum.crc32.digest body.toList) else none,
    .dataV1 ⟨slots, 0, 3, 3⟩⟩

structure WrittenGroup where
  offset : Nat
  rows : Nat
  slots : Nat
  page : PlainV1Writer.Encoded

def WrittenGroup.index (plan : Plan) (group : WrittenGroup) : Repeated.Writer.Schema.GroupIndex :=
  ⟨group.rows, [⟨plan.kind, plan.leaf.location.path, group.slots, group.offset, group.page.wire.length⟩]⟩

structure Measured (limits : Limits) (plan : Plan) (already : Nat) (group : Observation) where
  atoms : List Rows.Atom
  projected : Rows.Relation plan atoms group.rows
  rowCount : group.rows.length = group.rowCount
  rows : group.rowCount ≤ limits.chunk.maxRows
  slots : atoms.length ≤ limits.chunk.maxSlots
  levelValues : atoms.length ≤ limits.chunk.levels.values
  totalSlots : already + atoms.length ≤ limits.maxTotalSlots
  bytes : Nat
  bodyCap : bytes ≤ limits.chunk.maxBodyBytes

/-- A whole logical group is the page input, including an explicit empty
group. The slot and body budgets precede the corresponding allocations. -/
def measure (limits : Limits) (plan : Plan) (ordinal offset already : Nat)
    (group : Observation) : Except Error (Measured limits plan already group) := do
  let chunk := limits.chunk
  let rows := group.rows.length
  if rowCount : rows ≠ group.rowCount then throw (.rowCount ordinal group.rowCount rows)
  else if rowCap : rows > chunk.maxRows then throw (.rowLimit ordinal rows)
  else
    if chunk.framing.maxPages = 0 then throw (.pageLimit ordinal)
    let slots := group.rows.foldl (fun count row => count + slotDemand row) 0
    if slotCap : slots > chunk.maxSlots ∨ slots > chunk.levels.values ∨ slots ≥ Hybrid.runLimit then
      throw (.slotLimit ordinal slots)
    else
      if totalCap : already + slots ≤ limits.maxTotalSlots then
        let repSize := Repeated.Chunk.Writer.sectionSize 2 slots
        let defSize := Repeated.Chunk.Writer.sectionSize plan.maxDefinition slots
        if repSize > 4 + chunk.levels.bytes || defSize > 4 + chunk.levels.bytes then throw (.levelLimit ordinal)
        match projected : Rows.Projection.trace plan group.rows with
        | none => throw (.projection ordinal)
        | some atoms =>
          if count : atoms.length ≠ slots then throw (.measureMismatch ordinal)
          else
            let present := atoms.countP (fun atom => atom.word.isSome)
            let size := repSize + defSize + present * RecursiveSchema.Chunk.wordWidth plan.kind
            let frameCap := min chunk.maxChunkBytes (limits.schema.fileBytes - offset - 8)
            if bounded : size < 2 ^ 31 ∧ size ≤ chunk.maxBodyBytes ∧ size ≤ frameCap then
              let exactRows := Decidable.not_not.mp rowCount
              have exactSlots := (Decidable.not_not.mp count).symm
              return ⟨atoms, projected, exactRows, exactRows ▸ Nat.le_of_not_gt rowCap,
                exactSlots ▸ Nat.le_of_not_gt (fun tooMany => slotCap (.inl tooMany)),
                exactSlots ▸ Nat.le_of_not_gt (fun tooMany => slotCap (.inr (.inl tooMany))),
                exactSlots ▸ totalCap, size, bounded.2.1⟩
            else throw (.bodyLimit ordinal)
      else throw (.totalSlotLimit ordinal (already + slots))

def writeGroup (limits : Limits) (checksum : Bool) (plan : Plan) (ordinal offset already : Nat)
    (group : Observation) : Except Error WrittenGroup := do
  let measured ← measure limits plan ordinal offset already group
  let body := encodeBody plan measured.atoms
  if body.length ≠ measured.bytes then throw (.measureMismatch ordinal)
  else
    let header := pageHeader checksum measured.atoms.length body
    let some headerBytes := PlainV1Writer.encodeHeaderWithChecksum measured.atoms.length measured.bytes header.crc |
      throw (.headerInteger ordinal)
    if headerBytes.length > limits.chunk.framing.maxHeaderBytes then throw (.headerLimit ordinal)
    else
      let frameCap := min limits.chunk.maxChunkBytes (limits.schema.fileBytes - offset - 8)
      if headerBytes.length + measured.bytes > frameCap then throw (.chunkLimit ordinal)
      else return ⟨offset, group.rowCount, measured.atoms.length, ⟨header, headerBytes, body⟩⟩

def packGroups (limits : Limits) (checksum : Bool) (plan : Plan) :
    List Observation → Nat → Nat → Nat → Except Error (List WrittenGroup)
  | [], _, _, _ => .ok []
  | group :: groups, ordinal, offset, slots => do
    let first ← writeGroup limits checksum plan ordinal offset slots group
    let rest ← packGroups limits checksum plan groups (ordinal + 1) (offset + first.page.wire.length)
      (slots + first.slots)
    return first :: rest

def payload (groups : List WrittenGroup) : Bytes :=
  groups.foldl (fun bytes group => bytes.append group.page.wire) .empty

structure Output where
  bytes : Bytes
  footer : Footer.Span
  metadata : Footer.Metadata

/-- Compile the emitted canonical declaration to obtain the same thresholds
that the final file's reader will use. -/
def serialize (limits : Limits) (input : Input) : Except Error Output := do
  checkInput limits input
  let declared ← planSchema limits.schema input.schema
  let schemaOnly ← (Repeated.Writer.Schema.wrap limits.schema .empty declared []).mapError .schema
  let source ← (TwoList.openFile limits.schema.snapshot schemaOnly.bytes).mapError .openReadback
  let groups ← packGroups limits input.checksum source.schema.plan input.groups 0 4 0
  let indices := groups.map (WrittenGroup.index source.schema.plan)
  let framed ← (Repeated.Writer.Schema.wrap limits.schema (payload groups) declared indices).mapError .schema
  return ⟨framed.bytes, framed.footer, Repeated.Writer.Schema.metadata declared indices⟩

def agrees (limits : Limits) (input : Input) (output : Output)
    (source : TwoList.Source limits.schema.snapshot output.bytes) : Bool :=
  Repeated.Writer.Schema.equal limits.schema.snapshot.maxSchemaDepth input.schema (Rows.arrowSchema source.schema.plan) &&
    decide (source.snapshot.footer = output.footer ∧ source.snapshot.metadata = output.metadata ∧
      source.snapshot.groupCount = input.groups.length)

/-- Check the original native stream before exposing the output. The Events
reader performs the underlying checked row-group reads. -/
def certify (limits : Limits) (input : Input) (output : Output) : Except Error Unit := do
  let source ← (TwoList.openFile limits.schema.snapshot output.bytes).mapError .openReadback
  if agrees limits input output source then
    let ⟨_, trace⟩ ← (Rows.Events.readSource limits.chunk source.schema).mapError .events
    match trace.termination with
    | .eos =>
      let equal := Arrow.RecursiveSchema.Batch.Writer.agrees limits.schema.snapshot.maxSchemaDepth
      if (trace.batches.map eraseBatch).isEqv input.groups equal then return () else throw .readbackMismatch
    | .readError cause => throw (.events cause)
    | _ => throw .readbackMismatch
  else throw .readbackMismatch

def emit (limits : Limits) (input : Input) : Except Error Output := do
  let output ← serialize limits input
  certify limits input output
  return output

structure GroupWire (limits : Limits) (checksum : Bool) (plan : Plan) (offset already : Nat)
    (input : Observation) (output : WrittenGroup) : Prop where
  original : ∃ atoms,
    Rows.Relation plan atoms input.rows ∧
    output.offset = offset ∧ output.rows = input.rowCount ∧ input.rowCount = input.rows.length ∧
    output.slots = atoms.length ∧ output.page.body = encodeBody plan atoms ∧
    output.page.header = pageHeader checksum output.slots output.page.body ∧
    PlainV1Writer.encodeHeaderWithChecksum output.slots output.page.body.length output.page.header.crc =
      some output.page.headerBytes ∧
    output.rows ≤ limits.chunk.maxRows ∧ output.slots ≤ limits.chunk.maxSlots ∧
    output.slots ≤ limits.chunk.levels.values ∧ already + output.slots ≤ limits.maxTotalSlots ∧
    output.page.body.length ≤ limits.chunk.maxBodyBytes ∧
    output.page.headerBytes.length ≤ limits.chunk.framing.maxHeaderBytes ∧
    output.page.wire.length ≤ min limits.chunk.maxChunkBytes (limits.schema.fileBytes - offset - 8)

inductive GroupsWire (limits : Limits) (checksum : Bool) (plan : Plan) :
    Nat → Nat → List Observation → List WrittenGroup → Prop where
  | nil (offset already : Nat) : GroupsWire limits checksum plan offset already [] []
  | cons {offset already input inputs output outputs} :
      GroupWire limits checksum plan offset already input output →
      GroupsWire limits checksum plan (offset + output.page.wire.length) (already + output.slots) inputs outputs →
      GroupsWire limits checksum plan offset already (input :: inputs) (output :: outputs)

structure Construction (limits : Limits) (input : Input) (output : Output) : Prop where
  original : ∃ declared schemaOnly source groups,
    checkInput limits input = .ok () ∧ planSchema limits.schema input.schema = .ok declared ∧
    Repeated.Writer.Schema.wrap limits.schema .empty declared [] = .ok schemaOnly ∧
    TwoList.openFile limits.schema.snapshot schemaOnly.bytes = .ok source ∧
    GroupsWire limits input.checksum source.schema.plan 4 0 input.groups groups ∧
    let indices := groups.map (WrittenGroup.index source.schema.plan)
    Repeated.Writer.Schema.wrap limits.schema (payload groups) declared indices = .ok ⟨output.bytes, output.footer⟩ ∧
    output.metadata = Repeated.Writer.Schema.metadata declared indices

structure Readback (limits : Limits) (input : Input) (output : Output) : Prop where
  original : ∃ (source : TwoList.Source limits.schema.snapshot output.bytes)
      (events : Σ schema : Signature, Rows.Events.Trace schema),
    TwoList.openFile limits.schema.snapshot output.bytes = .ok source ∧
    source.snapshot.bytes = output.bytes ∧ source.snapshot.footer = output.footer ∧
    source.snapshot.metadata = output.metadata ∧ Rows.arrowSchema source.schema.plan = input.schema ∧
    source.snapshot.groupCount = input.groups.length ∧
    Rows.Events.read limits.schema.snapshot limits.chunk output.bytes = .ok events ∧
    declarations events.1 = input.schema.fields.map (fun field => (fieldName field, field)) ∧
    events.2.termination = .eos ∧ events.2.batches.map eraseBatch = input.groups ∧
    Rows.readAll limits.chunk source.schema = .ok input.groups ∧
    List.Forall₂ (Rows.GroupWire limits.chunk source.schema)
      (List.range source.snapshot.groupCount) input.groups

end

end Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Writer
