module

public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.Chunk.Defs

/-! Checked unindexed UNCOMPRESSED PLAIN V1/V2 chunks, with at most one
repeated ancestor and independent bounds on slots and row starts. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk

open RecursiveSchema (SupportedEncodings)
open Repeated (Compiled Leaf LevelError)

@[expose] public section

abbrev Address := RecursiveSchema.Chunk.Address
abbrev Word := RecursiveSchema.Chunk.Word

structure Limits extends RecursiveSchema.Chunk.Limits where
  maxSlots : Nat := 1024 * 1024

/-- This profile uses neither offset indexes nor column indexes. Only V1
can continue a row across pages. -/
def Unindexed (chunk : Footer.ColumnChunk) : Prop :=
  chunk.offsetIndexOffset = none ∧ chunk.offsetIndexLength = none ∧
    chunk.columnIndexOffset = none ∧ chunk.columnIndexLength = none

instance (chunk : Footer.ColumnChunk) : Decidable (Unindexed chunk) := by
  unfold Unindexed
  infer_instance

inductive BindCause where
  | missing
  | association
  | codec (original : Int)
  | encodings (original : List Int)
  | pageOffsets
  | pageIndex
  | negativeCounts (slots rows : Int)
  | span
  deriving DecidableEq, Repr

inductive BindError where
  | group (ordinal : Nat)
  | leaf (group column : Nat)
  | column (address : Address) (cause : BindCause)
  deriving DecidableEq, Repr

structure Binding {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (schema : Compiled schemaLimits snapshot) (group column : Nat) where
  leaf : Leaf
  rowGroup : Footer.RowGroup
  chunk : Footer.ColumnChunk
  span : Footer.Span
  leafAt : schema.leaves[column]? = some leaf
  groupAt : snapshot.groupAt group = some rowGroup
  chunkAt : rowGroup.columns[column]? = some chunk
  path : chunk.metadata.pathInSchema = leaf.site.location.path
  physical : chunk.metadata.physicalType = leaf.kind.physical
  codec : chunk.metadata.codec = 0
  encodings : SupportedEncodings chunk.metadata
  pageOffsets : chunk.metadata.dictionaryPageOffset = none ∧ chunk.metadata.indexPageOffset = none
  unindexed : Unindexed chunk
  counts : 0 ≤ chunk.metadata.numValues ∧ 0 ≤ rowGroup.numRows
  originalSpan : Page.columnSpan snapshot.footer.start chunk.metadata = some span

end

private def lookup {α ε : Type} (source : Option α) (error : ε) :
    Except ε {result // source = some result} :=
  match source with
  | none => .error error
  | some result => .ok ⟨result, rfl⟩

private def check {ε : Type} (condition : Prop) [Decidable condition] (error : ε) :
    Except ε (PLift condition) :=
  if yes : condition then .ok ⟨yes⟩ else .error error

/-- Bind the original positional chunk, with separate metadata counts for
level entries and rows. Neither count is inferred from the other. -/
public def bindChunk {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (schema : Compiled schemaLimits snapshot) (group column : Nat) :
    Except BindError (Binding schema group column) := do
  let ⟨rowGroup, groupAt⟩ ← lookup (snapshot.groupAt group) (.group group)
  let ⟨leaf, leafAt⟩ ← lookup schema.leaves[column]? (.leaf group column)
  let fail := BindError.column ⟨group, column, leaf.site.location.path⟩
  let ⟨chunk, chunkAt⟩ ← lookup rowGroup.columns[column]? (fail .missing)
  let metadata := chunk.metadata
  let ⟨⟨path, physical⟩⟩ ← check
    (metadata.pathInSchema = leaf.site.location.path ∧ metadata.physicalType = leaf.kind.physical)
    (fail .association)
  let ⟨codec⟩ ← check (metadata.codec = 0) (fail (.codec metadata.codec))
  let ⟨encodings⟩ ← check (SupportedEncodings metadata) (fail (.encodings metadata.encodings))
  let ⟨pageOffsets⟩ ← check
    (metadata.dictionaryPageOffset = none ∧ metadata.indexPageOffset = none) (fail .pageOffsets)
  let ⟨unindexed⟩ ← check (Unindexed chunk) (fail .pageIndex)
  let ⟨counts⟩ ← check (0 ≤ metadata.numValues ∧ 0 ≤ rowGroup.numRows)
    (fail (.negativeCounts metadata.numValues rowGroup.numRows))
  let ⟨span, originalSpan⟩ ← lookup (Page.columnSpan snapshot.footer.start metadata) (fail .span)
  return ⟨leaf, rowGroup, chunk, span, leafAt, groupAt, chunkAt, path, physical, codec, encodings,
    pageOffsets, unindexed, counts, originalSpan⟩

@[expose] public section

structure State where
  slot : Nat := 0
  rows : Nat := 0
  live : Bool := false
  deriving DecidableEq, Repr

structure Cursor where
  page : Nat
  byte : Nat
  state : State
  deriving DecidableEq, Repr

inductive LevelCause where
  | countLimit
  | section (original : FlatPage.Error)
  | hybrid (original : Hybrid.Error)
  | unexpectedV2Levels (bytes : Nat)
  deriving DecidableEq, Repr

inductive PageCause where
  | framing (original : Page.Error)
  | header (original : RecursiveSchema.Chunk.Cause)
  | slotOverrun (remaining advertised : Nat)
  | checksum (original : Page.Checksum.Error)
  | repetition (original : LevelCause)
  | definition (original : LevelCause)
  | level (original : LevelError)
  | continuationWithoutList (slot : Nat)
  | rowOverrun (slot expected : Nat)
  | levelCount (firstUnmatched : Nat)
  | plain (original : Plain.Error)
  | alignment (original : FlatPage.Error)
  | v2Encoding (actual : Int)
  | v2Extent
  | v2RowBoundary (slot repetition : Nat)
  | v2Rows (declared actual : Nat)
  | v2Nulls (declared actual : Nat)
  deriving DecidableEq, Repr

inductive ChunkCause where
  | bounds
  | chunkLimit
  | slotLimit (original : Nat)
  | rowLimit (original : Nat)
  | uncompressedSize (original : Int) (spanBytes : Nat)
  | slotCount (expected actual : Nat)
  | rowCount (expected actual : Nat)
  deriving DecidableEq, Repr

inductive Error where
  | chunk (address : Address) (span : Footer.Span) (cause : ChunkCause)
  | page (address : Address) (cursor : Cursor) (cause : PageCause)
  deriving DecidableEq, Repr

def bitWidth (maximum : Nat) : Nat :=
  if maximum = 0 then 0 else maximum.log2 + 1

structure LevelBlock where
  levels : List Nat
  tail : Bytes

/-- A zero maximum omits the entire level section. An encoded level
section uses the existing exact four-byte V1 prefix and hybrid reader. -/
def readLevels (limits : Hybrid.Limits) (maximum count : Nat) (body : Bytes) :
    Except LevelCause LevelBlock :=
  if maximum = 0 then
    if Hybrid.runLimit ≤ count ∨ limits.values < count then .error .countLimit
    else .ok ⟨List.replicate count 0, body⟩
  else do
    let parts ← (FlatPage.splitV1Optional limits.bytes body).mapError .section
    let levels ← (Hybrid.decode (bitWidth maximum) count limits parts.definitions).mapError .hybrid
    return ⟨levels, parts.scalars⟩

inductive LevelWire (limits : Hybrid.Limits) (maximum count : Nat) (body : Bytes) :
    LevelBlock → Prop where
  | omitted : maximum = 0 → count < Hybrid.runLimit → count ≤ limits.values →
      LevelWire limits maximum count body ⟨List.replicate count 0, body⟩
  | encoded {levels : List Nat} {tail encodedBytes : Bytes} {lengthBytes : List UInt8} :
      maximum ≠ 0 → lengthBytes.length = 4 → KBytes.leVal lengthBytes = encodedBytes.length →
      encodedBytes.length ≤ limits.bytes →
      body.toList = lengthBytes ++ encodedBytes.toList ++ tail.toList →
      Hybrid.Wire (bitWidth maximum) count encodedBytes.toList levels →
      LevelWire limits maximum count body ⟨levels, tail⟩

structure LevelSlot where
  repetition : Nat
  definition : Nat
  classified : Repeated.Slot
  deriving DecidableEq, Repr

def LevelSlot.present (slot : LevelSlot) : Bool :=
  match slot.classified.presence with
  | .value => true
  | .absent _ => false

def LevelSlot.startsRow (slot : LevelSlot) : Bool := slot.repetition == 0

/-- A slot reaches a live element-bearing list exactly when its definition
passes the wrapper boundary. Null elements also occupy a live element slot. -/
def State.consume (state : State) (leaf : Leaf) (repetition definition : Nat) : State :=
  ⟨state.slot + 1, state.rows + (if repetition = 0 then 1 else 0),
    leaf.repeated.any fun boundary => boundary.emptyLevel < definition⟩

/-- Per-slot wire witness with the original global slot ordinal, exact
classification, and an incoming open-list requirement for continuation. -/
inductive SlotsWire (leaf : Leaf) (rowCeiling : Nat) :
    List Nat → List Nat → State → List LevelSlot → State → Prop where
  | nil (state : State) : SlotsWire leaf rowCeiling [] [] state [] state
  | cons {rep defn reps defs start classified tail stop} :
      leaf.classify start.slot rep defn = .ok classified →
      (rep = 0 ∨ start.live = true) →
      (start.consume leaf rep defn).rows ≤ rowCeiling →
      SlotsWire leaf rowCeiling reps defs (start.consume leaf rep defn) tail stop →
      SlotsWire leaf rowCeiling (rep :: reps) (defn :: defs) start
        (⟨rep, defn, classified⟩ :: tail) stop

structure Classified where
  levels : List LevelSlot
  after : State

def classifySlotsFrom (leaf : Leaf) (rowCeiling : Nat) :
    List Nat → List Nat → State → List LevelSlot → Except PageCause Classified
  | [], [], start, reversed => .ok ⟨reversed.reverse, start⟩
  | rep :: reps, defn :: defs, start, reversed =>
    match leaf.classify start.slot rep defn with
    | .error cause => .error (.level cause)
    | .ok slot =>
      if rep = 0 ∨ start.live = true then
        let next := start.consume leaf rep defn
        if next.rows ≤ rowCeiling then
          classifySlotsFrom leaf rowCeiling reps defs next (⟨rep, defn, slot⟩ :: reversed)
        else .error (.rowOverrun start.slot rowCeiling)
      else .error (.continuationWithoutList start.slot)
  | _, _, start, _ => .error (.levelCount start.slot)

/-- Tail-recursive classification of original slots, carrying the live
state through page boundaries. Failures keep the first original slot. -/
def classifySlots (leaf : Leaf) (rowCeiling : Nat) (reps defs : List Nat)
    (start : State) : Except PageCause Classified :=
  classifySlotsFrom leaf rowCeiling reps defs start []

def admitPage (frame : Page.Frame) (remaining : Nat) : Except PageCause Page.DataV1 :=
  (RecursiveSchema.Chunk.admitPage frame remaining).mapError fun
    | .rowOverrun remaining advertised => .slotOverrun remaining advertised
    | cause => .header cause

structure DecodedPage where
  levels : List LevelSlot
  words : List (Option Word)
  after : State
  deriving Repr

/-- Classify original slots and consume the exact signed suffix. -/
def decodeSlots (leaf : Leaf) (repetitions definitions : List Nat) (suffix : Bytes)
    (start : State) (rowCeiling : Nat) : Except PageCause DecodedPage := do
  let classified ← classifySlots leaf rowCeiling repetitions definitions start
  let mask := classified.levels.map LevelSlot.present
  let words ← (RecursiveSchema.Chunk.readWords leaf.kind (mask.count true) suffix).mapError .plain
  let aligned ← (FlatPage.reconstruct mask words).mapError .alignment
  return ⟨classified.levels, aligned, classified.after⟩

structure DecodedWire (leaf : Leaf) (repetitions definitions : List Nat) (suffix : Bytes)
    (start : State) (rowCeiling : Nat) (decoded : DecodedPage) : Prop where
  slots : SlotsWire leaf rowCeiling repetitions definitions start decoded.levels decoded.after
  words : ∃ original : List (List UInt8),
    suffix.toList = original.flatten ∧ original.length = (decoded.levels.map LevelSlot.present).count true ∧
    (∀ word ∈ original, word.length = RecursiveSchema.Chunk.wordWidth leaf.kind) ∧
    decoded.words.map Option.isSome = decoded.levels.map LevelSlot.present ∧
    decoded.words.filterMap id = original.map (RecursiveSchema.Chunk.readWord leaf.kind)

/-- The existing V1 entry point checks the original length-prefixed levels. -/
def decodePage (limits : Limits) (leaf : Leaf) (source : Bytes) (frame : Page.Frame)
    (start : State) (remaining rowCeiling : Nat) : Except PageCause DecodedPage := do
  let info ← admitPage frame remaining
  let _ ← (Page.Checksum.verify limits.maxBodyBytes source frame).mapError .checksum
  let body := Page.Checksum.payloadBytes source frame
  let reps ← (readLevels limits.levels leaf.maxRepetition info.numValues body).mapError .repetition
  let defs ← (readLevels limits.levels leaf.maxDefinition info.numValues reps.tail).mapError .definition
  decodeSlots leaf reps.levels defs.levels defs.tail start rowCeiling

structure PageWire (limits : Limits) (leaf : Leaf) (source : Bytes) (frame : Page.Frame)
    (start : State) (remaining rowCeiling : Nat) (decoded : DecodedPage) : Prop where
  original : ∃ (info : Page.DataV1) (body : Bytes) (reps defs : LevelBlock)
    (words : List (List UInt8)) (checksum : Page.Checksum.Status),
    RecursiveSchema.Chunk.HeaderWire frame remaining info ∧
    Page.Checksum.verify limits.maxBodyBytes source frame = .ok checksum ∧
    source.slice? frame.payload.start (some frame.payload.stop) = some body ∧
    body.length = frame.value.compressedSize ∧
    LevelWire limits.levels leaf.maxRepetition info.numValues body reps ∧
    LevelWire limits.levels leaf.maxDefinition info.numValues reps.tail defs ∧
    SlotsWire leaf rowCeiling reps.levels defs.levels start decoded.levels decoded.after ∧
    defs.tail.toList = words.flatten ∧ words.length = (decoded.levels.map LevelSlot.present).count true ∧
    (∀ word ∈ words, word.length = RecursiveSchema.Chunk.wordWidth leaf.kind) ∧
    decoded.words.map Option.isSome = decoded.levels.map LevelSlot.present ∧
    decoded.words.filterMap id = words.map (RecursiveSchema.Chunk.readWord leaf.kind) ∧
    decoded.levels.length = info.numValues

/-- V2 level lengths come from the header. A zero maximum omits the section. -/
def readV2Levels (limits : Hybrid.Limits) (maximum count : Nat) (bytes : Bytes) :
    Except LevelCause (List Nat) :=
  if maximum = 0 then
    if bytes.length ≠ 0 then .error (.unexpectedV2Levels bytes.length)
    else if Hybrid.runLimit ≤ count ∨ limits.values < count then .error .countLimit
    else .ok (List.replicate count 0)
  else (Hybrid.decode (bitWidth maximum) count limits bytes).mapError .hybrid

inductive V2LevelWire (limits : Hybrid.Limits) (maximum count : Nat) (bytes : Bytes) :
    List Nat → Prop where
  | omitted : maximum = 0 → bytes.length = 0 → count < Hybrid.runLimit → count ≤ limits.values →
      V2LevelWire limits maximum count bytes (List.replicate count 0)
  | encoded {levels : List Nat} :
      maximum ≠ 0 → bitWidth maximum ≤ 32 → count < Hybrid.runLimit → count ≤ limits.values →
      bytes.length ≤ limits.bytes → Hybrid.Wire (bitWidth maximum) count bytes.toList levels →
      V2LevelWire limits maximum count bytes levels

def bytesAt (source : Bytes) (span : Footer.Span) : Bytes :=
  Footer.fileBytes source span.start span.stop

def absentSlots (decoded : DecodedPage) : Nat :=
  decoded.levels.countP (fun slot => !slot.present)

/-- V2 occupies complete rows. Closing the boundary also prevents a
following V1 page from continuing a row that ended on a V2 page. -/
def closeV2 (decoded : DecodedPage) : DecodedPage :=
  { decoded with after.live := false }

def admitV2Page (frame : Page.Frame) (remaining : Nat) : Except PageCause Page.DataV2 :=
  match frame.value.kind with
  | .dataV2 info =>
    if info.encoding ≠ 0 then .error (.v2Encoding info.encoding)
    else if frame.value.uncompressedSize ≠ frame.value.compressedSize then
      .error (.header (.pageSizes frame.value.uncompressedSize frame.value.compressedSize))
    else if info.numValues > remaining then .error (.slotOverrun remaining info.numValues)
    else .ok info
  | kind => .error (.header (.pageKind kind))

/-- Check the V2 row boundary and counts around the shared signed decoder. -/
def decodeV2Slots (leaf : Leaf) (info : Page.DataV2) (reps defs : List Nat) (suffix : Bytes)
    (start : State) (rowCeiling : Nat) : Except PageCause DecodedPage :=
  let first := reps.head?.getD 0
  let rows := reps.count 0
  if first ≠ 0 then .error (.v2RowBoundary start.slot first)
  else if rows ≠ info.numRows then .error (.v2Rows info.numRows rows)
  else do
    let checked ← decodeSlots leaf reps defs suffix start rowCeiling
    let nulls := absentSlots checked
    if nulls ≠ info.numNulls then .error (.v2Nulls info.numNulls nulls)
    else .ok (closeV2 checked)

/-- Decode a V2 frame from an UNCOMPRESSED chunk. A resolved compression
flag uses the chunk codec, so either flag leaves this codec-zero suffix raw. -/
def decodeV2Page (limits : Limits) (leaf : Leaf) (source : Bytes) (frame : Page.Frame)
    (start : State) (remaining rowCeiling : Nat) : Except PageCause DecodedPage := do
  let info ← admitV2Page frame remaining
  let _ ← (Page.Checksum.verify limits.maxBodyBytes source frame).mapError .checksum
  let some spans := frame.v2Spans | throw .v2Extent
  let reps ← (readV2Levels limits.levels leaf.maxRepetition info.numValues
    (bytesAt source spans.repetition)).mapError .repetition
  let defs ← (readV2Levels limits.levels leaf.maxDefinition info.numValues
    (bytesAt source spans.definition)).mapError .definition
  decodeV2Slots leaf info reps defs (bytesAt source spans.values) start rowCeiling

structure V2PageWire (limits : Limits) (leaf : Leaf) (source : Bytes) (frame : Page.Frame)
    (start : State) (remaining rowCeiling : Nat) (decoded : DecodedPage) : Prop where
  original : ∃ (info : Page.DataV2) (spans : Page.V2Spans) (reps defs : List Nat)
      (checksum : Page.Checksum.Status) (checked : DecodedPage),
    frame.value.kind = .dataV2 info ∧ info.encoding = 0 ∧ info.numValues ≤ remaining ∧
    frame.value.uncompressedSize = frame.value.compressedSize ∧
    Page.Checksum.verify limits.maxBodyBytes source frame = .ok checksum ∧ frame.v2Spans = some spans ∧
    (∀ span ∈ [spans.repetition, spans.definition, spans.values],
      source.slice? span.start (some span.stop) = some (bytesAt source span)) ∧
    V2LevelWire limits.levels leaf.maxRepetition info.numValues (bytesAt source spans.repetition) reps ∧
    V2LevelWire limits.levels leaf.maxDefinition info.numValues (bytesAt source spans.definition) defs ∧
    reps.head?.getD 0 = 0 ∧ reps.count 0 = info.numRows ∧ absentSlots decoded = info.numNulls ∧
    decoded.levels.length = info.numValues ∧
    DecodedWire leaf reps defs (bytesAt source spans.values) start rowCeiling checked ∧
    decoded = closeV2 checked

def decodeDataPage (limits : Limits) (leaf : Leaf) (source : Bytes) (frame : Page.Frame)
    (start : State) (remaining rowCeiling : Nat) : Except PageCause DecodedPage :=
  match frame.value.kind with
  | .dataV2 _ => decodeV2Page limits leaf source frame start remaining rowCeiling
  | _ => decodePage limits leaf source frame start remaining rowCeiling

inductive DataPageWire (limits : Limits) (leaf : Leaf) (source : Bytes) (frame : Page.Frame)
    (start : State) (remaining rowCeiling : Nat) (decoded : DecodedPage) : Prop where
  | v1 : PageWire limits leaf source frame start remaining rowCeiling decoded →
      DataPageWire limits leaf source frame start remaining rowCeiling decoded
  | v2 : V2PageWire limits leaf source frame start remaining rowCeiling decoded →
      DataPageWire limits leaf source frame start remaining rowCeiling decoded

structure ObservedPage where
  start : Cursor
  frame : Page.Frame
  decoded : DecodedPage
  deriving Repr

def Cursor.advance (cursor : Cursor) (page : ObservedPage) : Cursor :=
  ⟨cursor.page + 1, page.frame.payload.stop, page.decoded.after⟩

structure Carrier where
  bytes : Bytes
  span : Footer.Span
  leaf : Leaf
  address : Address
  slots : Nat
  rows : Nat

def initial (carrier : Carrier) : Cursor := ⟨0, carrier.span.start, {}⟩

def walk (limits : Limits) (carrier : Carrier) (budget : Nat) (cursor : Cursor)
    (reversed : List ObservedPage) : Except Error (List ObservedPage) :=
  if cursor.byte = carrier.span.stop then
    if cursor.state.slot ≠ carrier.slots then
      .error (.chunk carrier.address carrier.span (.slotCount carrier.slots cursor.state.slot))
    else if cursor.state.rows ≠ carrier.rows then
      .error (.chunk carrier.address carrier.span (.rowCount carrier.rows cursor.state.rows))
    else .ok reversed.reverse
  else
    let failed := Error.page carrier.address cursor
    match budget with
    | 0 => .error (failed (.framing .pageLimit))
    | fuel + 1 => do
      let frame ← (Page.readPage limits.framing carrier.bytes carrier.span cursor.byte).mapError
        (failed ∘ .framing)
      let decoded ← (decodeDataPage limits carrier.leaf carrier.bytes frame cursor.state
        (carrier.slots - cursor.state.slot) carrier.rows).mapError failed
      let page : ObservedPage := ⟨cursor, frame, decoded⟩
      walk limits carrier fuel (cursor.advance page) (page :: reversed)

structure Observation where
  pages : List ObservedPage
  deriving Repr

def Observation.levels (column : Observation) : List LevelSlot :=
  column.pages.flatMap (·.decoded.levels)

def carrierOf {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group column : Nat}
    (binding : Binding schema group column) : Carrier :=
  ⟨snapshot.bytes, binding.span, binding.leaf, ⟨group, column, binding.leaf.site.location.path⟩,
    binding.chunk.metadata.numValues.toNat, binding.rowGroup.numRows.toNat⟩

def read {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group column : Nat}
    (limits : Limits) (binding : Binding schema group column) : Except Error Observation :=
  let carrier := carrierOf binding
  let bytes := carrier.span.stop - carrier.span.start
  let failed := Error.chunk carrier.address carrier.span
  if ¬ (carrier.span.start ≤ carrier.span.stop ∧ carrier.span.stop ≤ carrier.bytes.length)
    then .error (failed .bounds)
  else if bytes > limits.maxChunkBytes then .error (failed .chunkLimit)
  else if carrier.slots > limits.maxSlots then .error (failed (.slotLimit carrier.slots))
  else if carrier.rows > limits.maxRows then .error (failed (.rowLimit carrier.rows))
  else if binding.chunk.metadata.totalUncompressedSize ≠ Int.ofNat bytes then
    .error (failed (.uncompressedSize binding.chunk.metadata.totalUncompressedSize bytes))
  else (walk limits carrier limits.framing.maxPages (initial carrier) []).map Observation.mk

inductive ChainWire (limits : Limits) (carrier : Carrier) : Cursor → Cursor → List ObservedPage → Prop where
  | nil (cursor : Cursor) : ChainWire limits carrier cursor cursor []
  | more {start stop first rest} :
      Page.readPage limits.framing carrier.bytes carrier.span start.byte = .ok first.frame →
      first.start = start →
      DataPageWire limits carrier.leaf carrier.bytes first.frame start.state
        (carrier.slots - start.state.slot) carrier.rows first.decoded →
      ChainWire limits carrier (start.advance first) stop rest →
      ChainWire limits carrier start stop (first :: rest)

structure Wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group column : Nat}
    (limits : Limits) (binding : Binding schema group column) (output : Observation) : Prop where
  bounds : binding.span.start ≤ binding.span.stop ∧ binding.span.stop ≤ snapshot.bytes.length
  chunkCap : binding.span.stop - binding.span.start ≤ limits.maxChunkBytes
  slotCap : binding.chunk.metadata.numValues.toNat ≤ limits.maxSlots
  rowCap : binding.rowGroup.numRows.toNat ≤ limits.maxRows
  pageCap : output.pages.length ≤ limits.framing.maxPages
  uncompressed : binding.chunk.metadata.totalUncompressedSize =
    Int.ofNat (binding.span.stop - binding.span.start)
  chain : ∃ stop : Cursor, stop.byte = binding.span.stop ∧
    stop.state.slot = binding.chunk.metadata.numValues.toNat ∧
    stop.state.rows = binding.rowGroup.numRows.toNat ∧
    ChainWire limits (carrierOf binding) (initial (carrierOf binding)) stop output.pages
  frames : Page.Chain binding.span binding.span.start binding.span.stop (output.pages.map ObservedPage.frame)
  slots : output.levels.length = binding.chunk.metadata.numValues.toNat
  rows : output.levels.countP LevelSlot.startsRow = binding.rowGroup.numRows.toNat

end

end Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk
