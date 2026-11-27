module

public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.Chunk.Defs
public import Silmaril.Formats.Parquet.ScalarPage.Defs

/-! Checked unindexed PLAIN V1/V2 chunks with Snappy or identity codecs, at most one
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

/-- The recursive reader admits the identity and Snappy column codecs. -/
inductive ColumnCodec where
  | uncompressed
  | snappy
  deriving DecidableEq, Repr

def ColumnCodec.payload : ColumnCodec → Payload.Codec
  | .uncompressed => .uncompressed
  | .snappy => .snappy

def ColumnCodec.id (codec : ColumnCodec) : Int :=
  codec.payload.id

def ColumnCodec.ofId : Int → Option ColumnCodec
  | 0 => some .uncompressed
  | 1 => some .snappy
  | _ => none

def ColumnCodec.v2 (codec : ColumnCodec) (info : Page.DataV2) : Int :=
  ScalarPage.v2Codec codec.id (some info.isCompressed)

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

/-- A pageless chunk retains its original metadata, but has no byte interval. -/
inductive Storage (snapshot : Snapshot.Checked) (rowGroup : Footer.RowGroup)
    (chunk : Footer.ColumnChunk) where
  | framed (span : Footer.Span)
      (encodings : SupportedEncodings chunk.metadata)
      (original : Page.columnSpan snapshot.footer.start chunk.metadata = some span)
  | pageless (admitted : snapshot.admitsPageLessRecursive rowGroup = true)

structure Binding {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (schema : Compiled schemaLimits snapshot) (group column : Nat) where
  leaf : Leaf
  rowGroup : Footer.RowGroup
  chunk : Footer.ColumnChunk
  storage : Storage snapshot rowGroup chunk
  leafAt : schema.leaves[column]? = some leaf
  groupAt : snapshot.groupAt group = some rowGroup
  chunkAt : rowGroup.columns[column]? = some chunk
  path : chunk.metadata.pathInSchema = leaf.site.location.path
  physical : chunk.metadata.physicalType = leaf.kind.physical
  codec : ColumnCodec
  originalCodec : ColumnCodec.ofId chunk.metadata.codec = some codec
  pageOffsets : chunk.metadata.dictionaryPageOffset = none ∧ chunk.metadata.indexPageOffset = none
  unindexed : Unindexed chunk
  counts : 0 ≤ chunk.metadata.numValues ∧ 0 ≤ rowGroup.numRows

def Binding.span? {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group column : Nat}
    (binding : Binding schema group column) : Option Footer.Span :=
  match binding.storage with
  | .framed span _ _ => some span
  | .pageless _ => none

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
  let ⟨codec, originalCodec⟩ ← lookup (ColumnCodec.ofId metadata.codec) (fail (.codec metadata.codec))
  let encodings ← if admitted : snapshot.admitsPageLessRecursive rowGroup = true then
      pure (Sum.inl (PLift.up admitted))
    else do
      let supported ← check (SupportedEncodings metadata) (fail (.encodings metadata.encodings))
      pure (Sum.inr supported)
  let ⟨pageOffsets⟩ ← check
    (metadata.dictionaryPageOffset = none ∧ metadata.indexPageOffset = none) (fail .pageOffsets)
  let ⟨unindexed⟩ ← check (Unindexed chunk) (fail .pageIndex)
  let ⟨counts⟩ ← check (0 ≤ metadata.numValues ∧ 0 ≤ rowGroup.numRows)
    (fail (.negativeCounts metadata.numValues rowGroup.numRows))
  let storage ← match encodings with
    | .inl admitted => pure (.pageless admitted.down)
    | .inr supported => do
      let ⟨span, original⟩ ← lookup (Page.columnSpan snapshot.footer.start metadata) (fail .span)
      pure (.framed span supported.down original)
  return ⟨leaf, rowGroup, chunk, storage, leafAt, groupAt, chunkAt, path, physical, codec, originalCodec,
    pageOffsets, unindexed, counts⟩

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
  | v2SignedExtent (declared expected : Nat)
  | payload (original : Payload.Error)
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

def admitPage (frame : Page.Frame) (remaining : Nat) (codec : ColumnCodec := .uncompressed) :
    Except PageCause Page.DataV1 :=
  (RecursiveSchema.Chunk.admitPageWith (codec == .uncompressed) frame remaining).mapError fun
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

def decodeSnappy (bounds : Payload.Bounds) (stored : Bytes) : Except PageCause Bytes :=
  ((Payload.decode bounds Payload.Codec.snappy.id stored.toList).mapError .payload).map Bytes.ofList

def v1BodyBounds (limits : Limits) (frame : Page.Frame) : Payload.Bounds :=
  ⟨frame.value.compressedSize, limits.maxBodyBytes, frame.value.uncompressedSize, limits.maxBodyBytes, 0⟩

/-- The serialized V1 body, including each level prefix, uses the column
codec. Verify the stored frame before extracting bytes or expanding it. -/
def readV1Body (limits : Limits) (codec : ColumnCodec) (source : Bytes) (frame : Page.Frame) :
    Except PageCause Bytes := do
  let _ ← (Page.Checksum.verify limits.maxBodyBytes source frame).mapError .checksum
  let stored := Page.Checksum.payloadBytes source frame
  match codec with
  | .uncompressed => return stored
  | .snappy => decodeSnappy (v1BodyBounds limits frame) stored

structure V1BodyWire (limits : Limits) (codec : ColumnCodec) (source : Bytes) (frame : Page.Frame)
    (body : Bytes) : Prop where
  original : ∃ stored checksum,
    Page.Checksum.verify limits.maxBodyBytes source frame = .ok checksum ∧
    source.slice? frame.payload.start (some frame.payload.stop) = some stored ∧
    stored.length = frame.value.compressedSize ∧ stored.length ≤ limits.maxBodyBytes ∧
    body.length = frame.value.uncompressedSize ∧ body.length ≤ limits.maxBodyBytes ∧
    Payload.Decodes frame.value.uncompressedSize codec.payload stored.toList body.toList

def decodeV1Page (limits : Limits) (codec : ColumnCodec) (leaf : Leaf) (source : Bytes)
    (frame : Page.Frame) (start : State) (remaining rowCeiling : Nat) : Except PageCause DecodedPage := do
  let info ← admitPage frame remaining codec
  let body ← readV1Body limits codec source frame
  let reps ← (readLevels limits.levels leaf.maxRepetition info.numValues body).mapError .repetition
  let defs ← (readLevels limits.levels leaf.maxDefinition info.numValues reps.tail).mapError .definition
  decodeSlots leaf reps.levels defs.levels defs.tail start rowCeiling

/-- The identity-codec V1 entry point used by native writer readback. -/
def decodePage (limits : Limits) (leaf : Leaf) (source : Bytes) (frame : Page.Frame)
    (start : State) (remaining rowCeiling : Nat) : Except PageCause DecodedPage :=
  decodeV1Page limits .uncompressed leaf source frame start remaining rowCeiling

structure PageWire (limits : Limits) (leaf : Leaf) (source : Bytes) (frame : Page.Frame)
    (start : State) (remaining rowCeiling : Nat) (decoded : DecodedPage)
    (codec : ColumnCodec := .uncompressed) : Prop where
  original : ∃ (info : Page.DataV1) (body : Bytes) (reps defs : LevelBlock),
    frame.value.kind = .dataV1 info ∧
    (info.encoding = 0 ∧ info.definitionLevelEncoding = 3 ∧ info.repetitionLevelEncoding = 3) ∧
    info.numValues ≤ remaining ∧
    V1BodyWire limits codec source frame body ∧
    LevelWire limits.levels leaf.maxRepetition info.numValues body reps ∧
    LevelWire limits.levels leaf.maxDefinition info.numValues reps.tail defs ∧
    DecodedWire leaf reps.levels defs.levels defs.tail start rowCeiling decoded ∧
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

def admitV2Page (codec : ColumnCodec) (frame : Page.Frame) (remaining : Nat) : Except PageCause Page.DataV2 :=
  match frame.value.kind with
  | .dataV2 info =>
    if info.encoding ≠ 0 then .error (.v2Encoding info.encoding)
    else if codec.v2 info = 0 ∧ frame.value.uncompressedSize ≠ frame.value.compressedSize then
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

def v2LevelBytes (info : Page.DataV2) : Nat :=
  info.repetitionBytes + info.definitionBytes

def v2ValueBounds (limits : Limits) (frame : Page.Frame) (info : Page.DataV2) : Payload.Bounds :=
  let levels := v2LevelBytes info
  ⟨frame.value.compressedSize - levels, limits.maxBodyBytes,
    frame.value.uncompressedSize - levels, limits.maxBodyBytes - levels, 0⟩

/-- Check both extents before subtracting the original raw level prefix.
Only the independently bounded stored value suffix enters Snappy. -/
def readV2Suffix (limits : Limits) (codec : ColumnCodec) (leaf : Leaf)
    (frame : Page.Frame) (info : Page.DataV2) (stored : Bytes) : Except PageCause Bytes := do
  let levels := v2LevelBytes info
  let bounds := v2ValueBounds limits frame info
  if levels > frame.value.compressedSize ∨ levels > frame.value.uncompressedSize then
    throw .v2Extent
  if codec.v2 info = 0 then
    if stored.length = bounds.expectedSize then return stored
    else throw .v2Extent
  else
    if frame.value.uncompressedSize > limits.maxBodyBytes then throw (.payload .outputLimit)
    let expected := (info.numValues - info.numNulls) * RecursiveSchema.Chunk.wordWidth leaf.kind
    if bounds.expectedSize ≠ expected then throw (.v2SignedExtent bounds.expectedSize expected)
    decodeSnappy bounds stored

inductive V2SuffixWire (limits : Limits) (codec : ColumnCodec) (frame : Page.Frame)
    (info : Page.DataV2) (stored : Bytes) : Bytes → Prop where
  | raw : codec.v2 info = 0 → stored.length = (v2ValueBounds limits frame info).expectedSize →
      V2SuffixWire limits codec frame info stored stored
  | snappy {raw : Bytes} :
      codec.v2 info = 1 →
      Payload.Decodes (v2ValueBounds limits frame info).expectedSize .snappy stored.toList raw.toList →
      stored.length = (v2ValueBounds limits frame info).compressedSize →
      raw.length = (v2ValueBounds limits frame info).expectedSize →
      frame.value.uncompressedSize ≤ limits.maxBodyBytes →
      V2SuffixWire limits codec frame info stored raw

/-- Verify CRC on the original body, decode the original level spans, and
use the header's resolved flag and original column codec for the suffix. -/
def decodeV2Page (limits : Limits) (codec : ColumnCodec) (leaf : Leaf)
    (source : Bytes) (frame : Page.Frame) (start : State)
    (remaining rowCeiling : Nat) : Except PageCause DecodedPage := do
  let info ← admitV2Page codec frame remaining
  let _ ← (Page.Checksum.verify limits.maxBodyBytes source frame).mapError .checksum
  let some spans := frame.v2Spans | throw .v2Extent
  let reps ← (readV2Levels limits.levels leaf.maxRepetition info.numValues
    (bytesAt source spans.repetition)).mapError .repetition
  let defs ← (readV2Levels limits.levels leaf.maxDefinition info.numValues
    (bytesAt source spans.definition)).mapError .definition
  let suffix ← readV2Suffix limits codec leaf frame info (bytesAt source spans.values)
  decodeV2Slots leaf info reps defs suffix start rowCeiling

structure V2PageWire (limits : Limits) (codec : ColumnCodec) (leaf : Leaf) (source : Bytes)
    (frame : Page.Frame) (start : State) (remaining rowCeiling : Nat) (decoded : DecodedPage) : Prop where
  original : ∃ (info : Page.DataV2) (spans : Page.V2Spans) (reps defs : List Nat)
      (checksum : Page.Checksum.Status) (checked : DecodedPage) (suffix : Bytes),
    frame.value.kind = .dataV2 info ∧ info.encoding = 0 ∧ info.numValues ≤ remaining ∧
    (codec.v2 info = 0 → frame.value.uncompressedSize = frame.value.compressedSize) ∧
    v2LevelBytes info ≤ frame.value.compressedSize ∧ v2LevelBytes info ≤ frame.value.uncompressedSize ∧
    Page.Checksum.verify limits.maxBodyBytes source frame = .ok checksum ∧ frame.v2Spans = some spans ∧
    (∀ span ∈ [spans.repetition, spans.definition, spans.values],
      source.slice? span.start (some span.stop) = some (bytesAt source span)) ∧
    V2LevelWire limits.levels leaf.maxRepetition info.numValues (bytesAt source spans.repetition) reps ∧
    V2LevelWire limits.levels leaf.maxDefinition info.numValues (bytesAt source spans.definition) defs ∧
    V2SuffixWire limits codec frame info (bytesAt source spans.values) suffix ∧
    reps.head?.getD 0 = 0 ∧ reps.count 0 = info.numRows ∧ absentSlots decoded = info.numNulls ∧
    decoded.levels.length = info.numValues ∧
    DecodedWire leaf reps defs suffix start rowCeiling checked ∧ decoded = closeV2 checked

def decodeDataPage (limits : Limits) (codec : ColumnCodec) (leaf : Leaf) (source : Bytes)
    (frame : Page.Frame) (start : State) (remaining rowCeiling : Nat) : Except PageCause DecodedPage :=
  match frame.value.kind with
  | .dataV2 _ => decodeV2Page limits codec leaf source frame start remaining rowCeiling
  | .dataV1 _ => decodeV1Page limits codec leaf source frame start remaining rowCeiling
  | kind => .error (.header (.pageKind kind))

inductive DataPageWire (limits : Limits) (codec : ColumnCodec) (leaf : Leaf) (source : Bytes)
    (frame : Page.Frame) (start : State) (remaining rowCeiling : Nat) (decoded : DecodedPage) : Prop where
  | v1 : PageWire limits leaf source frame start remaining rowCeiling decoded codec →
      DataPageWire limits codec leaf source frame start remaining rowCeiling decoded
  | v2 : V2PageWire limits codec leaf source frame start remaining rowCeiling decoded →
      DataPageWire limits codec leaf source frame start remaining rowCeiling decoded

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
  codec : ColumnCodec

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
      let decoded ← (decodeDataPage limits carrier.codec carrier.leaf carrier.bytes frame cursor.state
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
    (binding : Binding schema group column) (span : Footer.Span) : Carrier :=
  ⟨snapshot.bytes, span, binding.leaf, ⟨group, column, binding.leaf.site.location.path⟩,
    binding.chunk.metadata.numValues.toNat, binding.rowGroup.numRows.toNat, binding.codec⟩

/-- Parquet column sizes include each original header. The identity codec
already checks that the footer size agrees with the stored span. -/
def rawChunkBytes (carrier : Carrier) (pages : List ObservedPage) : Nat :=
  if carrier.codec = .uncompressed then carrier.span.stop - carrier.span.start
  else (pages.map fun page =>
    page.frame.header.stop - page.frame.header.start + page.frame.value.uncompressedSize).sum

def readFramed {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group column : Nat}
    (limits : Limits) (binding : Binding schema group column) (span : Footer.Span) : Except Error Observation :=
  let carrier := carrierOf binding span
  let bytes := carrier.span.stop - carrier.span.start
  let failed := Error.chunk carrier.address carrier.span
  if ¬ (carrier.span.start ≤ carrier.span.stop ∧ carrier.span.stop ≤ carrier.bytes.length)
    then .error (failed .bounds)
  else if bytes > limits.maxChunkBytes then .error (failed .chunkLimit)
  else if carrier.slots > limits.maxSlots then .error (failed (.slotLimit carrier.slots))
  else if carrier.rows > limits.maxRows then .error (failed (.rowLimit carrier.rows))
  else if carrier.codec = .uncompressed ∧ binding.chunk.metadata.totalUncompressedSize ≠ Int.ofNat bytes then
    .error (failed (.uncompressedSize binding.chunk.metadata.totalUncompressedSize bytes))
  else do
    let pages ← walk limits carrier limits.framing.maxPages (initial carrier) []
    let rawBytes := rawChunkBytes carrier pages
    if binding.chunk.metadata.totalUncompressedSize ≠ Int.ofNat rawBytes then
      throw (failed (.uncompressedSize binding.chunk.metadata.totalUncompressedSize rawBytes))
    return ⟨pages⟩

def read {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group column : Nat}
    (limits : Limits) (binding : Binding schema group column) : Except Error Observation :=
  match binding.storage with
  | .framed span _ _ => readFramed limits binding span
  | .pageless _ => .ok ⟨[]⟩

inductive ChainWire (limits : Limits) (carrier : Carrier) : Cursor → Cursor → List ObservedPage → Prop where
  | nil (cursor : Cursor) : ChainWire limits carrier cursor cursor []
  | more {start stop first rest} :
      Page.readPage limits.framing carrier.bytes carrier.span start.byte = .ok first.frame →
      first.start = start →
      DataPageWire limits carrier.codec carrier.leaf carrier.bytes first.frame start.state
        (carrier.slots - start.state.slot) carrier.rows first.decoded →
      ChainWire limits carrier (start.advance first) stop rest →
      ChainWire limits carrier start stop (first :: rest)

structure FramedWire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group column : Nat}
    (limits : Limits) (binding : Binding schema group column) (span : Footer.Span)
    (output : Observation) : Prop where
  bounds : span.start ≤ span.stop ∧ span.stop ≤ snapshot.bytes.length
  chunkCap : span.stop - span.start ≤ limits.maxChunkBytes
  slotCap : binding.chunk.metadata.numValues.toNat ≤ limits.maxSlots
  rowCap : binding.rowGroup.numRows.toNat ≤ limits.maxRows
  pageCap : output.pages.length ≤ limits.framing.maxPages
  uncompressed : binding.chunk.metadata.totalUncompressedSize = Int.ofNat (rawChunkBytes (carrierOf binding span) output.pages)
  chain : ∃ stop : Cursor, stop.byte = span.stop ∧
    stop.state.slot = binding.chunk.metadata.numValues.toNat ∧
    stop.state.rows = binding.rowGroup.numRows.toNat ∧
    ChainWire limits (carrierOf binding span) (initial (carrierOf binding span)) stop output.pages
  frames : Page.Chain span span.start span.stop (output.pages.map ObservedPage.frame)
  slots : output.levels.length = binding.chunk.metadata.numValues.toNat
  rows : output.levels.countP LevelSlot.startsRow = binding.rowGroup.numRows.toNat

structure Wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group column : Nat}
    (limits : Limits) (binding : Binding schema group column) (output : Observation) : Prop where
  slots : output.levels.length = binding.chunk.metadata.numValues.toNat
  rows : output.levels.countP LevelSlot.startsRow = binding.rowGroup.numRows.toNat
  storage : match binding.storage with
    | .framed span _ _ => FramedWire limits binding span output
    | .pageless _ => output.pages = [] ∧
        Page.columnSpan snapshot.footer.start binding.chunk.metadata = none

end

end Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk
