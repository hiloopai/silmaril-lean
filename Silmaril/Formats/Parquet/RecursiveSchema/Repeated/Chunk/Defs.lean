module

public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.Chunk.Defs
public import Silmaril.Formats.Parquet.FlatColumn.Zstd.Defs
public import Silmaril.Formats.Parquet.ScalarPage.BrotliRaw.Defs
public import Silmaril.Formats.Parquet.DictionaryIndex.Defs

/-! Checked unindexed PLAIN V1/V2 and dictionary-first V1/V2 chunks with identity, Snappy, GZIP or LZ4_RAW,
with at most one repeated ancestor and independent bounds on slots and row starts. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk

open RecursiveSchema (SupportedEncodings)
open Repeated (Compiled Leaf LevelError)

@[expose] public section

abbrev Address := RecursiveSchema.Chunk.Address
abbrev Word := RecursiveSchema.Chunk.Word

structure Limits extends RecursiveSchema.Chunk.Limits where
  maxSlots : Nat := 1024 * 1024
  maxDictionaryEntries : Nat := 1024 * 1024
  maxDictionaryBytes : Nat := 4 * 1024 * 1024
  indices : Hybrid.Limits := ⟨1024 * 1024, 16 * 1024 * 1024⟩
  /-- Controller calls per reached GZIP member, independent of stored and raw bytes. -/
  gzipCalls : Nat := 65536
  zstd : FlatColumn.Zstd.CompressionLimits := ⟨8 * 1024 * 1024, 43690⟩
  /-- Opt in to codec 4 with explicit raw-stream window and meta-block caps. -/
  brotliRaw : Option ScalarPage.BrotliRaw.Limits := none

/-- This profile uses neither offset indexes nor column indexes. Only V1
can continue a row across pages. -/
def Unindexed (chunk : Footer.ColumnChunk) : Prop :=
  chunk.offsetIndexOffset = none ∧ chunk.offsetIndexLength = none ∧
    chunk.columnIndexOffset = none ∧ chunk.columnIndexLength = none

instance (chunk : Footer.ColumnChunk) : Decidable (Unindexed chunk) := by
  unfold Unindexed
  infer_instance

/-- The column codecs admitted by the recursive profile. GZIP uses one member. -/
inductive ColumnCodec where
  | uncompressed
  | snappy
  | gzip
  | brotliRaw
  | zstd
  | lz4Raw
  deriving DecidableEq, Repr

def ColumnCodec.payload : ColumnCodec → Payload.Codec
  | .uncompressed => .uncompressed
  | .snappy => .snappy
  | .gzip => .gzip
  | .brotliRaw => .brotli
  | .zstd => .zstd
  | .lz4Raw => .lz4Raw

def ColumnCodec.id (codec : ColumnCodec) : Int :=
  codec.payload.id

def ColumnCodec.ofId : Int → Option ColumnCodec
  | 0 => some .uncompressed
  | 1 => some .snappy
  | 2 => some .gzip
  | 4 => some .brotliRaw
  | 6 => some .zstd
  | 7 => some .lz4Raw
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

/-- RLE_DICTIONARY data implies a leading PLAIN dictionary. The PLAIN
metadata tag also describes the dictionary body. -/
def DictionaryEncodings (metadata : Footer.ColumnMetadata) : Prop :=
  0 ∈ metadata.encodings ∧ 8 ∈ metadata.encodings ∧
    metadata.encodings.all (fun code => code == 0 || code == 3 || code == 8) = true

instance (metadata : Footer.ColumnMetadata) : Decidable (DictionaryEncodings metadata) := by
  unfold DictionaryEncodings
  infer_instance

/-- The codecs currently admitted for dictionary-first columns. -/
inductive DictionaryCodec where
  | uncompressed
  | snappy
  | gzip
  | brotliRaw
  | zstd
  | lz4Raw
  deriving DecidableEq, Repr

def DictionaryCodec.ofId : Int → Option DictionaryCodec
  | 0 => some .uncompressed
  | 1 => some .snappy
  | 2 => some .gzip
  | 4 => some .brotliRaw
  | 6 => some .zstd
  | 7 => some .lz4Raw
  | _ => none

def DictionaryCodec.column : DictionaryCodec → ColumnCodec
  | .uncompressed => .uncompressed
  | .snappy => .snappy
  | .gzip => .gzip
  | .brotliRaw => .brotliRaw
  | .zstd => .zstd
  | .lz4Raw => .lz4Raw

inductive FramedEncoding (metadata : Footer.ColumnMetadata) where
  | plain : SupportedEncodings metadata → metadata.dictionaryPageOffset = none →
      FramedEncoding metadata
  | dictionary : DictionaryEncodings metadata → (codec : DictionaryCodec) →
      DictionaryCodec.ofId metadata.codec = some codec → FramedEncoding metadata

/-- A pageless chunk retains its original metadata, but has no byte interval. -/
inductive Storage (snapshot : Snapshot.Checked) (rowGroup : Footer.RowGroup)
    (chunk : Footer.ColumnChunk) where
  | framed (span : Footer.Span)
      (encodings : FramedEncoding chunk.metadata)
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
  indexPageOffset : chunk.metadata.indexPageOffset = none
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
    (schema : Compiled schemaLimits snapshot) (group column : Nat) (limits : Limits := {}) :
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
  let _ ← check (codec ≠ .brotliRaw ∨ limits.brotliRaw.isSome) (fail (.codec metadata.codec))
  let ⟨indexPageOffset⟩ ← check (metadata.indexPageOffset = none) (fail .pageOffsets)
  let encodings ← if admitted : snapshot.admitsPageLessRecursive rowGroup = true then
      pure (Sum.inl (PLift.up admitted))
    else if metadata.dictionaryPageOffset.isSome || metadata.encodings.contains 8 then do
      let ⟨dictionaryCodec, original⟩ ← lookup (DictionaryCodec.ofId metadata.codec) (fail (.codec metadata.codec))
      let ⟨supported⟩ ← check (DictionaryEncodings metadata) (fail (.encodings metadata.encodings))
      pure (Sum.inr (.dictionary supported dictionaryCodec original))
    else do
      let ⟨supported⟩ ← check (SupportedEncodings metadata) (fail (.encodings metadata.encodings))
      let ⟨offset⟩ ← check (metadata.dictionaryPageOffset = none) (fail .pageOffsets)
      pure (Sum.inr (.plain supported offset))
  let ⟨unindexed⟩ ← check (Unindexed chunk) (fail .pageIndex)
  let ⟨counts⟩ ← check (0 ≤ metadata.numValues ∧ 0 ≤ rowGroup.numRows)
    (fail (.negativeCounts metadata.numValues rowGroup.numRows))
  let storage ← match encodings with
    | .inl admitted => pure (.pageless admitted.down)
    | .inr supported => do
      let ⟨span, original⟩ ← lookup (Page.columnSpan snapshot.footer.start metadata) (fail .span)
      pure (.framed span supported original)
  return ⟨leaf, rowGroup, chunk, storage, leafAt, groupAt, chunkAt, path, physical, codec, originalCodec,
    indexPageOffset, unindexed, counts⟩

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
  | missingDictionary
  | misplacedDictionary
  | dictionaryOffset (declared : Int)
  | dataOffset (declared : Int) (actual : Nat)
  | dictionaryEncoding (actual : Int)
  | dictionaryEntryLimit (count : Nat)
  | dictionaryByteLimit (count : Nat)
  | dictionaryRawByteLimit (count : Nat)
  | dictionaryIndices (original : DictionaryIndex.Error)
  | v2Encoding (actual : Int)
  | v2Extent
  | v2SignedExtent (declared expected : Nat)
  | payload (original : Payload.Error)
  | zstd (original : FlatColumn.Zstd.Error)
  | brotli (original : ScalarPage.BrotliRaw.Error)
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

def admitPage (frame : Page.Frame) (remaining : Nat) (codec : ColumnCodec := .uncompressed)
    (encoding : Int := 0) : Except PageCause Page.DataV1 :=
  (RecursiveSchema.Chunk.admitPageWith (codec == .uncompressed) frame remaining encoding).mapError fun
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

def decodePayload (limits : Limits) (codec : ColumnCodec) (bounds : Payload.Bounds)
    (stored : Bytes) : Except PageCause Bytes :=
  if codec = .brotliRaw then
    match limits.brotliRaw with
    | none => .error (.brotli (.codec codec.id))
    | some profile =>
      ((ScalarPage.BrotliRaw.decodePayload profile bounds stored.toList).mapError .brotli).map Bytes.ofList
  else if codec = .zstd then
    ((FlatColumn.Zstd.decodePayload limits.zstd bounds codec.id stored.toList).mapError .zstd).map Bytes.ofList
  else ((Payload.decode bounds codec.id stored.toList).mapError .payload).map Bytes.ofList

/-- The checked Brotli and Zstd adapters retain their own wire relations.
The shared scalar codecs retain their payload denotations. -/
def CodecWire (limits : Limits) (codec : ColumnCodec) (bounds : Payload.Bounds)
    (stored body : Bytes) : Prop :=
  if codec = .brotliRaw then
    ∃ profile, limits.brotliRaw = some profile ∧
      ScalarPage.BrotliRaw.PayloadWire profile bounds stored.toList body.toList
  else if codec = .zstd then FlatColumn.Zstd.PayloadWire limits.zstd bounds codec.id stored.toList body.toList
  else Payload.Decodes bounds.expectedSize codec.payload stored.toList body.toList

def v1BodyBounds (limits : Limits) (frame : Page.Frame) : Payload.Bounds :=
  ⟨frame.value.compressedSize, limits.maxBodyBytes, frame.value.uncompressedSize,
    limits.maxBodyBytes, limits.gzipCalls⟩

/-- The serialized V1 body, including each level prefix, uses the column
codec. Verify the stored frame before extracting bytes or expanding it. -/
def readV1Body (limits : Limits) (codec : ColumnCodec) (source : Bytes) (frame : Page.Frame) :
    Except PageCause Bytes := do
  let _ ← (Page.Checksum.verify limits.maxBodyBytes source frame).mapError .checksum
  let stored := Page.Checksum.payloadBytes source frame
  match codec with
  | .uncompressed => return stored
  | .snappy | .gzip | .brotliRaw | .zstd | .lz4Raw => decodePayload limits codec (v1BodyBounds limits frame) stored

structure V1BodyWire (limits : Limits) (codec : ColumnCodec) (source : Bytes) (frame : Page.Frame)
    (body : Bytes) : Prop where
  original : ∃ stored checksum,
    Page.Checksum.verify limits.maxBodyBytes source frame = .ok checksum ∧
    source.slice? frame.payload.start (some frame.payload.stop) = some stored ∧
    stored.length = frame.value.compressedSize ∧ stored.length ≤ limits.maxBodyBytes ∧
    body.length = frame.value.uncompressedSize ∧ body.length ≤ limits.maxBodyBytes ∧
    CodecWire limits codec (v1BodyBounds limits frame) stored body ∧
    (codec ≠ .uncompressed → decodePayload limits codec (v1BodyBounds limits frame) stored = .ok body)

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

def admitV2Page (codec : ColumnCodec) (frame : Page.Frame) (remaining : Nat)
    (encoding : Int := 0) : Except PageCause Page.DataV2 :=
  match frame.value.kind with
  | .dataV2 info =>
    if info.encoding ≠ encoding then .error (.v2Encoding info.encoding)
    else if codec.v2 info = 0 ∧ frame.value.uncompressedSize ≠ frame.value.compressedSize then
      .error (.header (.pageSizes frame.value.uncompressedSize frame.value.compressedSize))
    else if info.numValues > remaining then .error (.slotOverrun remaining info.numValues)
    else .ok info
  | kind => .error (.header (.pageKind kind))

/-- Check the V2 row boundary and counts around either signed value decoder.
Delay the decoder until after the original repetition checks. -/
def checkV2Slots (info : Page.DataV2) (reps : List Nat) (start : State)
    (decode : Unit → Except PageCause DecodedPage) : Except PageCause DecodedPage :=
  let first := reps.head?.getD 0
  let rows := reps.count 0
  if first ≠ 0 then .error (.v2RowBoundary start.slot first)
  else if rows ≠ info.numRows then .error (.v2Rows info.numRows rows)
  else do
    let checked ← decode ()
    let nulls := absentSlots checked
    if nulls ≠ info.numNulls then .error (.v2Nulls info.numNulls nulls)
    else .ok (closeV2 checked)

def decodeV2Slots (leaf : Leaf) (info : Page.DataV2) (reps defs : List Nat) (suffix : Bytes)
    (start : State) (rowCeiling : Nat) : Except PageCause DecodedPage :=
  checkV2Slots info reps start fun _ => decodeSlots leaf reps defs suffix start rowCeiling

def v2LevelBytes (info : Page.DataV2) : Nat :=
  info.repetitionBytes + info.definitionBytes

def v2ValueBounds (limits : Limits) (frame : Page.Frame) (info : Page.DataV2) : Payload.Bounds :=
  let levels := v2LevelBytes info
  ⟨frame.value.compressedSize - levels, limits.maxBodyBytes,
    frame.value.uncompressedSize - levels, limits.maxBodyBytes - levels, limits.gzipCalls⟩

/-- Check both extents before subtracting the original raw level prefix.
Only the independently bounded stored value suffix enters the codec. -/
def readV2SuffixWith (limits : Limits) (codec : ColumnCodec) (frame : Page.Frame)
    (info : Page.DataV2) (stored : Bytes) (signedExtent : Option Nat) : Except PageCause Bytes := do
  let levels := v2LevelBytes info
  let bounds := v2ValueBounds limits frame info
  if levels > frame.value.compressedSize ∨ levels > frame.value.uncompressedSize then
    throw .v2Extent
  if codec.v2 info = 0 then
    if stored.length = bounds.expectedSize then return stored
    else throw .v2Extent
  else
    if frame.value.uncompressedSize > limits.maxBodyBytes then throw (.payload .outputLimit)
    if signedExtent.any (· != bounds.expectedSize) then
      throw (.v2SignedExtent bounds.expectedSize (signedExtent.getD 0))
    decodePayload limits codec bounds stored

def readV2Suffix (limits : Limits) (codec : ColumnCodec) (leaf : Leaf)
    (frame : Page.Frame) (info : Page.DataV2) (stored : Bytes) : Except PageCause Bytes :=
  readV2SuffixWith limits codec frame info stored
    (some ((info.numValues - info.numNulls) * RecursiveSchema.Chunk.wordWidth leaf.kind))

inductive V2SuffixWire (limits : Limits) (codec : ColumnCodec) (frame : Page.Frame)
    (info : Page.DataV2) (stored : Bytes) : Bytes → Prop where
  | raw : codec.v2 info = 0 → stored.length = (v2ValueBounds limits frame info).expectedSize →
      V2SuffixWire limits codec frame info stored stored
  | compressed {raw : Bytes} :
      info.isCompressed = true → codec.v2 info ≠ 0 →
      CodecWire limits codec (v2ValueBounds limits frame info) stored raw →
      stored.length = (v2ValueBounds limits frame info).compressedSize →
      raw.length = (v2ValueBounds limits frame info).expectedSize →
      frame.value.uncompressedSize ≤ limits.maxBodyBytes →
      decodePayload limits codec (v2ValueBounds limits frame info) stored = .ok raw →
      V2SuffixWire limits codec frame info stored raw

structure V2Sections where
  spans : Page.V2Spans
  repetitions : List Nat
  definitions : List Nat

/-- Check the original stored body CRC before interpreting any of its sections. -/
def readV2SectionsWith (limits : RecursiveSchema.Chunk.Limits) (maxRepetition maxDefinition : Nat)
    (source : Bytes) (frame : Page.Frame) (info : Page.DataV2) : Except PageCause V2Sections := do
  let _ ← (Page.Checksum.verify limits.maxBodyBytes source frame).mapError .checksum
  let some spans := frame.v2Spans | throw .v2Extent
  let reps ← (readV2Levels limits.levels maxRepetition info.numValues
    (bytesAt source spans.repetition)).mapError .repetition
  let defs ← (readV2Levels limits.levels maxDefinition info.numValues
    (bytesAt source spans.definition)).mapError .definition
  return ⟨spans, reps, defs⟩

def readV2Sections (limits : Limits) (leaf : Leaf) (source : Bytes) (frame : Page.Frame)
    (info : Page.DataV2) : Except PageCause V2Sections :=
  readV2SectionsWith limits.toLimits leaf.maxRepetition leaf.maxDefinition source frame info

structure V2SectionsWireWith (limits : RecursiveSchema.Chunk.Limits)
    (maxRepetition maxDefinition : Nat) (source : Bytes) (frame : Page.Frame)
    (info : Page.DataV2) (sections : V2Sections) : Prop where
  checksum : ∃ status, Page.Checksum.verify limits.maxBodyBytes source frame = .ok status
  spans : frame.v2Spans = some sections.spans
  slices : ∀ span ∈ [sections.spans.repetition, sections.spans.definition, sections.spans.values],
    source.slice? span.start (some span.stop) = some (bytesAt source span)
  repetitions : V2LevelWire limits.levels maxRepetition info.numValues
    (bytesAt source sections.spans.repetition) sections.repetitions
  definitions : V2LevelWire limits.levels maxDefinition info.numValues
    (bytesAt source sections.spans.definition) sections.definitions
  count : sections.repetitions.length = info.numValues

structure V2SectionsWire (limits : Limits) (leaf : Leaf) (source : Bytes) (frame : Page.Frame)
    (info : Page.DataV2) (sections : V2Sections) : Prop where
  checksum : ∃ status, Page.Checksum.verify limits.maxBodyBytes source frame = .ok status
  spans : frame.v2Spans = some sections.spans
  slices : ∀ span ∈ [sections.spans.repetition, sections.spans.definition, sections.spans.values],
    source.slice? span.start (some span.stop) = some (bytesAt source span)
  repetitions : V2LevelWire limits.levels leaf.maxRepetition info.numValues
    (bytesAt source sections.spans.repetition) sections.repetitions
  definitions : V2LevelWire limits.levels leaf.maxDefinition info.numValues
    (bytesAt source sections.spans.definition) sections.definitions
  count : sections.repetitions.length = info.numValues

/-- Use the resolved flag and original column codec for the PLAIN suffix. -/
def decodeV2Page (limits : Limits) (codec : ColumnCodec) (leaf : Leaf)
    (source : Bytes) (frame : Page.Frame) (start : State)
    (remaining rowCeiling : Nat) : Except PageCause DecodedPage := do
  let info ← admitV2Page codec frame remaining
  let sections ← readV2Sections limits leaf source frame info
  let suffix ← readV2Suffix limits codec leaf frame info (bytesAt source sections.spans.values)
  decodeV2Slots leaf info sections.repetitions sections.definitions suffix start rowCeiling

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

/-- An original PLAIN dictionary from one column. Entry order is wire order. -/
structure Dictionary where
  frame : Page.Frame
  entries : Array Word
  codec : DictionaryCodec
  deriving Repr

def readDictionary (limits : Limits) (leaf : Leaf) (source : Bytes) (frame : Page.Frame)
    (codec : DictionaryCodec := .uncompressed) : Except PageCause Dictionary := do
  let .dictionary info := frame.value.kind | throw .missingDictionary
  if info.encoding ≠ 0 then throw (.dictionaryEncoding info.encoding)
  else if info.numValues > limits.maxDictionaryEntries then throw (.dictionaryEntryLimit info.numValues)
  else if frame.value.compressedSize > limits.maxDictionaryBytes then
    throw (.dictionaryByteLimit frame.value.compressedSize)
  else if frame.value.uncompressedSize > limits.maxDictionaryBytes then
    throw (.dictionaryRawByteLimit frame.value.uncompressedSize)
  else if codec.column = .uncompressed ∧ frame.value.uncompressedSize ≠ frame.value.compressedSize then
    throw (.header (.pageSizes frame.value.uncompressedSize frame.value.compressedSize))
  else
    let body ← readV1Body limits codec.column source frame
    let entries ← (RecursiveSchema.Chunk.readWords leaf.kind info.numValues body).mapError .plain
    return ⟨frame, entries.toArray, codec⟩

structure DictionaryWire (limits : Limits) (leaf : Leaf) (source : Bytes)
    (dictionary : Dictionary) : Prop where
  original : ∃ (info : Page.Dictionary) (body : Bytes) (words : List (List UInt8)),
    dictionary.frame.value.kind = .dictionary info ∧ info.encoding = 0 ∧
    info.numValues ≤ limits.maxDictionaryEntries ∧
    dictionary.frame.value.compressedSize ≤ limits.maxDictionaryBytes ∧
    dictionary.frame.value.uncompressedSize ≤ limits.maxDictionaryBytes ∧
    V1BodyWire limits dictionary.codec.column source dictionary.frame body ∧
    body.toList = words.flatten ∧ words.length = info.numValues ∧
    (∀ word ∈ words, word.length = RecursiveSchema.Chunk.wordWidth leaf.kind) ∧
    dictionary.entries = (words.map (RecursiveSchema.Chunk.readWord leaf.kind)).toArray

def decodeDictionarySlots (limits : Limits) (leaf : Leaf) (dictionary : Array Word)
    (repetitions definitions : List Nat) (suffix : Bytes) (start : State) (rowCeiling : Nat) :
    Except PageCause DecodedPage := do
  let classified ← classifySlots leaf rowCeiling repetitions definitions start
  let mask := classified.levels.map LevelSlot.present
  let indices ← (DictionaryIndex.readIndices limits.indices (mask.count true) suffix).mapError .dictionaryIndices
  let words ← (DictionaryIndex.select dictionary indices).mapError .dictionaryIndices
  let aligned ← (FlatPage.reconstruct mask words).mapError .alignment
  return ⟨classified.levels, aligned, classified.after⟩

structure DictionarySlotsWire (limits : Limits) (leaf : Leaf) (dictionary : Array Word)
    (repetitions definitions : List Nat) (suffix : Bytes) (start : State) (rowCeiling : Nat)
    (decoded : DecodedPage) : Prop where
  slots : SlotsWire leaf rowCeiling repetitions definitions start decoded.levels decoded.after
  aligned : decoded.words.map Option.isSome = decoded.levels.map LevelSlot.present
  indices : ∃ (width : UInt8) (runs : List UInt8) (indices : List Nat),
    suffix.toList = width :: runs ∧ width.toNat ≤ 32 ∧ suffix.length ≤ limits.indices.bytes ∧
    (decoded.levels.map LevelSlot.present).count true ≤ limits.indices.values ∧
    (decoded.levels.map LevelSlot.present).count true < Hybrid.runLimit ∧
    Hybrid.Wire width.toNat ((decoded.levels.map LevelSlot.present).count true) runs indices ∧
    (∀ index ∈ indices, index < dictionary.size) ∧
    indices.map (fun index => dictionary[index]?) = (decoded.words.filterMap id).map some

def decodeDictionaryPage (limits : Limits) (leaf : Leaf) (dictionary : Array Word) (source : Bytes)
    (frame : Page.Frame) (start : State) (remaining rowCeiling : Nat)
    (codec : DictionaryCodec := .uncompressed) : Except PageCause DecodedPage := do
  let info ← admitPage frame remaining codec.column 8
  let body ← readV1Body limits codec.column source frame
  let reps ← (readLevels limits.levels leaf.maxRepetition info.numValues body).mapError .repetition
  let defs ← (readLevels limits.levels leaf.maxDefinition info.numValues reps.tail).mapError .definition
  decodeDictionarySlots limits leaf dictionary reps.levels defs.levels defs.tail start rowCeiling

structure DictionaryPageWire (limits : Limits) (leaf : Leaf) (dictionary : Array Word)
    (source : Bytes) (frame : Page.Frame) (start : State) (remaining rowCeiling : Nat)
    (decoded : DecodedPage) (codec : DictionaryCodec := .uncompressed) : Prop where
  original : ∃ (info : Page.DataV1) (body : Bytes) (reps defs : LevelBlock),
    frame.value.kind = .dataV1 info ∧
    (info.encoding = 8 ∧ info.definitionLevelEncoding = 3 ∧ info.repetitionLevelEncoding = 3) ∧
    info.numValues ≤ remaining ∧
    V1BodyWire limits codec.column source frame body ∧
    LevelWire limits.levels leaf.maxRepetition info.numValues body reps ∧
    LevelWire limits.levels leaf.maxDefinition info.numValues reps.tail defs ∧
    DictionarySlotsWire limits leaf dictionary reps.levels defs.levels defs.tail start rowCeiling decoded ∧
    decoded.levels.length = info.numValues

/-- V2 index streams have a header-sized suffix for either resolved flag.
The Hybrid reader checks the variable byte extent and value count. -/
def decodeV2DictionaryPage (limits : Limits) (leaf : Leaf) (dictionary : Array Word) (source : Bytes)
    (frame : Page.Frame) (start : State) (remaining rowCeiling : Nat)
    (codec : DictionaryCodec := .uncompressed) : Except PageCause DecodedPage := do
  let info ← admitV2Page codec.column frame remaining 8
  let sections ← readV2Sections limits leaf source frame info
  let suffix ← readV2SuffixWith limits codec.column frame info (bytesAt source sections.spans.values) none
  checkV2Slots info sections.repetitions start fun _ =>
    decodeDictionarySlots limits leaf dictionary sections.repetitions sections.definitions suffix start rowCeiling

structure V2DictionaryPageWire (limits : Limits) (leaf : Leaf) (dictionary : Array Word)
    (source : Bytes) (frame : Page.Frame) (start : State) (remaining rowCeiling : Nat)
    (decoded : DecodedPage) (codec : DictionaryCodec := .uncompressed) : Prop where
  original : ∃ (info : Page.DataV2) (sections : V2Sections) (checked : DecodedPage) (suffix : Bytes),
    frame.value.kind = .dataV2 info ∧ info.encoding = 8 ∧ info.numValues ≤ remaining ∧
    (codec.column.v2 info = 0 → frame.value.uncompressedSize = frame.value.compressedSize) ∧
    v2LevelBytes info ≤ frame.value.compressedSize ∧ v2LevelBytes info ≤ frame.value.uncompressedSize ∧
    V2SectionsWire limits leaf source frame info sections ∧
    V2SuffixWire limits codec.column frame info (bytesAt source sections.spans.values) suffix ∧
    sections.repetitions.head?.getD 0 = 0 ∧ sections.repetitions.count 0 = info.numRows ∧
    absentSlots decoded = info.numNulls ∧ decoded.levels.length = info.numValues ∧
    DictionarySlotsWire limits leaf dictionary sections.repetitions sections.definitions suffix start rowCeiling checked ∧
    decoded = closeV2 checked

/-- A chunk's leading dictionary remains available to every data page.
Each original data header selects the value decoder for that page. -/
def decodeDictionaryDataPage (limits : Limits) (leaf : Leaf) (dictionary : Array Word) (source : Bytes)
    (frame : Page.Frame) (start : State) (remaining rowCeiling : Nat)
    (codec : DictionaryCodec := .uncompressed) : Except PageCause DecodedPage :=
  match frame.value.kind with
  | .dataV1 info =>
    if info.encoding = 0 then decodeV1Page limits codec.column leaf source frame start remaining rowCeiling
    else decodeDictionaryPage limits leaf dictionary source frame start remaining rowCeiling codec
  | .dataV2 info =>
    if info.encoding = 0 then decodeV2Page limits codec.column leaf source frame start remaining rowCeiling
    else decodeV2DictionaryPage limits leaf dictionary source frame start remaining rowCeiling codec
  | kind => .error (.header (.pageKind kind))

inductive DictionaryDataPageWire (limits : Limits) (leaf : Leaf) (dictionary : Array Word)
    (source : Bytes) (frame : Page.Frame) (start : State) (remaining rowCeiling : Nat)
    (decoded : DecodedPage) (codec : DictionaryCodec := .uncompressed) : Prop where
  | plain : DataPageWire limits codec.column leaf source frame start remaining rowCeiling decoded →
      DictionaryDataPageWire limits leaf dictionary source frame start remaining rowCeiling decoded codec
  | v1 : DictionaryPageWire limits leaf dictionary source frame start remaining rowCeiling decoded codec →
      DictionaryDataPageWire limits leaf dictionary source frame start remaining rowCeiling decoded codec
  | v2 : V2DictionaryPageWire limits leaf dictionary source frame start remaining rowCeiling decoded codec →
      DictionaryDataPageWire limits leaf dictionary source frame start remaining rowCeiling decoded codec

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
  dictionary : Option Dictionary

def decodeFramedPage (limits : Limits) (carrier : Carrier) (frame : Page.Frame)
    (start : State) : Except PageCause DecodedPage :=
  match frame.value.kind with
  | .dictionary _ => .error .misplacedDictionary
  | _ =>
    let remaining := carrier.slots - start.slot
    match carrier.dictionary with
    | none => decodeDataPage limits carrier.codec carrier.leaf carrier.bytes frame start remaining carrier.rows
    | some dictionary =>
      decodeDictionaryDataPage limits carrier.leaf dictionary.entries carrier.bytes frame start
        remaining carrier.rows dictionary.codec

def FramedPageWire (limits : Limits) (carrier : Carrier) (frame : Page.Frame)
    (start : State) (decoded : DecodedPage) : Prop :=
  match carrier.dictionary with
  | none => DataPageWire limits carrier.codec carrier.leaf carrier.bytes frame start
      (carrier.slots - start.slot) carrier.rows decoded
  | some dictionary => DictionaryDataPageWire limits carrier.leaf dictionary.entries carrier.bytes frame start
      (carrier.slots - start.slot) carrier.rows decoded dictionary.codec

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
      let decoded ← (decodeFramedPage limits carrier frame cursor.state).mapError failed
      let page : ObservedPage := ⟨cursor, frame, decoded⟩
      walk limits carrier fuel (cursor.advance page) (page :: reversed)

structure Observation where
  pages : List ObservedPage
  dictionary : Option Dictionary
  deriving Repr

def Observation.frames (column : Observation) : List Page.Frame :=
  column.dictionary.toList.map (·.frame) ++ column.pages.map (·.frame)

def Observation.levels (column : Observation) : List LevelSlot :=
  column.pages.flatMap (·.decoded.levels)

def carrierOf {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group column : Nat}
    (binding : Binding schema group column) (span : Footer.Span)
    (dictionary : Option Dictionary := none) : Carrier :=
  ⟨snapshot.bytes, span, binding.leaf, ⟨group, column, binding.leaf.site.location.path⟩,
    binding.chunk.metadata.numValues.toNat, binding.rowGroup.numRows.toNat, binding.codec, dictionary⟩

/-- Parquet column sizes include each original header, including the dictionary. -/
def storedChunkBytes (frames : List Page.Frame) : Nat :=
  (frames.map fun frame => frame.header.stop - frame.header.start + frame.value.compressedSize).sum

def rawChunkBytes (frames : List Page.Frame) : Nat :=
  (frames.map fun frame => frame.header.stop - frame.header.start + frame.value.uncompressedSize).sum

/-- A dictionary occupies physical page ordinal zero but consumes no slots
or rows. Its stored end must coincide with the declared first data page. -/
def afterDictionary (dictionary : Dictionary) : Cursor := ⟨1, dictionary.frame.payload.stop, {}⟩

def readPrefix (limits : Limits) (carrier : Carrier) (metadata : Footer.ColumnMetadata)
    (encoding : FramedEncoding metadata) : Except Error (Option Dictionary) := do
  match encoding with
  | .plain _ _ => return none
  | .dictionary _ codec _ =>
    let cursor := initial carrier
    let failed := Error.page carrier.address cursor
    let some offset := metadata.dictionaryPageOffset | throw (failed .missingDictionary)
    if offset ≠ Int.ofNat cursor.byte then throw (failed (.dictionaryOffset offset))
    else if limits.framing.maxPages = 0 then throw (failed (.framing .pageLimit))
    else
      let frame ← (Page.readPage limits.framing carrier.bytes carrier.span cursor.byte).mapError
        (failed ∘ .framing)
      let dictionary ← (readDictionary limits carrier.leaf carrier.bytes frame codec).mapError failed
      if metadata.dataPageOffset ≠ Int.ofNat frame.payload.stop ∨ frame.payload.stop ≥ carrier.span.stop then
        throw (Error.page carrier.address (afterDictionary dictionary)
          (.dataOffset metadata.dataPageOffset frame.payload.stop))
      else return some dictionary

def prefixCursor (carrier : Carrier) (dictionary : Option Dictionary) : Cursor :=
  match dictionary with
  | none => initial carrier
  | some dictionary => afterDictionary dictionary

structure PrefixWire (limits : Limits) (carrier : Carrier) (metadata : Footer.ColumnMetadata)
    (dictionary : Dictionary) : Prop where
  codec : DictionaryCodec.ofId metadata.codec = some dictionary.codec
  offset : metadata.dictionaryPageOffset = some (Int.ofNat carrier.span.start)
  dataOffset : metadata.dataPageOffset = Int.ofNat dictionary.frame.payload.stop
  hasData : dictionary.frame.payload.stop < carrier.span.stop
  cap : 0 < limits.framing.maxPages
  frame : Page.readPage limits.framing carrier.bytes carrier.span carrier.span.start = .ok dictionary.frame
  words : DictionaryWire limits carrier.leaf carrier.bytes dictionary

def PrefixAdmission (limits : Limits) (carrier : Carrier) (metadata : Footer.ColumnMetadata) :
    Option Dictionary → Prop
  | none => metadata.dictionaryPageOffset = none
  | some dictionary => PrefixWire limits carrier metadata dictionary

def readFramed {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group column : Nat}
    (limits : Limits) (binding : Binding schema group column) (span : Footer.Span)
    (encoding : FramedEncoding binding.chunk.metadata) : Except Error Observation :=
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
    let dictionary ← readPrefix limits carrier binding.chunk.metadata encoding
    let start := prefixCursor carrier dictionary
    let pages ← walk limits (carrierOf binding span dictionary) (limits.framing.maxPages - start.page) start []
    let observed := Observation.mk pages dictionary
    let rawBytes := rawChunkBytes observed.frames
    if binding.chunk.metadata.totalUncompressedSize ≠ Int.ofNat rawBytes then
      throw (failed (.uncompressedSize binding.chunk.metadata.totalUncompressedSize rawBytes))
    return observed

def read {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group column : Nat}
    (limits : Limits) (binding : Binding schema group column) : Except Error Observation :=
  match binding.storage with
  | .framed span encoding _ => readFramed limits binding span encoding
  | .pageless _ => .ok ⟨[], none⟩

inductive ChainWire (limits : Limits) (carrier : Carrier) : Cursor → Cursor → List ObservedPage → Prop where
  | nil (cursor : Cursor) : ChainWire limits carrier cursor cursor []
  | more {start stop first rest} :
      Page.readPage limits.framing carrier.bytes carrier.span start.byte = .ok first.frame →
      first.start = start →
      FramedPageWire limits carrier first.frame start.state first.decoded →
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
  pageCap : output.frames.length ≤ limits.framing.maxPages
  leading : PrefixAdmission limits (carrierOf binding span) binding.chunk.metadata output.dictionary
  uncompressed : binding.chunk.metadata.totalUncompressedSize = Int.ofNat (rawChunkBytes output.frames)
  chain : ∃ stop : Cursor, stop.byte = span.stop ∧
    stop.state.slot = binding.chunk.metadata.numValues.toNat ∧
    stop.state.rows = binding.rowGroup.numRows.toNat ∧
    ChainWire limits (carrierOf binding span output.dictionary)
      (prefixCursor (carrierOf binding span) output.dictionary) stop output.pages
  frames : Page.Chain span span.start span.stop output.frames
  slots : output.levels.length = binding.chunk.metadata.numValues.toNat
  rows : output.levels.countP LevelSlot.startsRow = binding.rowGroup.numRows.toNat

structure Wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group column : Nat}
    (limits : Limits) (binding : Binding schema group column) (output : Observation) : Prop where
  slots : output.levels.length = binding.chunk.metadata.numValues.toNat
  rows : output.levels.countP LevelSlot.startsRow = binding.rowGroup.numRows.toNat
  storage : match binding.storage with
    | .framed span _ _ => FramedWire limits binding span output
    | .pageless _ => output.dictionary = none ∧ output.pages = [] ∧
        Page.columnSpan snapshot.footer.start binding.chunk.metadata = none

end

end Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk
