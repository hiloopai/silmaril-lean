module

public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Rows.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Defs

/-! Original unindexed V1/V2 pages for one canonical LIST path. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Chunk

open RecursiveSchema.Chunk (Address)
open Repeated.Chunk (LevelBlock LevelCause bitWidth)

@[expose] public section

structure Limits extends RecursiveSchema.Chunk.Limits where
  maxSlots : Nat := 1024 * 1024
  indices : Hybrid.Limits := ({} : Repeated.Chunk.Limits).indices
  maxDictionaryEntries : Nat := ({} : Repeated.Chunk.Limits).maxDictionaryEntries
  maxDictionaryBytes : Nat := ({} : Repeated.Chunk.Limits).maxDictionaryBytes
  /-- Controller calls per reached GZIP member. -/
  gzipCalls : Nat := ({} : Repeated.Chunk.Limits).gzipCalls
  /-- Window and command bounds for one dictionary-free Zstandard frame. -/
  zstd : FlatColumn.Zstd.CompressionLimits := ({} : Repeated.Chunk.Limits).zstd

def Limits.logical (limits : Limits) : Rows.Limits := ⟨limits.maxRows, limits.maxSlots⟩

def Limits.payload (limits : Limits) : Repeated.Chunk.Limits :=
  { toLimits := limits.toLimits, indices := limits.indices, gzipCalls := limits.gzipCalls, zstd := limits.zstd,
    maxDictionaryEntries := limits.maxDictionaryEntries, maxDictionaryBytes := limits.maxDictionaryBytes }

inductive Codec where
  | uncompressed
  | snappy
  | gzip
  | zstd
  | lz4Raw
  deriving DecidableEq, Repr

def Codec.ofId : Int → Option Codec
  | 0 => some .uncompressed
  | 1 => some .snappy
  | 2 => some .gzip
  | 6 => some .zstd
  | 7 => some .lz4Raw
  | _ => none

def Codec.column : Codec → Repeated.Chunk.ColumnCodec
  | .uncompressed => .uncompressed
  | .snappy => .snappy
  | .gzip => .gzip
  | .zstd => .zstd
  | .lz4Raw => .lz4Raw

inductive BindCause where
  | columns (actual : Nat)
  | association
  | codec (actual : Int)
  | encodings (actual : List Int)
  | pageOffsets
  | pageIndex
  | counts
  | span
  deriving DecidableEq, Repr

inductive BindError where
  | group (ordinal : Nat)
  | column (address : Address) (cause : BindCause)
  deriving DecidableEq, Repr

inductive ColumnEncoding (metadata : Footer.ColumnMetadata) where
  | plain : RecursiveSchema.SupportedEncodings metadata → metadata.dictionaryPageOffset = none →
      ColumnEncoding metadata
  | dictionary : Repeated.Chunk.DictionaryEncodings metadata → metadata.codec = 0 →
      ColumnEncoding metadata

structure Binding {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (schema : Compiled schemaLimits snapshot) (group : Nat) where
  rowGroup : Footer.RowGroup
  column : Footer.ColumnChunk
  span : Footer.Span
  groupAt : snapshot.groupAt group = some rowGroup
  onlyColumn : rowGroup.columns = [column]
  path : column.metadata.pathInSchema = schema.plan.shape.leaf.1.location.path
  physical : column.metadata.physicalType = schema.plan.shape.leaf.2.physical
  codec : Codec
  originalCodec : Codec.ofId column.metadata.codec = some codec
  encodings : ColumnEncoding column.metadata
  offsets : column.metadata.indexPageOffset = none
  unindexed : Repeated.Chunk.Unindexed column
  counts : 0 ≤ column.metadata.numValues ∧ 0 ≤ rowGroup.numRows
  originalSpan : Page.columnSpan snapshot.footer.start column.metadata = some span

def address (plan : Plan) (group : Nat) : Address := ⟨group, 0, plan.shape.leaf.1.location.path⟩

end

private def lookup {α ε : Type} (option : Option α) (error : ε) :
    Except ε {value // option = some value} :=
  match option with
  | none => .error error
  | some value => .ok ⟨value, rfl⟩

private def checked {ε : Type} (condition : Prop) [Decidable condition] (error : ε) :
    Except ε (PLift condition) :=
  if yes : condition then .ok ⟨yes⟩ else .error error

private def bindEncoding (metadata : Footer.ColumnMetadata)
    (fail : BindCause → BindError) : Except BindError (ColumnEncoding metadata) := do
  if dictionary : Repeated.Chunk.DictionaryEncodings metadata then
    let ⟨codec⟩ ← checked (metadata.codec = 0) (fail (.codec metadata.codec))
    return .dictionary dictionary codec
  else
    let ⟨plain⟩ ← checked (RecursiveSchema.SupportedEncodings metadata) (fail (.encodings metadata.encodings))
    let ⟨offset⟩ ← checked (metadata.dictionaryPageOffset = none) (fail .pageOffsets)
    return .plain plain offset

public def bind {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (schema : Compiled schemaLimits snapshot) (group : Nat) : Except BindError (Binding schema group) := do
  let ⟨rowGroup, atGroup⟩ ← lookup (snapshot.groupAt group) (.group group)
  let fail := BindError.column (address schema.plan group)
  let ⟨column, onlyColumn⟩ ← match found : rowGroup.columns with
    | [column] => pure (⟨column, found⟩ : {column // rowGroup.columns = [column]})
    | _ => throw (fail (.columns rowGroup.columns.length))
  let metadata := column.metadata
  let leaf := schema.plan.shape.leaf
  let ⟨⟨path, physical⟩⟩ ← checked
    (metadata.pathInSchema = leaf.1.location.path ∧ metadata.physicalType = leaf.2.physical) (fail .association)
  let ⟨codec, originalCodec⟩ ← lookup (Codec.ofId metadata.codec) (fail (.codec metadata.codec))
  let encodings ← bindEncoding metadata fail
  let ⟨offsets⟩ ← checked (metadata.indexPageOffset = none) (fail .pageOffsets)
  let ⟨unindexed⟩ ← checked (Repeated.Chunk.Unindexed column) (fail .pageIndex)
  let ⟨counts⟩ ← checked (0 ≤ metadata.numValues ∧ 0 ≤ rowGroup.numRows) (fail .counts)
  let ⟨span, originalSpan⟩ ← lookup (Page.columnSpan snapshot.footer.start metadata) (fail .span)
  return ⟨rowGroup, column, span, atGroup, onlyColumn, path, physical, codec, originalCodec, encodings, offsets,
    unindexed, counts, originalSpan⟩

@[expose] public section

/-- Each entry is the original definition level at which a repeated
wrapper stops. A slot reaches that wrapper only above this level. -/
def wrappers (plan : Plan) : List Nat :=
  ((plan.shape.steps {}).zipIdx).filterMap fun (step, level) =>
    if step.wrapper?.isSome then some level else none

def reached (wrappers : List Nat) (definition : Nat) : Nat :=
  wrappers.countP (· < definition)

structure State where
  slots : Nat := 0
  rows : Nat := 0
  live : Nat := 0
  deriving DecidableEq, Repr

inductive LevelError where
  | repetition (slot actual maximum : Nat)
  | definition (slot actual maximum : Nat)
  | closedAncestor (slot repetition live : Nat)
  | unreachedAncestor (slot repetition reached : Nat)
  | rowOverrun (slot rows : Nat)
  deriving DecidableEq, Repr

def State.close (state : State) : State := { state with live := 0 }

def State.advance (start : State) (repetition live : Nat) : State :=
  ⟨start.slots + 1, start.rows + (repetition == 0).toNat, live⟩

def step (plan : Plan) (wrappers : List Nat) (ceiling : Nat) (start : State)
    (rep defn : Nat) : Except LevelError State :=
  if rep > plan.shape.repetitions then .error (.repetition start.slots rep plan.shape.repetitions)
  else if defn > plan.shape.definitions then .error (.definition start.slots defn plan.shape.definitions)
  else if rep > start.live then .error (.closedAncestor start.slots rep start.live)
  else
    let live := reached wrappers defn
    if rep > live then .error (.unreachedAncestor start.slots rep live)
    else
      let stop := start.advance rep live
      if stop.rows > ceiling then .error (.rowOverrun start.slots ceiling) else .ok stop

def scan (plan : Plan) (wrappers : List Nat) (ceiling : Nat) :
    List (Nat × Nat) → State → Except LevelError State
  | [], start => .ok start
  | (rep, defn) :: rest, start => do
    let stop ← step plan wrappers ceiling start rep defn
    scan plan wrappers ceiling rest stop

structure StepWire (plan : Plan) (wrappers : List Nat) (ceiling : Nat) (start : State)
    (rep defn : Nat) (stop : State) : Prop where
  repetition : rep ≤ plan.shape.repetitions
  definition : defn ≤ plan.shape.definitions
  openAncestor : rep ≤ start.live
  reachedAncestor : rep ≤ reached wrappers defn
  after : stop = start.advance rep (reached wrappers defn)
  rows : stop.rows ≤ ceiling

inductive ScanWire (plan : Plan) (wrappers : List Nat) (ceiling : Nat) :
    State → List (Nat × Nat) → State → Prop where
  | nil (state : State) : ScanWire plan wrappers ceiling state [] state
  | cons {start middle stop rep defn rest} :
      StepWire plan wrappers ceiling start rep defn middle →
      ScanWire plan wrappers ceiling middle rest stop →
      ScanWire plan wrappers ceiling start ((rep, defn) :: rest) stop

inductive SectionOrigin where
  | file
  | decodedBody
  deriving DecidableEq, Repr

/-- V1 level spans include their four-byte prefixes. Compressed V1 spans
are relative to the decoded body. V2 records the raw stored spans. -/
structure Sections where
  repetition : Footer.Span
  definition : Footer.Span
  values : Footer.Span
  origin : SectionOrigin := .file
  deriving DecidableEq, Repr

structure SectionSource where
  bytes : Bytes
  span : Footer.Span
  origin : SectionOrigin

def Codec.v1Source (codec : Codec) (source : Bytes) (frame : Page.Frame) (body : Bytes) : SectionSource :=
  match codec with
  | .uncompressed => ⟨source, frame.payload, .file⟩
  | _ => ⟨body, ⟨0, body.length⟩, .decodedBody⟩

def sections (input : SectionSource) (body : Bytes) (reps defs : LevelBlock) : Sections :=
  let definition := input.span.start + (body.length - reps.tail.length)
  let values := input.span.start + (body.length - defs.tail.length)
  ⟨⟨input.span.start, definition⟩, ⟨definition, values⟩, ⟨values, input.span.stop⟩, input.origin⟩

def Sections.ofV2 (spans : Page.V2Spans) : Sections :=
  ⟨spans.repetition, spans.definition, spans.values, .file⟩

inductive PageCause where
  | header (cause : RecursiveSchema.Chunk.Cause)
  | slotOverrun (remaining advertised : Nat)
  | checksum (cause : Page.Checksum.Error)
  | repetition (cause : LevelCause)
  | definition (cause : LevelCause)
  | level (cause : LevelError)
  | plain (cause : Plain.Error)
  | alignment (cause : FlatPage.Error)
  | dictionary (cause : Repeated.Chunk.PageCause)
  | dictionaryIndices (cause : DictionaryIndex.Error)
  | v1Payload (cause : Repeated.Chunk.PageCause)
  | v2 (cause : Repeated.Chunk.PageCause)
  deriving DecidableEq, Repr

def v1Error : Repeated.Chunk.PageCause → PageCause
  | .header cause => .header cause
  | .slotOverrun remaining advertised => .slotOverrun remaining advertised
  | .checksum cause => .checksum cause
  | cause => .v1Payload cause

structure Decoded where
  sections : Sections
  atoms : List Rows.Atom
  after : State
  deriving Repr

def atoms (levels : List (Nat × Nat)) (values : List (Option RecursiveSchema.Chunk.Word)) :
    List Rows.Atom :=
  levels.zipWith (fun (rep, defn) word => ⟨rep, defn, word⟩) values

def mask (plan : Plan) (definitions : List Nat) : List Bool :=
  definitions.map (· == plan.shape.definitions)

inductive ValueEncoding where
  | plain
  | dictionary (entries : Array RecursiveSchema.Chunk.Word)

def ValueEncoding.tag : ValueEncoding → Int
  | .plain => 0
  | .dictionary _ => 8

def ValueEncoding.read (limits : Limits) (kind : RecursiveSchema.Kind) (count : Nat)
    (suffix : Bytes) : ValueEncoding → Except PageCause (List RecursiveSchema.Chunk.Word)
  | .plain => (RecursiveSchema.Chunk.readWords kind count suffix).mapError .plain
  | .dictionary entries =>
    (DictionaryIndex.readValues limits.indices entries count suffix).mapError .dictionaryIndices

def ValueEncoding.signedExtent (plan : Plan) (info : Page.DataV2) : ValueEncoding → Option Nat
  | .plain => some ((info.numValues - info.numNulls) * RecursiveSchema.Chunk.wordWidth plan.shape.leaf.2)
  | .dictionary _ => none

def ValueEncoding.select (dictionary : Option Repeated.Chunk.Dictionary) (tag : Int) :
    Except PageCause ValueEncoding :=
  if tag = 8 then
    match dictionary with
    | some table => .ok (.dictionary table.entries)
    | none => .error (.dictionary .missingDictionary)
  else .ok .plain

/-- Both page versions scan ancestry independently of the value encoding. -/
def decodeSlots (plan : Plan) (wrappers : List Nat) (spans : Sections) (start : State)
    (ceiling : Nat) (reps defs : List Nat) (suffix : Bytes) (limits : Limits)
    (encoding : ValueEncoding := .plain) : Except PageCause Decoded := do
  let levels := reps.zip defs
  let stop ← (scan plan wrappers ceiling levels start).mapError .level
  let present := mask plan defs
  let words ← encoding.read limits plan.shape.leaf.2 (present.count true) suffix
  let aligned ← (FlatPage.reconstruct present words).mapError .alignment
  return ⟨spans, atoms levels aligned, stop⟩

def decodePage (limits : Limits) (plan : Plan) (wrappers : List Nat) (source : Bytes) (frame : Page.Frame)
    (start : State) (remaining ceiling : Nat) (codec : Codec := .uncompressed)
    (encoding : ValueEncoding := .plain) : Except PageCause Decoded := do
  let info ← (Repeated.Chunk.admitPage frame remaining codec.column encoding.tag).mapError v1Error
  let body ← (Repeated.Chunk.readV1Body limits.payload codec.column source frame).mapError v1Error
  let reps ← (Repeated.Chunk.readLevels limits.levels plan.shape.repetitions info.numValues body).mapError .repetition
  let defs ← (Repeated.Chunk.readLevels limits.levels plan.shape.definitions info.numValues reps.tail).mapError .definition
  decodeSlots plan wrappers (sections (codec.v1Source source frame body) body reps defs)
    start ceiling reps.levels defs.levels defs.tail limits encoding

def Decoded.close (decoded : Decoded) : Decoded := { decoded with after := decoded.after.close }

def absentSlots (decoded : Decoded) : Nat := decoded.atoms.countP (·.word.isNone)

/-- Check the original V2 header, stored body and raw level spans.
Only the value suffix enters the codec when the original flag is true.
A V2 page starts and ends with a closed ancestry cursor. -/
def decodeV2Page (limits : Limits) (plan : Plan) (wrappers : List Nat) (source : Bytes) (frame : Page.Frame)
    (start : State) (remaining ceiling : Nat) (codec : Codec := .uncompressed)
    (encoding : ValueEncoding := .plain) : Except PageCause Decoded := do
  let info ← (Repeated.Chunk.admitV2Page codec.column frame remaining encoding.tag).mapError .v2
  let parts ← (Repeated.Chunk.readV2SectionsWith limits.toLimits plan.shape.repetitions
    plan.shape.definitions source frame info).mapError .v2
  let stored := Repeated.Chunk.bytesAt source parts.spans.values
  let suffix ← (Repeated.Chunk.readV2SuffixWith limits.payload codec.column frame info stored
    (encoding.signedExtent plan info)).mapError .v2
  let decoded ← Repeated.Chunk.checkV2Counts info parts.repetitions start.slots PageCause.v2 absentSlots fun _ =>
    decodeSlots plan wrappers (.ofV2 parts.spans) start.close ceiling parts.repetitions parts.definitions suffix limits encoding
  return decoded.close

def decodeDataPage (limits : Limits) (plan : Plan) (wrappers : List Nat) (source : Bytes) (frame : Page.Frame)
    (start : State) (remaining ceiling : Nat) (codec : Codec := .uncompressed)
    (dictionary : Option Repeated.Chunk.Dictionary := none) : Except PageCause Decoded :=
  match frame.value.kind with
  | .dataV1 info => do
    let encoding ← ValueEncoding.select dictionary info.encoding
    decodePage limits plan wrappers source frame start remaining ceiling codec encoding
  | .dataV2 info => do
    let encoding ← ValueEncoding.select dictionary info.encoding
    decodeV2Page limits plan wrappers source frame start remaining ceiling codec encoding
  | .dictionary _ => .error (.dictionary .misplacedDictionary)
  | _ => decodePage limits plan wrappers source frame start remaining ceiling codec

def ValueEncoding.Wire (limits : Limits) (kind : RecursiveSchema.Kind) (count : Nat)
    (suffix : Bytes) (words : List RecursiveSchema.Chunk.Word) : ValueEncoding → Prop
  | .plain => ∃ physical : List (List UInt8),
      suffix.toList = physical.flatten ∧ physical.length = count ∧
      (∀ word ∈ physical, word.length = RecursiveSchema.Chunk.wordWidth kind) ∧
      words = physical.map (RecursiveSchema.Chunk.readWord kind)
  | .dictionary entries => DictionaryIndex.ValuesWire limits.indices entries count suffix words

inductive ValueEncoding.From (dictionary : Option Repeated.Chunk.Dictionary) : ValueEncoding → Prop where
  | plain : From dictionary .plain
  | dictionary {table : Repeated.Chunk.Dictionary} :
      dictionary = some table → From dictionary (.dictionary table.entries)

structure SlotsWire (plan : Plan) (wrappers : List Nat) (start : State) (ceiling : Nat)
    (reps defs : List Nat) (suffix : Bytes) (decoded : Decoded) (limits : Limits)
    (encoding : ValueEncoding := .plain) : Prop where
  original : ∃ aligned : List (Option RecursiveSchema.Chunk.Word),
    ScanWire plan wrappers ceiling start (reps.zip defs) decoded.after ∧
    encoding.Wire limits plan.shape.leaf.2 ((mask plan defs).count true) suffix (aligned.filterMap id) ∧
    aligned.map Option.isSome = mask plan defs ∧
    decoded.atoms = atoms (reps.zip defs) aligned

structure SectionsWire (limits : Hybrid.Limits) (plan : Plan) (count : Nat) (input : SectionSource)
    (spans : Sections) (repetitions definitions : List Nat) (suffix : Bytes) : Prop where
  original : ∃ repPrefix defPrefix repBytes defBytes : List UInt8,
    repPrefix.length = 4 ∧ defPrefix.length = 4 ∧
    KBytes.leVal repPrefix = repBytes.length ∧ KBytes.leVal defPrefix = defBytes.length ∧
    repBytes.length ≤ limits.bytes ∧ defBytes.length ≤ limits.bytes ∧
    Hybrid.Wire (bitWidth plan.shape.repetitions) count repBytes repetitions ∧
    Hybrid.Wire (bitWidth plan.shape.definitions) count defBytes definitions ∧
    spans.origin = input.origin ∧
    spans.repetition.start = input.span.start ∧ spans.repetition.stop = spans.definition.start ∧
    spans.definition.stop = spans.values.start ∧ spans.values.stop = input.span.stop ∧
    input.bytes.slice? spans.repetition.start (some spans.repetition.stop) =
      some (Bytes.ofList (repPrefix ++ repBytes)) ∧
    input.bytes.slice? spans.definition.start (some spans.definition.stop) =
      some (Bytes.ofList (defPrefix ++ defBytes)) ∧
    input.bytes.slice? spans.values.start (some spans.values.stop) = some suffix

structure PageWire (limits : Limits) (plan : Plan) (wrappers : List Nat) (source : Bytes) (frame : Page.Frame)
    (start : State) (remaining ceiling : Nat) (decoded : Decoded) (codec : Codec := .uncompressed)
    (encoding : ValueEncoding := .plain) : Prop where
  original : ∃ (info : Page.DataV1) (body : Bytes) (reps defs : LevelBlock),
    frame.value.kind = .dataV1 info ∧
    (info.encoding = encoding.tag ∧ info.definitionLevelEncoding = 3 ∧ info.repetitionLevelEncoding = 3) ∧
    info.numValues ≤ remaining ∧
    Repeated.Chunk.V1BodyWire limits.payload codec.column source frame body ∧
    SectionsWire limits.levels plan info.numValues (codec.v1Source source frame body)
      decoded.sections reps.levels defs.levels defs.tail ∧
    reps.levels.length = info.numValues ∧ defs.levels.length = info.numValues ∧
    SlotsWire plan wrappers start ceiling reps.levels defs.levels defs.tail decoded limits encoding

structure V2PageWire (limits : Limits) (plan : Plan) (wrappers : List Nat) (source : Bytes) (frame : Page.Frame)
    (start : State) (remaining ceiling : Nat) (decoded : Decoded) (codec : Codec := .uncompressed)
    (encoding : ValueEncoding := .plain) : Prop where
  original : ∃ (info : Page.DataV2) (parts : Repeated.Chunk.V2Sections) (suffix : Bytes) (checked : Decoded),
    frame.value.kind = .dataV2 info ∧ info.encoding = encoding.tag ∧ info.numValues ≤ remaining ∧
    (codec.column.v2 info = 0 → frame.value.uncompressedSize = frame.value.compressedSize) ∧
    Repeated.Chunk.V2SectionsWireWith limits.toLimits plan.shape.repetitions plan.shape.definitions
      source frame info parts ∧
    Repeated.Chunk.V2SuffixWire limits.payload codec.column frame info
      (Repeated.Chunk.bytesAt source parts.spans.values) suffix ∧
    Repeated.Chunk.v2LevelBytes info + suffix.length = frame.value.uncompressedSize ∧
    parts.repetitions.head?.getD 0 = 0 ∧ parts.repetitions.count 0 = info.numRows ∧
    absentSlots decoded = info.numNulls ∧ decoded.sections = .ofV2 parts.spans ∧
    SlotsWire plan wrappers start.close ceiling parts.repetitions parts.definitions suffix checked limits encoding ∧
    decoded = checked.close

inductive DataPageWire (limits : Limits) (plan : Plan) (wrappers : List Nat) (source : Bytes) (frame : Page.Frame)
    (start : State) (remaining ceiling : Nat) (decoded : Decoded) (codec : Codec := .uncompressed)
    (dictionary : Option Repeated.Chunk.Dictionary := none) : Prop where
  | v1 {encoding : ValueEncoding} : encoding.From dictionary →
      PageWire limits plan wrappers source frame start remaining ceiling decoded codec encoding →
      DataPageWire limits plan wrappers source frame start remaining ceiling decoded codec dictionary
  | v2 {encoding : ValueEncoding} : encoding.From dictionary →
      V2PageWire limits plan wrappers source frame start remaining ceiling decoded codec encoding →
      DataPageWire limits plan wrappers source frame start remaining ceiling decoded codec dictionary

inductive ChunkCause where
  | chunkLimit
  | slotLimit
  | rowLimit
  | framing (cause : Page.Error)
  | storedSize (advertised : Int) (actual : Nat)
  | rawSize (advertised : Int) (actual : Nat)
  | slotCount (expected actual : Nat)
  | rowCount (expected actual : Nat)
  deriving DecidableEq, Repr

inductive Error where
  | chunk (address : Address) (span : Footer.Span) (cause : ChunkCause)
  | dictionary (address : Address) (ordinal byte : Nat) (cause : Repeated.Chunk.PageCause)
  | page (address : Address) (ordinal byte : Nat) (start : State) (cause : PageCause)
  deriving DecidableEq, Repr

structure ObservedPage where
  frame : Page.Frame
  start : State
  decoded : Decoded
  deriving Repr

structure Observation where
  pages : List ObservedPage
  stop : State
  dictionary : Option Repeated.Chunk.Dictionary := none
  deriving Repr

def Observation.frames (observed : Observation) : List Page.Frame :=
  (observed.dictionary.toList.map (·.frame)) ++ observed.pages.map ObservedPage.frame
def Observation.atoms (observed : Observation) : List Rows.Atom := observed.pages.flatMap (·.decoded.atoms)

structure Carrier where
  plan : Plan
  source : Bytes
  span : Footer.Span
  address : Address
  slots : Nat
  rows : Nat
  storedSize : Int
  rawSize : Int
  codec : Codec
  metadata : Footer.ColumnMetadata

def carrierOf {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} (binding : Binding schema group) : Carrier :=
  ⟨schema.plan, snapshot.bytes, binding.span, address schema.plan group, binding.column.metadata.numValues.toNat,
    binding.rowGroup.numRows.toNat, binding.column.metadata.totalCompressedSize,
    binding.column.metadata.totalUncompressedSize, binding.codec, binding.column.metadata⟩

def readPrefix (limits : Limits) (carrier : Carrier) (encoding : ColumnEncoding carrier.metadata)
    (frames : List Page.Frame) :
    Except Repeated.Chunk.DictionaryPrefixError (Option Repeated.Chunk.Dictionary × List Page.Frame) :=
  match encoding with
  | .plain _ _ => .ok (none, frames)
  | .dictionary _ _ => do
    let (table, rest) ← Repeated.Chunk.readFramedDictionary limits.payload carrier.plan.shape.leaf.2
      carrier.source carrier.span carrier.metadata frames .uncompressed
    return (some table, rest)

def decodeFrames (limits : Limits) (carrier : Carrier) (wrappers : List Nat)
    (dictionary : Option Repeated.Chunk.Dictionary) :
    List Page.Frame → Nat → State → List ObservedPage → Except Error Observation
  | [], _, finish, reversed => .ok ⟨reversed.reverse, finish, dictionary⟩
  | frame :: frames, ordinal, start, reversed => do
    let decoded ← (decodeDataPage limits carrier.plan wrappers carrier.source frame start
      (carrier.slots - start.slots) carrier.rows carrier.codec dictionary).mapError
        (.page carrier.address ordinal frame.header.start start)
    decodeFrames limits carrier wrappers dictionary frames (ordinal + 1) decoded.after (⟨frame, start, decoded⟩ :: reversed)

/-- Counts refer to the complete original frame chain. Both footer
sizes include each serialized page header. -/
def checkTotals (carrier : Carrier) (frames : List Page.Frame) (observed : Observation) : Except Error Observation :=
  let fail := Error.chunk carrier.address carrier.span
  if observed.stop.slots ≠ carrier.slots then .error (fail (.slotCount carrier.slots observed.stop.slots))
  else if observed.stop.rows ≠ carrier.rows then .error (fail (.rowCount carrier.rows observed.stop.rows))
  else
    let stored := Repeated.Chunk.storedChunkBytes frames
    let raw := Repeated.Chunk.rawChunkBytes frames
    if carrier.storedSize ≠ Int.ofNat stored then .error (fail (.storedSize carrier.storedSize stored))
    else if carrier.rawSize ≠ Int.ofNat raw then .error (fail (.rawSize carrier.rawSize raw))
    else .ok observed

/-- Each framed page advances one original body. The live LIST ancestry
belongs to the chunk, including across a V1 continuation. -/
def read {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat}
    (limits : Limits) (binding : Binding schema group) : Except Error Observation :=
  let carrier := carrierOf binding
  let bytes := carrier.span.stop - carrier.span.start
  let fail := Error.chunk carrier.address carrier.span
  if bytes > limits.maxChunkBytes then .error (fail .chunkLimit)
  else if carrier.slots > limits.maxSlots then .error (fail .slotLimit)
  else if carrier.rows > limits.maxRows then .error (fail .rowLimit)
  else do
    let frames ← (Page.readChunk limits.framing carrier.source carrier.span).mapError (fail ∘ .framing)
    let (dictionary, data) ← (readPrefix limits carrier binding.encodings frames).mapError fun cause =>
      Error.dictionary carrier.address cause.ordinal cause.byte cause.cause
    let observed ← decodeFrames limits carrier (wrappers carrier.plan) dictionary data dictionary.isSome.toNat {} []
    checkTotals carrier frames observed

inductive ChainWire (limits : Limits) (carrier : Carrier) (dictionary : Option Repeated.Chunk.Dictionary) :
    State → State → List ObservedPage → Prop where
  | nil (state : State) : ChainWire limits carrier dictionary state state []
  | cons {start stop frame decoded rest} :
      DataPageWire limits carrier.plan (wrappers carrier.plan) carrier.source frame start
        (carrier.slots - start.slots) carrier.rows decoded carrier.codec dictionary →
      ChainWire limits carrier dictionary decoded.after stop rest →
      ChainWire limits carrier dictionary start stop (⟨frame, start, decoded⟩ :: rest)

inductive PrefixWire (limits : Limits) (carrier : Carrier) :
    Option Repeated.Chunk.Dictionary → List Page.Frame → List Page.Frame → Prop where
  | plain {frames} : carrier.metadata.dictionaryPageOffset = none →
      PrefixWire limits carrier none frames frames
  | dictionary {table : Repeated.Chunk.Dictionary} {frames} :
      carrier.metadata.codec = 0 →
      table.codec = .uncompressed →
      carrier.metadata.dictionaryPageOffset = some (Int.ofNat carrier.span.start) →
      carrier.metadata.dataPageOffset = Int.ofNat table.frame.payload.stop →
      table.frame.payload.stop < carrier.span.stop →
      Repeated.Chunk.DictionaryContentsWire limits.payload carrier.plan.shape.leaf.2 carrier.source table →
      PrefixWire limits carrier (some table) (table.frame :: frames) frames

/-- A payload or slot refusal comes from the next original frame after
the complete checked page prefix, with its original absolute header offset. -/
structure PageFailureWire (limits : Limits) (carrier : Carrier) (address : Address)
    (ordinal byte : Nat) (start : State) (cause : PageCause) : Prop where
  column : address = carrier.address
  original : ∃ (dictionary : Option Repeated.Chunk.Dictionary) (frames : List Page.Frame)
      (completed : List ObservedPage) (frame : Page.Frame) (rest : List Page.Frame),
    Page.readChunk limits.framing carrier.source carrier.span = .ok frames ∧
    PrefixWire limits carrier dictionary frames (completed.map ObservedPage.frame ++ frame :: rest) ∧
    Page.readPage limits.framing carrier.source carrier.span byte = .ok frame ∧
    ChainWire limits carrier dictionary {} start completed ∧
    ordinal = dictionary.isSome.toNat + completed.length ∧ byte = frame.header.start ∧
    decodeDataPage limits carrier.plan (wrappers carrier.plan) carrier.source frame start
      (carrier.slots - start.slots) carrier.rows carrier.codec dictionary = .error cause

/-- A dictionary refusal comes from the original leading frame or its
metadata anchors, before any data slot is consumed. -/
structure DictionaryFailureWire (limits : Limits) (carrier : Carrier)
    (encoding : ColumnEncoding carrier.metadata) (address : Address)
    (ordinal byte : Nat) (cause : Repeated.Chunk.PageCause) : Prop where
  column : address = carrier.address
  original : ∃ frames,
    Page.readChunk limits.framing carrier.source carrier.span = .ok frames ∧
    readPrefix limits carrier encoding frames = .error ⟨ordinal, byte, cause⟩

structure Wire (limits : Limits) (carrier : Carrier) (observed : Observation) : Prop where
  framed : Page.readChunk limits.framing carrier.source carrier.span = .ok observed.frames
  pages : Page.Chain carrier.span carrier.span.start carrier.span.stop observed.frames
  leading : PrefixWire limits carrier observed.dictionary observed.frames (observed.pages.map ObservedPage.frame)
  checked : ChainWire limits carrier observed.dictionary {} observed.stop observed.pages
  slotCount : observed.stop.slots = carrier.slots
  rowCount : observed.stop.rows = carrier.rows
  stored : carrier.storedSize = Int.ofNat (Repeated.Chunk.storedChunkBytes observed.frames)
  raw : carrier.rawSize = Int.ofNat (Repeated.Chunk.rawChunkBytes observed.frames)
  byteLimit : carrier.span.stop - carrier.span.start ≤ limits.maxChunkBytes
  slotLimit : carrier.slots ≤ limits.maxSlots
  rowLimit : carrier.rows ≤ limits.maxRows

end

end Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Chunk
