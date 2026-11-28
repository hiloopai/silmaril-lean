module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Defs

/-! Bounded, unindexed PLAIN V1/V2 for one two-LIST leaf with checked column codecs.
Each codec admits one leading PLAIN dictionary. V1 carries live ancestry
across pages. V2 covers complete rows. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Chunk

@[expose] public section
abbrev Address := RecursiveSchema.Chunk.Address
abbrev Word := RecursiveSchema.Chunk.Word

structure Limits extends RecursiveSchema.Chunk.Limits where
  maxSlots : Nat := 1024 * 1024
  /-- Controller calls per reached GZIP member. -/
  gzipCalls : Nat := ({} : Repeated.Chunk.Limits).gzipCalls
  /-- Window and command bounds for one checked dictionary-free Zstd frame. -/
  zstd : FlatColumn.Zstd.CompressionLimits := ({} : Repeated.Chunk.Limits).zstd
  maxDictionaryEntries : Nat := ({} : Repeated.Chunk.Limits).maxDictionaryEntries
  maxDictionaryBytes : Nat := ({} : Repeated.Chunk.Limits).maxDictionaryBytes
  indices : Hybrid.Limits := ({} : Repeated.Chunk.Limits).indices

def Limits.payload (limits : Limits) : Repeated.Chunk.Limits :=
  { toLimits := limits.toLimits, gzipCalls := limits.gzipCalls, zstd := limits.zstd
    maxDictionaryEntries := limits.maxDictionaryEntries, maxDictionaryBytes := limits.maxDictionaryBytes
    indices := limits.indices }

/-- LZ4 uses codec 7 and a raw block. GZIP uses one member and Zstd uses one checked dictionary-free frame. -/
inductive Codec where
  | uncompressed | snappy | gzip | zstd | lz4Raw
  deriving DecidableEq, Repr

def Codec.ofId : Int → Option Codec
  | 0 => some .uncompressed
  | 1 => some .snappy
  | 2 => some .gzip
  | 6 => some .zstd
  | 7 => some .lz4Raw
  | _ => none

def Codec.dictionary : Codec → Repeated.Chunk.DictionaryCodec
  | .uncompressed => .uncompressed
  | .snappy => .snappy
  | .gzip => .gzip
  | .zstd => .zstd
  | .lz4Raw => .lz4Raw

def Codec.column (codec : Codec) : Repeated.Chunk.ColumnCodec :=
  codec.dictionary.column

inductive Live where
  | closed | outer | inner
  deriving DecidableEq, Repr

def Presence.live : TwoList.Presence → Live
  | .nullOuter | .emptyOuter => .closed
  | .nullInner | .emptyInner => .outer
  | .nullValue | .value => .inner

inductive Position where
  | rowStart | innerStart | innerContinue
  deriving DecidableEq, Repr

def Position.ofRep : Nat → Option Position
  | 0 => some .rowStart
  | 1 => some .innerStart
  | 2 => some .innerContinue
  | _ => none

def Position.admits : Position → Live → Bool
  | .rowStart, _ => true
  | .innerStart, live => live != .closed
  | .innerContinue, live => live == .inner

structure Slot where
  repetition : Nat
  definition : Nat
  position : Position
  presence : TwoList.Presence
  deriving DecidableEq, Repr

def Slot.present (slot : Slot) : Bool := slot.presence == .value

def Slot.startsRow (slot : Slot) : Bool := slot.position == .rowStart

structure State where
  slots : Nat := 0
  rows : Nat := 0
  live : Live := .closed
  deriving DecidableEq, Repr

/-- Start with the liveness of this slot, discarding any inner List from a
previous inner element or row. -/
def State.consume (start : State) (slot : Slot) : State :=
  ⟨start.slots + 1, start.rows + slot.startsRow.toNat, Presence.live slot.presence⟩

inductive LevelError where
  | repetition (slot actual : Nat)
  | definition (slot actual maximum : Nat)
  | closedAncestor (slot repetition : Nat) (live : Live)
  | unreachedAncestor (slot repetition definition : Nat)
  | rowLimit (slot ceiling : Nat)
  | levelCount (slot : Nat)
  deriving DecidableEq, Repr

def step (plan : Plan) (ceiling : Nat) (start : State) (rep defn : Nat) :
    Except LevelError Slot := do
  let some position := Position.ofRep rep | throw (.repetition start.slots rep)
  let some presence := plan.presence defn | throw (.definition start.slots defn plan.maxDefinition)
  let slot : Slot := ⟨rep, defn, position, presence⟩
  if !position.admits start.live then throw (.closedAncestor start.slots rep start.live)
  else if !position.admits (Presence.live presence) then throw (.unreachedAncestor start.slots rep defn)
  else if ceiling < (start.consume slot).rows then throw (.rowLimit start.slots ceiling)
  else return slot

structure StepWire (plan : Plan) (ceiling : Nat) (start : State) (slot : Slot) : Prop where
  position : Position.ofRep slot.repetition = some slot.position
  definition : DefinitionWire plan slot.definition slot.presence
  incoming : slot.position.admits start.live = true
  current : slot.position.admits (Presence.live slot.presence) = true
  rows : (start.consume slot).rows ≤ ceiling

inductive SlotsWire (plan : Plan) (ceiling : Nat) :
    State → List Nat → List Nat → List Slot → State → Prop where
  | nil (start : State) : SlotsWire plan ceiling start [] [] [] start
  | cons {start slot reps defs tail stop} :
      StepWire plan ceiling start slot →
      SlotsWire plan ceiling (start.consume slot) reps defs tail stop →
      SlotsWire plan ceiling start (slot.repetition :: reps) (slot.definition :: defs) (slot :: tail) stop

structure Classified where
  levels : List Slot
  after : State

def classifyFrom (plan : Plan) (ceiling : Nat) :
    State → List Nat → List Nat → List Slot → Except LevelError Classified
  | start, [], [], reversed => .ok ⟨reversed.reverse, start⟩
  | start, rep :: reps, defn :: defs, reversed => do
    let slot ← step plan ceiling start rep defn
    classifyFrom plan ceiling (start.consume slot) reps defs (slot :: reversed)
  | start, _, _, _ => .error (.levelCount start.slots)

def classify (plan : Plan) (ceiling : Nat) (start : State) (reps defs : List Nat) :
    Except LevelError Classified :=
  classifyFrom plan ceiling start reps defs []

inductive PageCause where
  | header (original : RecursiveSchema.Chunk.Cause)
  | slotOverrun (remaining advertised : Nat)
  | checksum (original : Page.Checksum.Error)
  | repetition (original : Repeated.Chunk.LevelCause)
  | definition (original : Repeated.Chunk.LevelCause)
  | level (original : LevelError)
  | plain (original : Plain.Error)
  | alignment (original : FlatPage.Error)
  | dictionary (original : Repeated.Chunk.PageCause)
  | dictionaryIndices (original : DictionaryIndex.Error)
  | v1Payload (original : Repeated.Chunk.PageCause)
  | v2 (original : Repeated.Chunk.PageCause)
  deriving DecidableEq, Repr

structure Decoded where
  levels : List Slot
  words : List (Option Word)
  after : State
  deriving Repr

inductive ValueEncoding where
  | plain
  | dictionary (entries : Array Word)

def ValueEncoding.tag : ValueEncoding → Int
  | .plain => 0
  | .dictionary _ => 8

def ValueEncoding.read (limits : Limits) (kind : RecursiveSchema.Kind)
    (count : Nat) (suffix : Bytes) : ValueEncoding → Except PageCause (List Word)
  | .plain => (RecursiveSchema.Chunk.readWords kind count suffix).mapError .plain
  | .dictionary entries => (DictionaryIndex.readValues limits.indices entries count suffix).mapError .dictionaryIndices

/-- PLAIN has a fixed signed extent. The dictionary suffix is instead
bounded by its original header and consumed exactly by Hybrid. -/
def ValueEncoding.signedExtent (kind : RecursiveSchema.Kind) (info : Page.DataV2) : ValueEncoding → Option Nat
  | .plain => some ((info.numValues - info.numNulls) * RecursiveSchema.Chunk.wordWidth kind)
  | .dictionary _ => none

def ValueEncoding.select (dictionary : Option Repeated.Chunk.Dictionary)
    (encoding : Int) : Except PageCause ValueEncoding :=
  if encoding = 8 then
    match dictionary with
    | some original => .ok (.dictionary original.entries)
    | none => .error (.dictionary .missingDictionary)
  else .ok .plain

inductive ValueEncoding.From (dictionary : Option Repeated.Chunk.Dictionary) : ValueEncoding → Prop where
  | plain : From dictionary .plain
  | dictionary {original : Repeated.Chunk.Dictionary} :
      dictionary = some original → From dictionary (.dictionary original.entries)

def decodeSlots (limits : Limits) (plan : Plan) (ceiling : Nat) (start : State) (reps defs : List Nat)
    (suffix : Bytes) (encoding : ValueEncoding := .plain) : Except PageCause Decoded := do
  let classified ← (classify plan ceiling start reps defs).mapError .level
  let mask := classified.levels.map Slot.present
  let words ← encoding.read limits plan.kind (mask.count true) suffix
  let aligned ← (FlatPage.reconstruct mask words).mapError .alignment
  return ⟨classified.levels, aligned, classified.after⟩

def v1Error : Repeated.Chunk.PageCause → PageCause
  | .header cause => .header cause
  | .slotOverrun remaining advertised => .slotOverrun remaining advertised
  | .checksum cause => .checksum cause
  | cause => .v1Payload cause

/-- Verify the stored V1 frame and expand its entire body before reading
the original level prefixes and signed values. -/
def decodePage (limits : Limits) (plan : Plan) (source : Bytes) (frame : Page.Frame)
    (start : State) (remaining ceiling : Nat) (codec : Codec := .uncompressed)
    (encoding : ValueEncoding := .plain) : Except PageCause Decoded := do
  let info ← (Repeated.Chunk.admitPage frame remaining codec.column encoding.tag).mapError v1Error
  let body ← (Repeated.Chunk.readV1Body limits.payload codec.column source frame).mapError v1Error
  let reps ← (Repeated.Chunk.readLevels limits.levels 2 info.numValues body).mapError .repetition
  let defs ← (Repeated.Chunk.readLevels limits.levels plan.maxDefinition info.numValues reps.tail).mapError .definition
  decodeSlots limits plan ceiling start reps.levels defs.levels defs.tail encoding

def State.close (state : State) : State := { state with live := .closed }

def closeV2 (decoded : Decoded) : Decoded := { decoded with after := decoded.after.close }

def absentSlots (decoded : Decoded) : Nat :=
  decoded.levels.countP (fun slot => !slot.present)

/-- V2 begins a new row, so any live ancestry from an earlier V1 page
is discarded. A V2 page also closes its outgoing cursor, including when
it has zero slots. -/
def checkV2Slots (limits : Limits) (plan : Plan) (info : Page.DataV2) (reps defs : List Nat)
    (suffix : Bytes) (start : State) (ceiling : Nat) (encoding : ValueEncoding := .plain) : Except PageCause Decoded := do
  let first := reps.head?.getD 0
  let rows := reps.count 0
  if first ≠ 0 then throw (.v2 (.v2RowBoundary start.slots first))
  else if rows ≠ info.numRows then throw (.v2 (.v2Rows info.numRows rows))
  else do
    let decoded ← decodeSlots limits plan ceiling start.close reps defs suffix encoding
    let nulls := absentSlots decoded
    if nulls ≠ info.numNulls then throw (.v2 (.v2Nulls info.numNulls nulls))
    else return closeV2 decoded

/-- Keep the original raw V2 levels and resolve the original flag before
passing the value suffix to the shared codec dispatch. -/
def decodeV2Page (limits : Limits) (plan : Plan) (source : Bytes) (frame : Page.Frame)
    (start : State) (remaining ceiling : Nat) (codec : Codec := .uncompressed)
    (encoding : ValueEncoding := .plain) : Except PageCause Decoded := do
  let info ← (Repeated.Chunk.admitV2Page codec.column frame remaining encoding.tag).mapError .v2
  let sections ← (Repeated.Chunk.readV2SectionsWith limits.toLimits 2 plan.maxDefinition
    source frame info).mapError .v2
  let stored := Repeated.Chunk.bytesAt source sections.spans.values
  let expected := encoding.signedExtent plan.kind info
  let suffix ← (Repeated.Chunk.readV2SuffixWith limits.payload codec.column frame info stored
    expected).mapError .v2
  checkV2Slots limits plan info sections.repetitions sections.definitions suffix start ceiling encoding

def decodeDataPage (limits : Limits) (plan : Plan) (source : Bytes) (frame : Page.Frame)
    (start : State) (remaining ceiling : Nat) (codec : Codec := .uncompressed)
    (dictionary : Option Repeated.Chunk.Dictionary := none) : Except PageCause Decoded :=
  match frame.value.kind with
  | .dataV1 info => do
    let encoding ← ValueEncoding.select dictionary info.encoding
    decodePage limits plan source frame start remaining ceiling codec encoding
  | .dataV2 info => do
    let encoding ← ValueEncoding.select dictionary info.encoding
    decodeV2Page limits plan source frame start remaining ceiling codec encoding
  | .dictionary _ => .error (.dictionary .misplacedDictionary)
  | _ => decodePage limits plan source frame start remaining ceiling codec

def ValueEncoding.Wire (limits : Limits) (kind : RecursiveSchema.Kind) (count : Nat)
    (suffix : Bytes) (values : List Word) : ValueEncoding → Prop
  | .plain => ∃ words : List (List UInt8), suffix.toList = words.flatten ∧ words.length = count ∧
      (∀ word ∈ words, word.length = RecursiveSchema.Chunk.wordWidth kind) ∧
      values = words.map (RecursiveSchema.Chunk.readWord kind)
  | .dictionary entries => DictionaryIndex.ValuesWire limits.indices entries count suffix values

structure DecodedWire (limits : Limits) (plan : Plan) (ceiling : Nat) (start : State)
    (reps defs : List Nat) (suffix : Bytes) (decoded : Decoded) (encoding : ValueEncoding := .plain) : Prop where
  levels : SlotsWire plan ceiling start reps defs decoded.levels decoded.after
  aligned : decoded.words.map Option.isSome = decoded.levels.map Slot.present
  words : encoding.Wire limits plan.kind ((decoded.levels.map Slot.present).count true) suffix (decoded.words.filterMap id)

structure PageWire (limits : Limits) (plan : Plan) (source : Bytes) (frame : Page.Frame)
    (start : State) (remaining ceiling : Nat) (decoded : Decoded)
    (codec : Codec := .uncompressed) (encoding : ValueEncoding := .plain) : Prop where
  original : ∃ (info : Page.DataV1) (body : Bytes) (reps defs : Repeated.Chunk.LevelBlock),
    frame.value.kind = .dataV1 info ∧
    (info.encoding = encoding.tag ∧ info.definitionLevelEncoding = 3 ∧ info.repetitionLevelEncoding = 3) ∧
    info.numValues ≤ remaining ∧
    Repeated.Chunk.V1BodyWire limits.payload codec.column source frame body ∧
    Repeated.Chunk.LevelWire limits.levels 2 info.numValues body reps ∧
    Repeated.Chunk.LevelWire limits.levels plan.maxDefinition info.numValues reps.tail defs ∧
    DecodedWire limits plan ceiling start reps.levels defs.levels defs.tail decoded encoding ∧
    decoded.levels.length = info.numValues

structure V2PageWire (limits : Limits) (plan : Plan) (source : Bytes) (frame : Page.Frame)
    (start : State) (remaining ceiling : Nat) (decoded : Decoded)
    (codec : Codec := .uncompressed) (encoding : ValueEncoding := .plain) : Prop where
  original : ∃ (info : Page.DataV2) (sections : Repeated.Chunk.V2Sections) (suffix : Bytes) (checked : Decoded),
    frame.value.kind = .dataV2 info ∧ info.encoding = encoding.tag ∧ info.numValues ≤ remaining ∧
    Repeated.Chunk.V2SectionsWireWith limits.toLimits 2 plan.maxDefinition source frame info sections ∧
    Repeated.Chunk.V2SuffixWire limits.payload codec.column frame info
      (Repeated.Chunk.bytesAt source sections.spans.values) suffix ∧
    Repeated.Chunk.v2LevelBytes info + suffix.length = frame.value.uncompressedSize ∧
    sections.repetitions.head?.getD 0 = 0 ∧ sections.repetitions.count 0 = info.numRows ∧
    absentSlots decoded = info.numNulls ∧ decoded.levels.length = info.numValues ∧
    DecodedWire limits plan ceiling start.close sections.repetitions sections.definitions suffix checked encoding ∧
    decoded = closeV2 checked

inductive DataPageWire (limits : Limits) (plan : Plan) (source : Bytes) (frame : Page.Frame)
    (start : State) (remaining ceiling : Nat) (decoded : Decoded) (codec : Codec := .uncompressed)
    (dictionary : Option Repeated.Chunk.Dictionary := none) : Prop where
  | v1 {encoding : ValueEncoding} : encoding.From dictionary →
      PageWire limits plan source frame start remaining ceiling decoded codec encoding →
      DataPageWire limits plan source frame start remaining ceiling decoded codec dictionary
  | v2 {encoding : ValueEncoding} : encoding.From dictionary →
      V2PageWire limits plan source frame start remaining ceiling decoded codec encoding →
      DataPageWire limits plan source frame start remaining ceiling decoded codec dictionary

inductive ColumnEncoding (metadata : Footer.ColumnMetadata) where
  | plain : RecursiveSchema.SupportedEncodings metadata → metadata.dictionaryPageOffset = none →
      ColumnEncoding metadata
  | dictionary : Repeated.Chunk.DictionaryEncodings metadata → ColumnEncoding metadata

inductive BindCause where
  | missing | association | pageOffsets | pageIndex | span | counts
  | codec (actual : Int)
  | encodings (actual : List Int)
  deriving DecidableEq, Repr

inductive BindError where
  | group (ordinal : Nat)
  | column (address : Address) (cause : BindCause)
  deriving DecidableEq, Repr

structure Binding {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (schema : Compiled schemaLimits snapshot) (group : Nat) where
  rowGroup : Footer.RowGroup
  column : Footer.ColumnChunk
  span : Footer.Span
  groupAt : snapshot.groupAt group = some rowGroup
  columnAt : rowGroup.columns[0]? = some column
  path : column.metadata.pathInSchema = schema.plan.leaf.location.path
  physical : column.metadata.physicalType = schema.plan.kind.physical
  codec : Codec
  originalCodec : Codec.ofId column.metadata.codec = some codec
  encodings : ColumnEncoding column.metadata
  indexOffset : column.metadata.indexPageOffset = none
  unindexed : Repeated.Chunk.Unindexed column
  counts : 0 ≤ column.metadata.numValues ∧ 0 ≤ rowGroup.numRows
  originalSpan : Page.columnSpan snapshot.footer.start column.metadata = some span

end

private def lookup {α ε : Type} (source : Option α) (error : ε) :
    Except ε {value // source = some value} :=
  match source with
  | none => .error error
  | some value => .ok ⟨value, rfl⟩

private def checked {ε : Type} (p : Prop) [Decidable p] (error : ε) : Except ε (PLift p) :=
  if yes : p then .ok ⟨yes⟩ else .error error

private def bindEncoding (metadata : Footer.ColumnMetadata)
    (fail : BindCause → BindError) : Except BindError (ColumnEncoding metadata) := do
  if dictionary : Repeated.Chunk.DictionaryEncodings metadata then
    return .dictionary dictionary
  else
    let ⟨plain⟩ ← checked (RecursiveSchema.SupportedEncodings metadata) (fail (.encodings metadata.encodings))
    let ⟨offset⟩ ← checked (metadata.dictionaryPageOffset = none) (fail .pageOffsets)
    return .plain plain offset

public def bind {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (schema : Compiled schemaLimits snapshot) (group : Nat) : Except BindError (Binding schema group) := do
  let ⟨rowGroup, groupAt⟩ ← lookup (snapshot.groupAt group) (.group group)
  let fail := BindError.column ⟨group, 0, schema.plan.leaf.location.path⟩
  let ⟨column, columnAt⟩ ← lookup rowGroup.columns[0]? (fail .missing)
  let metadata := column.metadata
  let ⟨⟨path, physical⟩⟩ ← checked
    (metadata.pathInSchema = schema.plan.leaf.location.path ∧ metadata.physicalType = schema.plan.kind.physical)
    (fail .association)
  let ⟨codec, originalCodec⟩ ← lookup (Codec.ofId metadata.codec) (fail (.codec metadata.codec))
  let encodings ← bindEncoding metadata fail
  let ⟨indexOffset⟩ ← checked (metadata.indexPageOffset = none) (fail .pageOffsets)
  let ⟨unindexed⟩ ← checked (Repeated.Chunk.Unindexed column) (fail .pageIndex)
  let ⟨counts⟩ ← checked (0 ≤ metadata.numValues ∧ 0 ≤ rowGroup.numRows) (fail .counts)
  let ⟨span, originalSpan⟩ ← lookup (Page.columnSpan snapshot.footer.start metadata) (fail .span)
  return ⟨rowGroup, column, span, groupAt, columnAt, path, physical, codec, originalCodec, encodings,
    indexOffset, unindexed, counts, originalSpan⟩

@[expose] public section

inductive ChunkCause where
  | chunkLimit | slotLimit | rowLimit
  | framing (original : Page.Error)
  | uncompressedSize (advertised : Int) (actual : Nat)
  | slotCount (expected actual : Nat)
  | rowCount (expected actual : Nat)
  deriving DecidableEq, Repr

inductive Error where
  | chunk (address : Address) (span : Footer.Span) (cause : ChunkCause)
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
  observed.dictionary.toList.map (·.frame) ++ observed.pages.map ObservedPage.frame

structure Carrier where
  plan : Plan
  source : Bytes
  span : Footer.Span
  address : Address
  slots : Nat
  rows : Nat
  metadata : Footer.ColumnMetadata
  codec : Codec

def Carrier.uncompressedBytes (carrier : Carrier) : Int :=
  carrier.metadata.totalUncompressedSize

def carrierOf {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat}
    (binding : Binding schema group) : Carrier :=
  ⟨schema.plan, snapshot.bytes, binding.span, ⟨group, 0, schema.plan.leaf.location.path⟩,
    binding.column.metadata.numValues.toNat, binding.rowGroup.numRows.toNat,
    binding.column.metadata, binding.codec⟩

/-- Consume at most one dictionary at physical ordinal zero. The same
scanned original frames continue at the declared first data page. -/
def readPrefix (limits : Limits) (carrier : Carrier) (encoding : ColumnEncoding carrier.metadata)
    (frames : List Page.Frame) : Except Error (Option Repeated.Chunk.Dictionary × List Page.Frame) := do
  match encoding with
  | .plain _ _ => return (none, frames)
  | .dictionary _ =>
    let fail := Error.page carrier.address 0 carrier.span.start {} ∘ PageCause.dictionary
    let some offset := carrier.metadata.dictionaryPageOffset | throw (fail .missingDictionary)
    if offset ≠ Int.ofNat carrier.span.start then throw (fail (.dictionaryOffset offset))
    let frame :: tail := frames | throw (fail .missingDictionary)
    let dictionary ← (Repeated.Chunk.readDictionaryWith limits.payload carrier.plan.kind carrier.source
      frame carrier.codec.dictionary).mapError fail
    if carrier.metadata.dataPageOffset ≠ Int.ofNat frame.payload.stop ∨ frame.payload.stop ≥ carrier.span.stop then
      throw (.page carrier.address 1 frame.payload.stop {}
        (.dictionary (.dataOffset carrier.metadata.dataPageOffset frame.payload.stop)))
    return (some dictionary, tail)

def decodeFrames (limits : Limits) (carrier : Carrier) (dictionary : Option Repeated.Chunk.Dictionary) :
    List Page.Frame → Nat → State → List ObservedPage → Except Error Observation
  | [], _, state, reversed => .ok ⟨reversed.reverse, state, dictionary⟩
  | frame :: frames, ordinal, start, reversed => do
    let decoded ← (decodeDataPage limits carrier.plan carrier.source frame start
      (carrier.slots - start.slots) carrier.rows carrier.codec dictionary).mapError
        (Error.page carrier.address ordinal frame.header.start start)
    decodeFrames limits carrier dictionary frames (ordinal + 1) decoded.after (⟨frame, start, decoded⟩ :: reversed)

/-- Scan the original positive-sized in-file interval and consume each
framed V1 or V2 body in order, keeping separate footer slot and row counts. -/
def read {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat}
    (limits : Limits) (binding : Binding schema group) : Except Error Observation := do
  let carrier := carrierOf binding
  let bytes := carrier.span.stop - carrier.span.start
  let fail := Error.chunk carrier.address carrier.span
  if limits.maxChunkBytes < bytes then throw (fail .chunkLimit)
  else if limits.maxSlots < carrier.slots then throw (fail .slotLimit)
  else if limits.maxRows < carrier.rows then throw (fail .rowLimit)
  else if carrier.codec = .uncompressed ∧ carrier.uncompressedBytes ≠ Int.ofNat bytes then
    throw (fail (.uncompressedSize carrier.uncompressedBytes bytes))
  else do
    let frames ← (Page.readChunk limits.framing carrier.source carrier.span).mapError (fail ∘ .framing)
    let (dictionary, data) ← readPrefix limits carrier binding.encodings frames
    let observed ← decodeFrames limits carrier dictionary data dictionary.isSome.toNat {} []
    if observed.stop.slots ≠ carrier.slots then throw (fail (.slotCount carrier.slots observed.stop.slots))
    else if observed.stop.rows ≠ carrier.rows then throw (fail (.rowCount carrier.rows observed.stop.rows))
    else
      let decodedBytes := Repeated.Chunk.rawChunkBytes observed.frames
      if carrier.uncompressedBytes ≠ Int.ofNat decodedBytes then
        throw (fail (.uncompressedSize carrier.uncompressedBytes decodedBytes))
      else return observed

inductive ChainWire (limits : Limits) (carrier : Carrier) (dictionary : Option Repeated.Chunk.Dictionary) :
    State → List Page.Frame → List ObservedPage → State → Prop where
  | nil (state : State) : ChainWire limits carrier dictionary state [] [] state
  | cons {start frame decoded frames pages stop} :
      DataPageWire limits carrier.plan carrier.source frame start (carrier.slots - start.slots) carrier.rows decoded carrier.codec dictionary →
      ChainWire limits carrier dictionary decoded.after frames pages stop →
      ChainWire limits carrier dictionary start (frame :: frames) (⟨frame, start, decoded⟩ :: pages) stop

inductive PrefixWire (limits : Limits) (carrier : Carrier) :
    Option Repeated.Chunk.Dictionary → List Page.Frame → List Page.Frame → Prop where
  | plain {frames} : carrier.metadata.dictionaryPageOffset = none → PrefixWire limits carrier none frames frames
  | dictionary {dictionary : Repeated.Chunk.Dictionary} {frames} :
      dictionary.codec = carrier.codec.dictionary →
      carrier.metadata.dictionaryPageOffset = some (Int.ofNat carrier.span.start) →
      carrier.metadata.dataPageOffset = Int.ofNat dictionary.frame.payload.stop →
      dictionary.frame.payload.stop < carrier.span.stop →
      Repeated.Chunk.DictionaryContentsWire limits.payload carrier.plan.kind carrier.source dictionary →
      PrefixWire limits carrier (some dictionary) (dictionary.frame :: frames) frames

structure Wire (limits : Limits) (carrier : Carrier) (output : Observation) : Prop where
  origFrames : Page.readChunk limits.framing carrier.source carrier.span = .ok output.frames
  original : Page.Chain carrier.span carrier.span.start carrier.span.stop output.frames
  leading : PrefixWire limits carrier output.dictionary output.frames (output.pages.map ObservedPage.frame)
  decoded : ChainWire limits carrier output.dictionary {} (output.pages.map ObservedPage.frame) output.pages output.stop
  uncompressed : carrier.uncompressedBytes =
    Int.ofNat (Repeated.Chunk.rawChunkBytes output.frames)
  slots : output.stop.slots = carrier.slots
  rows : output.stop.rows = carrier.rows
  caps : carrier.span.stop - carrier.span.start ≤ limits.maxChunkBytes ∧
    carrier.slots ≤ limits.maxSlots ∧ carrier.rows ≤ limits.maxRows

end

end Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Chunk
