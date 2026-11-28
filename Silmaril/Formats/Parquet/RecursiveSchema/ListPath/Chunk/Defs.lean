module

public import Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Rows.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Defs

/-! Original unindexed UNCOMPRESSED PLAIN V1/V2 pages for one canonical LIST path. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Chunk

open RecursiveSchema.Chunk (Address)
open Repeated.Chunk (LevelBlock LevelCause bitWidth)

@[expose] public section

structure Limits extends RecursiveSchema.Chunk.Limits where
  maxSlots : Nat := 1024 * 1024

def Limits.logical (limits : Limits) : Rows.Limits := ⟨limits.maxRows, limits.maxSlots⟩

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

structure Binding {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (schema : Compiled schemaLimits snapshot) (group : Nat) where
  rowGroup : Footer.RowGroup
  column : Footer.ColumnChunk
  span : Footer.Span
  groupAt : snapshot.groupAt group = some rowGroup
  onlyColumn : rowGroup.columns = [column]
  path : column.metadata.pathInSchema = schema.plan.shape.leaf.1.location.path
  physical : column.metadata.physicalType = schema.plan.shape.leaf.2.physical
  codec : column.metadata.codec = 0
  encodings : RecursiveSchema.SupportedEncodings column.metadata
  offsets : column.metadata.dictionaryPageOffset = none ∧ column.metadata.indexPageOffset = none
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
  let ⟨codec⟩ ← checked (metadata.codec = 0) (fail (.codec metadata.codec))
  let ⟨encodings⟩ ← checked (RecursiveSchema.SupportedEncodings metadata) (fail (.encodings metadata.encodings))
  let ⟨offsets⟩ ← checked (metadata.dictionaryPageOffset = none ∧ metadata.indexPageOffset = none) (fail .pageOffsets)
  let ⟨unindexed⟩ ← checked (Repeated.Chunk.Unindexed column) (fail .pageIndex)
  let ⟨counts⟩ ← checked (0 ≤ metadata.numValues ∧ 0 ≤ rowGroup.numRows) (fail .counts)
  let ⟨span, originalSpan⟩ ← lookup (Page.columnSpan snapshot.footer.start metadata) (fail .span)
  return ⟨rowGroup, column, span, atGroup, onlyColumn, path, physical, codec, encodings, offsets,
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

/-- V1 level spans include their four-byte prefixes. V2 spans are raw. -/
structure Sections where
  repetition : Footer.Span
  definition : Footer.Span
  values : Footer.Span
  deriving DecidableEq, Repr

def sections (frame : Page.Frame) (body : Bytes) (reps defs : LevelBlock) : Sections :=
  let definition := frame.payload.start + (body.length - reps.tail.length)
  let values := frame.payload.start + (body.length - defs.tail.length)
  ⟨⟨frame.payload.start, definition⟩, ⟨definition, values⟩, ⟨values, frame.payload.stop⟩⟩

def Sections.ofV2 (spans : Page.V2Spans) : Sections :=
  ⟨spans.repetition, spans.definition, spans.values⟩

inductive PageCause where
  | header (cause : RecursiveSchema.Chunk.Cause)
  | slotOverrun (remaining advertised : Nat)
  | checksum (cause : Page.Checksum.Error)
  | repetition (cause : LevelCause)
  | definition (cause : LevelCause)
  | level (cause : LevelError)
  | plain (cause : Plain.Error)
  | alignment (cause : FlatPage.Error)
  | v2 (cause : Repeated.Chunk.PageCause)
  deriving DecidableEq, Repr

def headerError : RecursiveSchema.Chunk.Cause → PageCause
  | .rowOverrun remaining advertised => .slotOverrun remaining advertised
  | other => .header other

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

/-- Both page versions use the same ancestry scan and exact signed extent. -/
def decodeSlots (plan : Plan) (wrappers : List Nat) (spans : Sections) (start : State)
    (ceiling : Nat) (reps defs : List Nat) (suffix : Bytes) : Except PageCause Decoded := do
  let levels := reps.zip defs
  let stop ← (scan plan wrappers ceiling levels start).mapError .level
  let present := mask plan defs
  let words ← (RecursiveSchema.Chunk.readWords plan.shape.leaf.2 (present.count true) suffix).mapError .plain
  let aligned ← (FlatPage.reconstruct present words).mapError .alignment
  return ⟨spans, atoms levels aligned, stop⟩

def decodePage (limits : Limits) (plan : Plan) (wrappers : List Nat) (source : Bytes) (frame : Page.Frame)
    (start : State) (remaining ceiling : Nat) : Except PageCause Decoded := do
  let info ← (RecursiveSchema.Chunk.admitPage frame remaining).mapError headerError
  let _ ← (Page.Checksum.verify limits.maxBodyBytes source frame).mapError .checksum
  let body := Page.Checksum.payloadBytes source frame
  let reps ← (Repeated.Chunk.readLevels limits.levels plan.shape.repetitions info.numValues body).mapError .repetition
  let defs ← (Repeated.Chunk.readLevels limits.levels plan.shape.definitions info.numValues reps.tail).mapError .definition
  decodeSlots plan wrappers (sections frame body reps defs) start ceiling reps.levels defs.levels defs.tail

def Decoded.close (decoded : Decoded) : Decoded := { decoded with after := decoded.after.close }

def absentSlots (decoded : Decoded) : Nat := decoded.atoms.countP (·.word.isNone)

/-- Check the original V2 header, stored body and raw level spans. Codec
zero keeps the original values for either header flag. A V2 page starts
from a closed cursor and closes its last row before the next frame. -/
def decodeV2Page (limits : Limits) (plan : Plan) (wrappers : List Nat) (source : Bytes) (frame : Page.Frame)
    (start : State) (remaining ceiling : Nat) : Except PageCause Decoded := do
  let info ← (Repeated.Chunk.admitV2Page .uncompressed frame remaining).mapError .v2
  let parts ← (Repeated.Chunk.readV2SectionsWith limits.toLimits plan.shape.repetitions
    plan.shape.definitions source frame info).mapError .v2
  let stored := Repeated.Chunk.bytesAt source parts.spans.values
  let suffix ← (Repeated.Chunk.readV2SuffixWith { toLimits := limits.toLimits }
    .uncompressed frame info stored none).mapError .v2
  let decoded ← Repeated.Chunk.checkV2Counts info parts.repetitions start.slots PageCause.v2 absentSlots fun _ =>
    decodeSlots plan wrappers (.ofV2 parts.spans) start.close ceiling parts.repetitions parts.definitions suffix
  return decoded.close

def decodeDataPage (limits : Limits) (plan : Plan) (wrappers : List Nat) (source : Bytes) (frame : Page.Frame)
    (start : State) (remaining ceiling : Nat) : Except PageCause Decoded :=
  match frame.value.kind with
  | .dataV2 _ => decodeV2Page limits plan wrappers source frame start remaining ceiling
  | _ => decodePage limits plan wrappers source frame start remaining ceiling

structure SlotsWire (plan : Plan) (wrappers : List Nat) (start : State) (ceiling : Nat)
    (reps defs : List Nat) (suffix : Bytes) (decoded : Decoded) : Prop where
  original : ∃ (aligned : List (Option RecursiveSchema.Chunk.Word)) (words : List (List UInt8)),
    ScanWire plan wrappers ceiling start (reps.zip defs) decoded.after ∧
    suffix.toList = words.flatten ∧ words.length = (mask plan defs).count true ∧
    (∀ word ∈ words, word.length = RecursiveSchema.Chunk.wordWidth plan.shape.leaf.2) ∧
    aligned.map Option.isSome = mask plan defs ∧
    aligned.filterMap id = words.map (RecursiveSchema.Chunk.readWord plan.shape.leaf.2) ∧
    decoded.atoms = atoms (reps.zip defs) aligned

structure SectionsWire (limits : Hybrid.Limits) (plan : Plan) (count : Nat) (source : Bytes)
    (frame : Page.Frame) (spans : Sections) (repetitions definitions : List Nat) (suffix : Bytes) : Prop where
  original : ∃ repPrefix defPrefix repBytes defBytes : List UInt8,
    repPrefix.length = 4 ∧ defPrefix.length = 4 ∧
    KBytes.leVal repPrefix = repBytes.length ∧ KBytes.leVal defPrefix = defBytes.length ∧
    repBytes.length ≤ limits.bytes ∧ defBytes.length ≤ limits.bytes ∧
    Hybrid.Wire (bitWidth plan.shape.repetitions) count repBytes repetitions ∧
    Hybrid.Wire (bitWidth plan.shape.definitions) count defBytes definitions ∧
    spans.repetition.start = frame.payload.start ∧ spans.repetition.stop = spans.definition.start ∧
    spans.definition.stop = spans.values.start ∧ spans.values.stop = frame.payload.stop ∧
    source.slice? spans.repetition.start (some spans.repetition.stop) =
      some (Bytes.ofList (repPrefix ++ repBytes)) ∧
    source.slice? spans.definition.start (some spans.definition.stop) =
      some (Bytes.ofList (defPrefix ++ defBytes)) ∧
    source.slice? spans.values.start (some spans.values.stop) = some suffix

structure PageWire (limits : Limits) (plan : Plan) (wrappers : List Nat) (source : Bytes) (frame : Page.Frame)
    (start : State) (remaining ceiling : Nat) (decoded : Decoded) : Prop where
  original : ∃ (info : Page.DataV1) (checksum : Page.Checksum.Status) (reps defs : LevelBlock)
      (aligned : List (Option RecursiveSchema.Chunk.Word)) (words : List (List UInt8)),
    RecursiveSchema.Chunk.HeaderWire frame remaining info ∧
    Page.Checksum.verify limits.maxBodyBytes source frame = .ok checksum ∧
    SectionsWire limits.levels plan info.numValues source frame decoded.sections reps.levels defs.levels defs.tail ∧
    ScanWire plan wrappers ceiling start (reps.levels.zip defs.levels) decoded.after ∧
    reps.levels.length = info.numValues ∧ defs.levels.length = info.numValues ∧
    defs.tail.toList = words.flatten ∧ words.length = (mask plan defs.levels).count true ∧
    (∀ word ∈ words, word.length = RecursiveSchema.Chunk.wordWidth plan.shape.leaf.2) ∧
    aligned.map Option.isSome = mask plan defs.levels ∧
    aligned.filterMap id = words.map (RecursiveSchema.Chunk.readWord plan.shape.leaf.2) ∧
    decoded.atoms = atoms (reps.levels.zip defs.levels) aligned

structure V2PageWire (limits : Limits) (plan : Plan) (wrappers : List Nat) (source : Bytes) (frame : Page.Frame)
    (start : State) (remaining ceiling : Nat) (decoded : Decoded) : Prop where
  original : ∃ (info : Page.DataV2) (parts : Repeated.Chunk.V2Sections) (checked : Decoded),
    frame.value.kind = .dataV2 info ∧ info.encoding = 0 ∧ info.numValues ≤ remaining ∧
    frame.value.uncompressedSize = frame.value.compressedSize ∧
    Repeated.Chunk.V2SectionsWireWith limits.toLimits plan.shape.repetitions plan.shape.definitions
      source frame info parts ∧
    Repeated.Chunk.v2LevelBytes info + (Repeated.Chunk.bytesAt source parts.spans.values).length =
      frame.value.uncompressedSize ∧
    parts.repetitions.head?.getD 0 = 0 ∧ parts.repetitions.count 0 = info.numRows ∧
    absentSlots decoded = info.numNulls ∧ decoded.sections = .ofV2 parts.spans ∧
    SlotsWire plan wrappers start.close ceiling parts.repetitions parts.definitions
      (Repeated.Chunk.bytesAt source parts.spans.values) checked ∧ decoded = checked.close

inductive DataPageWire (limits : Limits) (plan : Plan) (wrappers : List Nat) (source : Bytes) (frame : Page.Frame)
    (start : State) (remaining ceiling : Nat) (decoded : Decoded) : Prop where
  | v1 : PageWire limits plan wrappers source frame start remaining ceiling decoded →
      DataPageWire limits plan wrappers source frame start remaining ceiling decoded
  | v2 : V2PageWire limits plan wrappers source frame start remaining ceiling decoded →
      DataPageWire limits plan wrappers source frame start remaining ceiling decoded

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
  deriving Repr

def Observation.frames (observed : Observation) : List Page.Frame := observed.pages.map ObservedPage.frame
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

def carrierOf {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat} (binding : Binding schema group) : Carrier :=
  ⟨schema.plan, snapshot.bytes, binding.span, address schema.plan group, binding.column.metadata.numValues.toNat,
    binding.rowGroup.numRows.toNat, binding.column.metadata.totalCompressedSize,
    binding.column.metadata.totalUncompressedSize⟩

def decodeFrames (limits : Limits) (carrier : Carrier) (wrappers : List Nat) :
    List Page.Frame → Nat → State → List ObservedPage → Except Error Observation
  | [], _, finish, reversed => .ok ⟨reversed.reverse, finish⟩
  | frame :: frames, ordinal, start, reversed => do
    let decoded ← (decodeDataPage limits carrier.plan wrappers carrier.source frame start
      (carrier.slots - start.slots) carrier.rows).mapError
        (.page carrier.address ordinal frame.header.start start)
    decodeFrames limits carrier wrappers frames (ordinal + 1) decoded.after (⟨frame, start, decoded⟩ :: reversed)

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
    let observed ← decodeFrames limits carrier (wrappers carrier.plan) frames 0 {} []
    checkTotals carrier frames observed

inductive ChainWire (limits : Limits) (carrier : Carrier) : State → State → List ObservedPage → Prop where
  | nil (state : State) : ChainWire limits carrier state state []
  | cons {start stop frame decoded rest} :
      DataPageWire limits carrier.plan (wrappers carrier.plan) carrier.source frame start
        (carrier.slots - start.slots) carrier.rows decoded →
      ChainWire limits carrier decoded.after stop rest →
      ChainWire limits carrier start stop (⟨frame, start, decoded⟩ :: rest)

structure Wire (limits : Limits) (carrier : Carrier) (observed : Observation) : Prop where
  framed : Page.readChunk limits.framing carrier.source carrier.span = .ok observed.frames
  pages : Page.Chain carrier.span carrier.span.start carrier.span.stop observed.frames
  checked : ChainWire limits carrier {} observed.stop observed.pages
  slotCount : observed.stop.slots = carrier.slots
  rowCount : observed.stop.rows = carrier.rows
  stored : carrier.storedSize = Int.ofNat (Repeated.Chunk.storedChunkBytes observed.frames)
  raw : carrier.rawSize = Int.ofNat (Repeated.Chunk.rawChunkBytes observed.frames)
  byteLimit : carrier.span.stop - carrier.span.start ≤ limits.maxChunkBytes
  slotLimit : carrier.slots ≤ limits.maxSlots
  rowLimit : carrier.rows ≤ limits.maxRows

end

end Silmaril.Formats.Parquet.RecursiveSchema.ListPath.Chunk
