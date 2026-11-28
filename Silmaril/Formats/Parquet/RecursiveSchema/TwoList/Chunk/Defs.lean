module

public import Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Defs
public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Defs

/-! Bounded, unindexed UNCOMPRESSED PLAIN V1 for one two-LIST leaf.
The cursor carries the deepest live List across consecutive data pages. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Chunk

@[expose] public section
abbrev Address := RecursiveSchema.Chunk.Address
abbrev Word := RecursiveSchema.Chunk.Word

structure Limits extends RecursiveSchema.Chunk.Limits where
  maxSlots : Nat := 1024 * 1024

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
  deriving DecidableEq, Repr

structure Decoded where
  levels : List Slot
  words : List (Option Word)
  after : State
  deriving Repr

def decodeSlots (plan : Plan) (ceiling : Nat) (start : State) (reps defs : List Nat)
    (suffix : Bytes) : Except PageCause Decoded := do
  let classified ← (classify plan ceiling start reps defs).mapError .level
  let mask := classified.levels.map Slot.present
  let words ← (RecursiveSchema.Chunk.readWords plan.kind (mask.count true) suffix).mapError .plain
  let aligned ← (FlatPage.reconstruct mask words).mapError .alignment
  return ⟨classified.levels, aligned, classified.after⟩

def decodePage (limits : Limits) (plan : Plan) (source : Bytes) (frame : Page.Frame)
    (start : State) (remaining ceiling : Nat) : Except PageCause Decoded := do
  let info ← (RecursiveSchema.Chunk.admitPage frame remaining).mapError fun
    | .rowOverrun remaining advertised => .slotOverrun remaining advertised
    | error => .header error
  let _ ← (Page.Checksum.verify limits.maxBodyBytes source frame).mapError .checksum
  let body := Page.Checksum.payloadBytes source frame
  let reps ← (Repeated.Chunk.readLevels limits.levels 2 info.numValues body).mapError .repetition
  let defs ← (Repeated.Chunk.readLevels limits.levels plan.maxDefinition info.numValues reps.tail).mapError .definition
  decodeSlots plan ceiling start reps.levels defs.levels defs.tail

structure DecodedWire (plan : Plan) (ceiling : Nat) (start : State) (reps defs : List Nat) (suffix : Bytes)
    (decoded : Decoded) : Prop where
  levels : SlotsWire plan ceiling start reps defs decoded.levels decoded.after
  words : ∃ words : List (List UInt8), suffix.toList = words.flatten ∧
    words.length = (decoded.levels.map Slot.present).count true ∧
    (∀ word ∈ words, word.length = RecursiveSchema.Chunk.wordWidth plan.kind) ∧
    decoded.words.map Option.isSome = decoded.levels.map Slot.present ∧
    decoded.words.filterMap id = words.map (RecursiveSchema.Chunk.readWord plan.kind)

structure PageWire (limits : Limits) (plan : Plan) (source : Bytes) (frame : Page.Frame)
    (start : State) (remaining ceiling : Nat) (decoded : Decoded) : Prop where
  original : ∃ (info : Page.DataV1) (body : Bytes) (checksum : Page.Checksum.Status) (reps defs : Repeated.Chunk.LevelBlock),
    RecursiveSchema.Chunk.HeaderWire frame remaining info ∧
    Page.Checksum.verify limits.maxBodyBytes source frame = .ok checksum ∧
    source.slice? frame.payload.start (some frame.payload.stop) = some body ∧
    body.length = frame.value.compressedSize ∧
    Repeated.Chunk.LevelWire limits.levels 2 info.numValues body reps ∧
    Repeated.Chunk.LevelWire limits.levels plan.maxDefinition info.numValues reps.tail defs ∧
    DecodedWire plan ceiling start reps.levels defs.levels defs.tail decoded ∧
    decoded.levels.length = info.numValues

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
  codec : column.metadata.codec = 0
  encodings : RecursiveSchema.SupportedEncodings column.metadata
  offsets : column.metadata.dictionaryPageOffset = none ∧ column.metadata.indexPageOffset = none
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

public def bind {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    (schema : Compiled schemaLimits snapshot) (group : Nat) : Except BindError (Binding schema group) := do
  let ⟨rowGroup, groupAt⟩ ← lookup (snapshot.groupAt group) (.group group)
  let fail := BindError.column ⟨group, 0, schema.plan.leaf.location.path⟩
  let ⟨column, columnAt⟩ ← lookup rowGroup.columns[0]? (fail .missing)
  let metadata := column.metadata
  let ⟨⟨path, physical⟩⟩ ← checked
    (metadata.pathInSchema = schema.plan.leaf.location.path ∧ metadata.physicalType = schema.plan.kind.physical)
    (fail .association)
  let ⟨codec⟩ ← checked (metadata.codec = 0) (fail (.codec metadata.codec))
  let ⟨encodings⟩ ← checked (RecursiveSchema.SupportedEncodings metadata) (fail (.encodings metadata.encodings))
  let ⟨offsets⟩ ← checked (metadata.dictionaryPageOffset = none ∧ metadata.indexPageOffset = none) (fail .pageOffsets)
  let ⟨unindexed⟩ ← checked (Repeated.Chunk.Unindexed column) (fail .pageIndex)
  let ⟨counts⟩ ← checked (0 ≤ metadata.numValues ∧ 0 ≤ rowGroup.numRows) (fail .counts)
  let ⟨span, originalSpan⟩ ← lookup (Page.columnSpan snapshot.footer.start metadata) (fail .span)
  return ⟨rowGroup, column, span, groupAt, columnAt, path, physical, codec, encodings,
    offsets, unindexed, counts, originalSpan⟩

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
  deriving Repr

structure Carrier where
  plan : Plan
  source : Bytes
  span : Footer.Span
  address : Address
  slots : Nat
  rows : Nat
  uncompressedBytes : Int

def carrierOf {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat}
    (binding : Binding schema group) : Carrier :=
  ⟨schema.plan, snapshot.bytes, binding.span, ⟨group, 0, schema.plan.leaf.location.path⟩,
    binding.column.metadata.numValues.toNat, binding.rowGroup.numRows.toNat,
    binding.column.metadata.totalUncompressedSize⟩

def decodeFrames (limits : Limits) (carrier : Carrier) :
    List Page.Frame → Nat → State → List ObservedPage → Except Error Observation
  | [], _, state, reversed => .ok ⟨reversed.reverse, state⟩
  | frame :: frames, ordinal, start, reversed => do
    let decoded ← (decodePage limits carrier.plan carrier.source frame start
      (carrier.slots - start.slots) carrier.rows).mapError
        (Error.page carrier.address ordinal frame.header.start start)
    decodeFrames limits carrier frames (ordinal + 1) decoded.after (⟨frame, start, decoded⟩ :: reversed)

/-- Scan the original positive-sized in-file interval and consume each
framed V1 body in order, keeping separate footer slot and row counts. -/
def read {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group : Nat}
    (limits : Limits) (binding : Binding schema group) : Except Error Observation := do
  let carrier := carrierOf binding
  let bytes := carrier.span.stop - carrier.span.start
  let fail := Error.chunk carrier.address carrier.span
  if limits.maxChunkBytes < bytes then throw (fail .chunkLimit)
  else if limits.maxSlots < carrier.slots then throw (fail .slotLimit)
  else if limits.maxRows < carrier.rows then throw (fail .rowLimit)
  else if carrier.uncompressedBytes ≠ Int.ofNat bytes then
    throw (fail (.uncompressedSize carrier.uncompressedBytes bytes))
  else do
    let frames ← (Page.readChunk limits.framing carrier.source carrier.span).mapError (fail ∘ .framing)
    let observed ← decodeFrames limits carrier frames 0 {} []
    if observed.stop.slots ≠ carrier.slots then throw (fail (.slotCount carrier.slots observed.stop.slots))
    else if observed.stop.rows ≠ carrier.rows then throw (fail (.rowCount carrier.rows observed.stop.rows))
    else return observed

inductive ChainWire (limits : Limits) (carrier : Carrier) :
    State → List Page.Frame → List ObservedPage → State → Prop where
  | nil (state : State) : ChainWire limits carrier state [] [] state
  | cons {start frame decoded frames pages stop} :
      PageWire limits carrier.plan carrier.source frame start (carrier.slots - start.slots) carrier.rows decoded →
      ChainWire limits carrier decoded.after frames pages stop →
      ChainWire limits carrier start (frame :: frames) (⟨frame, start, decoded⟩ :: pages) stop

structure Wire (limits : Limits) (carrier : Carrier) (output : Observation) : Prop where
  origFrames : Page.readChunk limits.framing carrier.source carrier.span = .ok (output.pages.map ObservedPage.frame)
  original : Page.Chain carrier.span carrier.span.start carrier.span.stop (output.pages.map ObservedPage.frame)
  decoded : ChainWire limits carrier {} (output.pages.map ObservedPage.frame) output.pages output.stop
  uncompressed : carrier.uncompressedBytes = Int.ofNat (carrier.span.stop - carrier.span.start)
  slots : output.stop.slots = carrier.slots
  rows : output.stop.rows = carrier.rows
  caps : carrier.span.stop - carrier.span.start ≤ limits.maxChunkBytes ∧
    carrier.slots ≤ limits.maxSlots ∧ carrier.rows ≤ limits.maxRows

end

end Silmaril.Formats.Parquet.RecursiveSchema.TwoList.Chunk
