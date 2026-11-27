module

public import Silmaril.Formats.Parquet.RecursiveSchema.Defs
public import Silmaril.Formats.Parquet.Page.Checksum.Defs
public import Silmaril.Formats.Parquet.FlatPage.Defs
public import Silmaril.Formats.Parquet.Plain.Defs

/-! Native UNCOMPRESSED PLAIN Data Page V1 for one non-repeated signed
leaf selected by the original recursive Parquet footer. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.Chunk

@[expose] public section

structure Limits where
  framing : Page.Limits := {}
  levels : Hybrid.Limits := ⟨1024 * 1024, 16 * 1024 * 1024⟩
  maxBodyBytes : Nat := 16 * 1024 * 1024
  maxChunkBytes : Nat := 64 * 1024 * 1024
  maxRows : Nat := 1024 * 1024

structure Address where
  group : Nat
  column : Nat
  path : List String
  deriving DecidableEq, Repr

structure Cursor where
  page : Nat
  byte : Nat
  row : Nat
  deriving DecidableEq, Repr

inductive Word where
  | int32 (value : Int32)
  | int64 (value : Int64)
  deriving DecidableEq, Repr

inductive Slot where
  | absent (location : Location)
  | value (word : Word)
  deriving DecidableEq, Repr

def Slot.presence : Slot → Presence
  | .absent location => .absent location
  | .value _ => .value

def Slot.word? : Slot → Option Word
  | .absent _ => none
  | .value word => some word

def wordWidth : RecursiveSchema.Kind → Nat
  | .int32 => 4
  | .int64 => 8

def readWord : RecursiveSchema.Kind → List UInt8 → Word
  | .int32, bytes => .int32 (Plain.readUInt32Word bytes).toInt32
  | .int64, bytes => .int64 (Plain.readUInt64Word bytes).toInt64

def readWords (kind : RecursiveSchema.Kind) (count : Nat) (source : Bytes) :
    Except Plain.Error (List Word) :=
  Plain.decodeFixedWidth (wordWidth kind) count (readWord kind) source

def present : Presence → Bool
  | .value => true
  | .absent _ => false

inductive Cause where
  | framing (original : Page.Error)
  | pageKind (original : Page.Kind)
  | encoding (value definition repetition : Int)
  | pageSizes (uncompressed compressed : Nat)
  | rowOverrun (remaining advertised : Nat)
  | checksum (original : Page.Checksum.Error)
  | countLimit
  | section (original : FlatPage.Error)
  | hybrid (original : Hybrid.Error)
  | definition (original : DefinitionError)
  | plain (original : Plain.Error)
  | wordCount
  deriving DecidableEq, Repr

inductive ChunkCause where
  | bounds
  | chunkLimit
  | rowLimit
  | uncompressedSize (advertised : Int) (spanBytes : Nat)
  | rowCount (expected actual : Nat)
  deriving DecidableEq, Repr

inductive Error where
  | chunk (address : Address) (span : Footer.Span) (cause : ChunkCause)
  | page (address : Address) (cursor : Cursor) (cause : Cause)
  deriving DecidableEq, Repr

structure Definitions where
  levels : List Nat
  scalars : Bytes

/-- A zero-definition V1 path stores its words directly after the header.
Other paths have the original length-delimited hybrid section first. -/
def readDefinitions (leaf : Leaf) (limits : Hybrid.Limits) (count : Nat) (body : Bytes) :
    Except Cause Definitions :=
  if leaf.maxDefinition = 0 then
    if Hybrid.runLimit ≤ count ∨ limits.values < count then .error .countLimit
    else .ok ⟨List.replicate count 0, body⟩
  else do
    let parts ← (FlatPage.splitV1Optional limits.bytes body).mapError .section
    let levels ← (Hybrid.decode leaf.bitWidth count limits parts.definitions).mapError .hybrid
    return ⟨levels, parts.scalars⟩

def classifyLevels (leaf : Leaf) (firstRow : Nat) (levels : List Nat) :
    Except Cause (List Presence) :=
  (levels.zipIdx firstRow).mapM fun (level, row) => (leaf.classify row level).mapError .definition

def fill (states : List Presence) (words : List Word) (reversed : List Slot) :
    Except Cause (List Slot) :=
  match states, words with
  | [], [] => .ok reversed.reverse
  | .absent location :: rest, words => fill rest words (.absent location :: reversed)
  | .value :: rest, word :: words => fill rest words (.value word :: reversed)
  | _, _ => .error .wordCount

/-- Share the PLAIN V1 header checks. Identity callers also require equal
stored and raw sizes before they read the body. -/
def admitPageWith (requireEqualSizes : Bool) (frame : Page.Frame) (remaining : Nat) : Except Cause Page.DataV1 :=
  match frame.value.kind with
  | .dataV1 info =>
    if ¬ (info.encoding = 0 ∧ info.definitionLevelEncoding = 3 ∧ info.repetitionLevelEncoding = 3)
      then .error (.encoding info.encoding info.definitionLevelEncoding info.repetitionLevelEncoding)
    else if requireEqualSizes = true ∧ frame.value.uncompressedSize ≠ frame.value.compressedSize
      then .error (.pageSizes frame.value.uncompressedSize frame.value.compressedSize)
    else if info.numValues > remaining then .error (.rowOverrun remaining info.numValues)
    else .ok info
  | other => .error (.pageKind other)

def admitPage (frame : Page.Frame) (remaining : Nat) : Except Cause Page.DataV1 :=
  admitPageWith true frame remaining

/-- The supplied frame is checked against its original serialized payload.
CRC is verified when present. The entire scalar suffix must be consumed. -/
def decodePage (limits : Limits) (leaf : Leaf) (source : Bytes) (frame : Page.Frame)
    (firstRow remaining : Nat) : Except Cause (List Slot) := do
  let info ← admitPage frame remaining
  let _ ← (Page.Checksum.verify limits.maxBodyBytes source frame).mapError .checksum
  let body := Page.Checksum.payloadBytes source frame
  let definitions ← readDefinitions leaf limits.levels info.numValues body
  let states ← classifyLevels leaf firstRow definitions.levels
  let words ← (readWords leaf.kind (states.countP present) definitions.scalars).mapError .plain
  fill states words []

structure ObservedPage where
  frame : Page.Frame
  firstRow : Nat
  slots : List Slot
  deriving Repr

def Cursor.advance (cursor : Cursor) (page : ObservedPage) : Cursor :=
  ⟨cursor.page + 1, page.frame.payload.stop, cursor.row + page.slots.length⟩

structure Carrier where
  bytes : Bytes
  span : Footer.Span
  leaf : Leaf
  address : Address
  expected : Nat

def initial (carrier : Carrier) : Cursor := ⟨0, carrier.span.start, 0⟩

/-- Consume each original frame once. Reaching the end of the span checks
the whole footer row count even at the exact page-budget boundary. -/
def walk (limits : Limits) (carrier : Carrier) (budget : Nat) (cursor : Cursor)
    (reversed : List ObservedPage) : Except Error (List ObservedPage) :=
  if cursor.byte = carrier.span.stop then
    if cursor.row = carrier.expected then .ok reversed.reverse
    else .error (.chunk carrier.address carrier.span (.rowCount carrier.expected cursor.row))
  else
    let failed := Error.page carrier.address cursor
    match budget with
    | 0 => .error (failed (.framing .pageLimit))
    | fuel + 1 => do
      let frame ← (Page.readPage limits.framing carrier.bytes carrier.span cursor.byte).mapError
        (failed ∘ Cause.framing)
      let slots ← (decodePage limits carrier.leaf carrier.bytes frame cursor.row
        (carrier.expected - cursor.row)).mapError failed
      let page : ObservedPage := ⟨frame, cursor.row, slots⟩
      walk limits carrier fuel (cursor.advance page) (page :: reversed)

structure Observation where
  pages : List ObservedPage

def Observation.rows (column : Observation) : List Slot := column.pages.flatMap ObservedPage.slots

def carrierOf {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group column : Nat}
    (binding : ChunkBinding schema group column) : Carrier :=
  ⟨snapshot.bytes, binding.span, binding.leaf, ⟨group, column, binding.leaf.site.location.path⟩,
    binding.rowGroup.numRows.toNat⟩

/-- Read from the checked binding's immutable snapshot. Chunk limits and
its total uncompressed extent are checked before reading headers. -/
def read {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group column : Nat}
    (limits : Limits) (binding : ChunkBinding schema group column) : Except Error Observation :=
  let carrier := carrierOf binding
  let bytes := carrier.span.stop - carrier.span.start
  let failed := Error.chunk carrier.address carrier.span
  if ¬ (carrier.span.start ≤ carrier.span.stop ∧ carrier.span.stop ≤ carrier.bytes.length)
    then .error (failed .bounds)
  else if bytes > limits.maxChunkBytes then .error (failed .chunkLimit)
  else if carrier.expected > limits.maxRows then .error (failed .rowLimit)
  else if binding.chunk.metadata.totalUncompressedSize ≠ Int.ofNat bytes then
    .error (failed (.uncompressedSize binding.chunk.metadata.totalUncompressedSize bytes))
  else (walk limits carrier limits.framing.maxPages (initial carrier) []).map Observation.mk

structure HeaderWire (frame : Page.Frame) (remaining : Nat) (info : Page.DataV1) : Prop where
  kind : frame.value.kind = .dataV1 info
  encodings : info.encoding = 0 ∧ info.definitionLevelEncoding = 3 ∧ info.repetitionLevelEncoding = 3
  sizes : frame.value.uncompressedSize = frame.value.compressedSize
  count : info.numValues ≤ remaining

inductive DefinitionWire (leaf : Leaf) (limits : Hybrid.Limits) (count : Nat) (body : Bytes) :
    Definitions → Prop where
  | required : leaf.maxDefinition = 0 → count < Hybrid.runLimit → count ≤ limits.values →
      DefinitionWire leaf limits count body ⟨List.replicate count 0, body⟩
  | optional {levels : List Nat} {scalars definitionBytes : Bytes} {lengthBytes : List UInt8} :
      leaf.maxDefinition ≠ 0 → lengthBytes.length = 4 →
      KBytes.leVal lengthBytes = definitionBytes.length → definitionBytes.length ≤ limits.bytes →
      body.toList = lengthBytes ++ definitionBytes.toList ++ scalars.toList →
      Hybrid.Wire leaf.bitWidth count definitionBytes.toList levels →
      DefinitionWire leaf limits count body ⟨levels, scalars⟩

def ClassificationWire (leaf : Leaf) (firstRow : Nat) (levels : List Nat) (states : List Presence) :
    Prop :=
  List.Forall₂ (fun (level, row) state => leaf.classify row level = .ok state)
    (levels.zipIdx firstRow) states

/-- Exact original body and logical slots for one page. The signed words
exhaust the original suffix and are assigned in original present-slot order. -/
structure PageWire (limits : Limits) (leaf : Leaf) (source : Bytes) (frame : Page.Frame)
    (firstRow remaining : Nat) (slots : List Slot) : Prop where
  original : ∃ (info : Page.DataV1) (body : Bytes) (definitions : Definitions)
    (states : List Presence) (words : List (List UInt8)) (checksum : Page.Checksum.Status),
    HeaderWire frame remaining info ∧
    Page.Checksum.verify limits.maxBodyBytes source frame = .ok checksum ∧
    source.slice? frame.payload.start (some frame.payload.stop) = some body ∧
    body.length = frame.value.compressedSize ∧
    DefinitionWire leaf limits.levels info.numValues body definitions ∧
    ClassificationWire leaf firstRow definitions.levels states ∧
    definitions.scalars.toList = words.flatten ∧ words.length = states.countP present ∧
    (∀ word ∈ words, word.length = wordWidth leaf.kind) ∧
    slots.map Slot.presence = states ∧ slots.filterMap Slot.word? = words.map (readWord leaf.kind) ∧
    slots.length = info.numValues

inductive ChainWire (limits : Limits) (carrier : Carrier) :
    Cursor → Cursor → List ObservedPage → Prop where
  | nil (cursor : Cursor) : ChainWire limits carrier cursor cursor []
  | more {start stop first rest} :
      Page.readPage limits.framing carrier.bytes carrier.span start.byte = .ok first.frame →
      first.firstRow = start.row →
      PageWire limits carrier.leaf carrier.bytes first.frame start.row (carrier.expected - start.row) first.slots →
      ChainWire limits carrier (start.advance first) stop rest →
      ChainWire limits carrier start stop (first :: rest)

structure Wire {schemaLimits : Snapshot.Limits} {snapshot : Snapshot.Checked}
    {schema : Compiled schemaLimits snapshot} {group column : Nat}
    (limits : Limits) (binding : ChunkBinding schema group column) (output : Observation) : Prop where
  bounds : binding.span.start ≤ binding.span.stop ∧ binding.span.stop ≤ snapshot.bytes.length
  chunkCap : binding.span.stop - binding.span.start ≤ limits.maxChunkBytes
  rowCap : binding.rowGroup.numRows.toNat ≤ limits.maxRows
  uncompressed : binding.chunk.metadata.totalUncompressedSize =
    Int.ofNat (binding.span.stop - binding.span.start)
  chain : ∃ stop : Cursor, stop.byte = binding.span.stop ∧ stop.row = binding.rowGroup.numRows.toNat ∧
    ChainWire limits (carrierOf binding) (initial (carrierOf binding)) stop output.pages
  frames : Page.Chain binding.span binding.span.start binding.span.stop (output.pages.map ObservedPage.frame)
  rows : output.rows.length = binding.rowGroup.numRows.toNat

end

end Silmaril.Formats.Parquet.RecursiveSchema.Chunk
