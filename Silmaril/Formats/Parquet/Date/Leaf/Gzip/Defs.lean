module

public import Silmaril.Formats.Parquet.Date.Leaf.Events.Defs
public import Silmaril.Formats.Parquet.Page.Checksum.Defs

/-! Opt-in GZIP PLAIN V1 data for a strictly selected flat DATE leaf. -/

@[expose] public section

namespace Silmaril.Formats.Parquet.Date.Leaf.Gzip

structure Limits where
  framing : Page.Limits := {}
  scalar : ScalarPage.Limits :=
    ⟨16 * 1024 * 1024, 16 * 1024 * 1024, ⟨1024 * 1024, 16 * 1024 * 1024⟩, 1024 * 1024⟩
  maxRows : Nat := 1024 * 1024
  maxStoredChunkBytes : Nat := 64 * 1024 * 1024
  maxExpandedChunkBytes : Nat := 64 * 1024 * 1024

inductive PageError where
  | expectedV1
  | encoding (actual : Int)
  | dataOffset
  | checksum (cause : Page.Checksum.Error)
  | scalar (cause : ScalarPage.Error)
  deriving DecidableEq, Repr

inductive GroupError where
  | selection (cause : Leaf.Error)
  | codec (actual : Int)
  | unsupportedOffsets
  | rowLimit
  | rowCount (expected : Nat) (declared : Int)
  | storedChunkLimit
  | expandedChunkLimit
  | framing (cause : Page.Error)
  | missingData
  | page (ordinal offset : Nat) (cause : PageError)
  deriving DecidableEq, Repr

inductive Error where
  | openFailure (cause : Leaf.Error)
  | groupFailure (index : Nat) (cause : GroupError)
  deriving DecidableEq, Repr

inductive IpcError where
  | source (cause : Error)
  | closed
  | writer (cause : Arrow.DateStream.Writer.Error)
  deriving DecidableEq, Repr

structure DataPage where
  frame : Page.Frame
  params : ScalarPage.Parameters

structure CheckedGroup where
  selection : Leaf.Chunk
  data : List DataPage

def CheckedGroup.frames (checked : CheckedGroup) : List Page.Frame :=
  checked.data.map (·.frame)

def atFrame (ordinal : Nat) (frame : Page.Frame) : PageError → GroupError :=
  .page ordinal frame.header.start

/-- Keep the original flat V1 header and select the GZIP payload decoder. -/
def planData (bound : Bound) (frame : Page.Frame) : Except PageError DataPage := do
  let .dataV1 header := frame.value.kind | throw .expectedV1
  if header.encoding ≠ 0 then throw (.encoding header.encoding)
  let some params := FlatScan.int32PageParameters bound.field frame.value | throw .expectedV1
  return ⟨frame, { params with codec := Payload.Codec.gzip.id }⟩

/-- Admit the original selected chunk, checking the stored and expanded
chunk caps independently before decoding any page bodies. -/
def checkGroupWith {ε : Type} (wrap : GroupError → ε)
    (plan : Page.Frame → Nat → Except ε DataPage)
    (limits : Limits) (bound : Bound) (index : Nat) : Except ε CheckedGroup := do
  let selected ← (selectChunk bound index).mapError (wrap ∘ .selection)
  let metadata := selected.column.metadata
  let rows := selected.group.numRows.toNat
  if metadata.codec ≠ Payload.Codec.gzip.id then .error (wrap (.codec metadata.codec))
  else if metadata.dictionaryPageOffset.isSome || metadata.indexPageOffset.isSome then
    .error (wrap .unsupportedOffsets)
  else if metadata.numValues ≠ (rows : Int) then .error (wrap (.rowCount rows metadata.numValues))
  else if limits.maxRows < rows then .error (wrap .rowLimit)
  else if limits.maxStoredChunkBytes < selected.span.stop - selected.span.start then .error (wrap .storedChunkLimit)
  else do
    let frames ← (Page.readChunk limits.framing bound.snapshot.bytes selected.span).mapError (wrap ∘ .framing)
    if limits.maxExpandedChunkBytes < (frames.map (·.value.uncompressedSize)).sum then
      .error (wrap .expandedChunkLimit)
    else do
      let first :: _ := frames | throw (wrap .missingData)
      if metadata.dataPageOffset ≠ (first.header.start : Int) then .error (wrap (atFrame 0 first .dataOffset))
      else do
        let data ← frames.zipIdx.mapM fun (frame, ordinal) => plan frame ordinal
        let declared := (data.map (·.params.numValues)).sum
        if declared ≠ rows then .error (wrap (.rowCount rows declared))
        else .ok ⟨selected, data⟩

def checkGroup (limits : Limits) (bound : Bound) (index : Nat) : Except GroupError CheckedGroup :=
  checkGroupWith id (fun frame ordinal => (planData bound frame).mapError (atFrame ordinal frame))
    limits bound index

/-- A checked GZIP plan uses the original selected bytes, count and offsets. -/
structure GroupWire (limits : Limits) (bound : Bound) (index : Nat) (checked : CheckedGroup)
    (admitted : DataPage → Prop := fun page => planData bound page.frame = .ok page) : Prop where
  selected : selectChunk bound index = .ok checked.selection
  codec : checked.selection.column.metadata.codec = Payload.Codec.gzip.id
  storedCap : checked.selection.span.stop - checked.selection.span.start ≤ limits.maxStoredChunkBytes
  expandedCap : (checked.frames.map (·.value.uncompressedSize)).sum ≤ limits.maxExpandedChunkBytes
  frames : Page.readChunk limits.framing bound.snapshot.bytes checked.selection.span = .ok checked.frames
  chain : Page.Chain checked.selection.span checked.selection.span.start checked.selection.span.stop checked.frames
  dataOffset : checked.data.head?.map (fun page => (page.frame.header.start : Int)) =
    some checked.selection.column.metadata.dataPageOffset
  data : ∀ page ∈ checked.data, admitted page
  rows : (checked.data.map (·.params.numValues)).sum = checked.selection.group.numRows.toNat

/-- Verify the outer Parquet CRC over the entire stored page before
selecting the scalar page layout and decoding its payload. -/
def decodePage (limits : Limits) (source : Bytes) (page : DataPage) (ordinal : Nat) :
    Except GroupError Slots := do
  let _ ← (Page.Checksum.verify limits.scalar.compressedBytes source page.frame).mapError
    (atFrame ordinal page.frame ∘ .checksum)
  (ScalarPage.decode .int32 page.params limits.scalar
    (Page.Checksum.payloadBytes source page.frame)).mapError (atFrame ordinal page.frame ∘ .scalar)

def PageWire (limits : Limits) (source : Bytes) (page : DataPage) (slots : Slots) : Prop :=
  ∃ status, Page.Checksum.verify limits.scalar.compressedBytes source page.frame = .ok status ∧
    ScalarPage.decode .int32 page.params limits.scalar
      (Page.Checksum.payloadBytes source page.frame) = .ok slots

def readGroup (limits : Limits) (bound : Bound) (index : Nat) : Except GroupError Slots := do
  let checked ← checkGroup limits bound index
  let pages ← checked.data.zipIdx.mapM fun (page, ordinal) =>
    decodePage limits bound.snapshot.bytes page ordinal
  return pages.flatten

def trace (limits : Limits) (bound : Bound) :
    Arrow.Events.Trace (Events.schema bound) Date.Events.Cell Error :=
  Events.traceWith bound (readGroup limits bound) .groupFailure

def readAll (input : Snapshot.Limits) (limits : Limits) (ordinal : Nat) (bytes : Bytes) :
    Arrow.Events.EventStream String Date.Events.Cell Error :=
  ((openLeaf input bytes ordinal).mapError .openFailure).map fun bound =>
    ⟨Events.schema bound, trace limits bound⟩

/-- Emit complete Date32 IPC only after the checked DATE source reaches EOF. -/
def toIpc (input : Snapshot.Limits) (limits : Limits) (output : Arrow.ObservationLimits)
    (ordinal : Nat) (bytes : Bytes) : Except IpcError KBytes := do
  let bound ← (openLeaf input bytes ordinal).mapError (.source ∘ .openFailure)
  Events.emitWith output bound .source .closed .writer (trace limits bound)

end Silmaril.Formats.Parquet.Date.Leaf.Gzip
