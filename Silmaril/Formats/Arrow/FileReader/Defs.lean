module

public import Silmaril.Formats.Arrow.Body.Defs
import Init.Omega

/-! Random-access Arrow IPC V5 files over one immutable byte carrier.
The file adds a magic, a duplicate schema and an ordered footer index to
the existing modern schema, record-batch and EOS framing. -/

@[expose] public section

namespace Silmaril.Formats.Arrow.FileReader

/-- The six bytes `ARROW1` as a little-endian word. -/
def magic : Nat := 0x31574f525241

/-- A bounded footer interval ending just before the length word and magic. -/
structure FooterSpan (input : KBytes) where
  start : Nat
  length : Nat
  extent : start + length + 10 = input.len
  aligned : start % 8 = 0
  positive : 0 < length
  source : input.wf = true

def readFooterSpan (limits : Limits) (input : KBytes) : Except Error (FooterSpan input) :=
  if source : input.wf ≠ true then .error (.malformed .source)
  else if input.len < 18 then .error (.malformed .truncated)
  else if input.read 0 6 ≠ magic || input.read (input.len - 6) 6 ≠ magic then
    .error (.malformed .source)
  else if input.read 6 2 ≠ 0 then .error (.malformed .alignment)
  else
    let length := input.read (input.len - 10) 4
    if positive : length = 0 then .error (.malformed .metadataLength)
    else if length ≥ 2^31 then .error (.malformed .metadataLength)
    else if length > limits.metadataBytes then .error (.limit .metadataBytes)
    else if fits : length + 18 > input.len then .error (.malformed .truncated)
    else
      let start := input.len - 10 - length
      if aligned : start % 8 = 0 then .ok ⟨start, length, by omega, aligned, by omega, Decidable.not_not.mp source⟩
      else .error (.malformed .alignment)

/-- Blocks follow the embedded stream in index order. The metadata length
includes its prefix. The first byte after the last block is the EOS marker. -/
def BlocksFit (footerStart : Nat) : Nat → List FileBlock → Prop
  | cursor, [] => cursor + 8 = footerStart
  | cursor, block :: rest =>
    block.offset = cursor ∧ block.offset % 8 = 0 ∧
      8 ≤ block.metadataLength ∧ block.metadataLength % 8 = 0 ∧
      block.bodyLength % 8 = 0 ∧ block.endOffset ≤ footerStart ∧
      BlocksFit footerStart block.endOffset rest

instance (footerStart cursor : Nat) (blocks : List FileBlock) :
    Decidable (BlocksFit footerStart cursor blocks) :=
  match blocks with
  | [] => inferInstanceAs (Decidable (cursor + 8 = footerStart))
  | block :: rest =>
    letI := instDecidableBlocksFit footerStart block.endOffset rest
    show Decidable (_ ∧ _) from inferInstance

/-- The index and its proof are tied to the input that was checked. -/
structure Index (input : KBytes) where
  span : FooterSpan input
  footer : FileFooter
  schemaEnd : Nat
  fits : BlocksFit span.start schemaEnd footer.blocks

/-- Validate the footer schema against the embedded schema and check the
whole index before any indexed metadata or body is sliced. -/
def readIndex (limits : Limits) (input : KBytes) : Except Error (Index input) := do
  let span ← readFooterSpan limits input
  let footer ← readFileFooter limits (input.slice span.start span.length)
  let .metadata size ← readEnvelope limits input 8 | throw (.malformed .schemaOrder)
  let schemaEnd := 16 + size
  if schemaEnd + 8 > span.start then throw (.malformed .truncated)
  let message ← readMessage limits (input.slice 16 size)
  let .schema fields := message.header | throw (.malformed .schemaOrder)
  if message.bodyLength ≠ 0 then throw (.malformed .bodyLength)
  if fields ≠ footer.fields then throw (.malformed .schemaOrder)
  if fits : BlocksFit span.start schemaEnd footer.blocks then
    let .eos ← readEnvelope limits input (span.start - 8) | throw (.malformed .trailingBytes)
    return ⟨span, footer, schemaEnd, fits⟩
  else
    throw (.malformed .batchLayout)

/-- Read a record from a checked index. Its footer lengths must agree with
the modern prefix and the Message table. -/
def Index.readBlock {input : KBytes} (index : Index input) (limits : Limits)
    (block : FileBlock) (_member : block ∈ index.footer.blocks) :
    Except Error (BatchFrame index.footer.fields) := do
  let .metadata size ← readEnvelope limits input block.offset | throw (.malformed .schemaOrder)
  if 8 + size ≠ block.metadataLength then throw (.malformed .metadataLength)
  let message ← readMessage limits (input.slice (block.offset + 8) size)
  let .recordBatch metadata := message.header | throw (.malformed .schemaOrder)
  if message.bodyLength ≠ block.bodyLength then throw (.malformed .bodyLength)
  let body ← readBody limits input (block.offset + block.metadataLength) block.bodyLength
  validateBatch index.footer.fields metadata body

def Index.readBatches {input : KBytes} (index : Index input) (limits : Limits) :
    Except Error (List (BatchFrame index.footer.fields)) :=
  index.footer.blocks.attach.mapM (fun block => index.readBlock limits block.val block.property)

/-- An absent index entry gives `none`. A present malformed record is an error. -/
def Index.readBatchAt {input : KBytes} (index : Index input) (limits : Limits) (n : Nat) :
    Except Error (Option (BatchFrame index.footer.fields)) :=
  index.footer.blocks.attach[n]?.mapM (fun block => index.readBlock limits block.val block.property)

def Index.readRowsAt {input : KBytes} (index : Index input) (limits : ObservationLimits) (n : Nat) :
    Except Error (Option (List Row)) := do
  let batch ← index.readBatchAt limits.ipc n
  batch.mapM (decodeBatch limits)

structure ObservedFile where
  fields : List Field
  batches : List (List Row)
  deriving DecidableEq, Repr

/-- Materialize ordered file observations after checking the aggregate budget. -/
def readRows (limits : ObservationLimits) (input : KBytes) : Except Error ObservedFile := do
  let index ← readIndex limits.ipc input
  let batches ← index.readBatches limits.ipc
  Body.checkBudget limits index.footer.fields.length (batches.map (·.metadata.rowCount)).sum
  return ⟨index.footer.fields, ← batches.mapM (decodeBatch limits)⟩

end Silmaril.Formats.Arrow.FileReader
