module

public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Rows.Projection.Defs
public import Silmaril.Formats.Parquet.ListFile.Writer.Defs

/-! One bounded UNCOMPRESSED PLAIN V1 page for a recursive signed leaf. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer

open Repeated (Leaf)
open Repeated.Rows (Atom)

@[expose] public section

structure Input where
  leaf : Leaf
  start : Chunk.State
  atoms : List Atom
  checksum : Bool := false

inductive Limit where
  | pages
  | slots
  | rows
  | width
  | levelBytes
  | body
  | header
  | chunk
  deriving DecidableEq, Repr

inductive Error where
  | limit (original : Limit)
  | level (original : Repeated.LevelError)
  | classification (slot : Nat)
  | continuationWithoutList (slot : Nat)
  | wordPresence (slot : Nat)
  | signedType (slot : Nat)
  | headerInteger
  | measureMismatch
  | framing (original : Page.Error)
  | frameMismatch
  | decode (original : Chunk.PageCause)
  | readbackMismatch
  deriving DecidableEq, Repr

/-- Singleton RLE includes one header octet and the fixed-width value. -/
def sectionSize (maximum count : Nat) : Nat :=
  if maximum = 0 then 0
  else 4 + count * (1 + Hybrid.repeatedByteCount (Chunk.bitWidth maximum))

def encodeSection (maximum : Nat) (levels : List Nat) : Bytes :=
  if maximum = 0 then .empty else
    ListFile.Writer.PageEncoding.lengthPrefixed
      (ListFile.Writer.PageEncoding.runs (Chunk.bitWidth maximum) levels)

def wordOctets : Chunk.Word → List UInt8
  | .int32 value => Plain.writeUInt32Word value.toUInt32
  | .int64 value => Plain.writeUInt64Word value.toUInt64

def body (input : Input) : Bytes :=
  let reps := encodeSection input.leaf.maxRepetition (input.atoms.map (·.levels.repetition))
  let defs := encodeSection input.leaf.maxDefinition (input.atoms.map (·.levels.definition))
  (reps.append defs).append (Plain.encodeWords wordOctets (input.atoms.filterMap (·.word)))

def checksumOf (input : Input) (payload : Bytes) : Option UInt32 :=
  if input.checksum then some (Compression.Checksum.crc32.digest payload.toList) else none

def header (input : Input) (payload : Bytes) : Page.Header :=
  ⟨payload.length, payload.length, checksumOf input payload, .dataV1 ⟨input.atoms.length, 0, 3, 3⟩⟩

/-- Validate an original atom and advance from the supplied chunk state.
Contradictory classifications and signed widths are typed refusals. -/
def admitAtom (leaf : Leaf) (state : Chunk.State) (atom : Atom) :
    Except Error Chunk.State := do
  let levels := atom.levels
  let expected ← (leaf.classify state.slot levels.repetition levels.definition).mapError .level
  if expected ≠ levels.classified then throw (.classification state.slot)
  if levels.repetition ≠ 0 && !state.live then throw (.continuationWithoutList state.slot)
  let next := state.consume leaf levels.repetition levels.definition
  match expected.presence, atom.word with
  | .absent _, none => return next
  | .value, some (.int32 _) =>
    if leaf.kind = .int32 then return next else throw (.signedType state.slot)
  | .value, some (.int64 _) =>
    if leaf.kind = .int64 then return next else throw (.signedType state.slot)
  | _, _ => throw (.wordPresence state.slot)

structure Measured (limits : Chunk.Limits) (input : Input) where
  after : Chunk.State
  bytes : Nat
  slotCap : input.start.slot + input.atoms.length ≤ limits.maxSlots
  rowCap : input.start.rows ≤ limits.maxRows ∧ after.rows ≤ limits.maxRows
  pageCap : 0 < limits.framing.maxPages
  runCap : input.atoms.length < Hybrid.runLimit ∧ input.atoms.length ≤ limits.levels.values
  levelCap : sectionSize input.leaf.maxRepetition input.atoms.length ≤ 4 + limits.levels.bytes ∧
    sectionSize input.leaf.maxDefinition input.atoms.length ≤ 4 + limits.levels.bytes
  bodyCap : bytes < 2 ^ 31 ∧ bytes ≤ limits.maxBodyBytes ∧ bytes ≤ limits.maxChunkBytes

/-- Count and validate before allocating level sections or signed bytes.
Header extent and the full frame extent are checked after CRC encoding. -/
def measure (limits : Chunk.Limits) (input : Input) : Except Error (Measured limits input) := do
  let count := input.atoms.length
  if pageCap : 0 < limits.framing.maxPages then
    if slotCap : input.start.slot + count ≤ limits.maxSlots then
      if runCap : count < Hybrid.runLimit ∧ count ≤ limits.levels.values then
        if Chunk.bitWidth input.leaf.maxRepetition > 32 ||
            Chunk.bitWidth input.leaf.maxDefinition > 32 then
          throw (.limit .width)
        let repSize := sectionSize input.leaf.maxRepetition count
        let defSize := sectionSize input.leaf.maxDefinition count
        if levelCap : repSize ≤ 4 + limits.levels.bytes ∧ defSize ≤ 4 + limits.levels.bytes then
          let after ← input.atoms.foldlM (admitAtom input.leaf) input.start
          if rowCap : input.start.rows ≤ limits.maxRows ∧ after.rows ≤ limits.maxRows then
            let present := input.atoms.countP (fun atom => atom.word.isSome)
            let bytes := repSize + defSize + present * RecursiveSchema.Chunk.wordWidth input.leaf.kind
            if bodyCap : bytes < 2 ^ 31 ∧ bytes ≤ limits.maxBodyBytes ∧ bytes ≤ limits.maxChunkBytes then
              return ⟨after, bytes, slotCap, rowCap, pageCap, runCap, levelCap, bodyCap⟩
            else throw (.limit .body)
          else throw (.limit .rows)
        else throw (.limit .levelBytes)
      else throw (.limit .slots)
    else throw (.limit .slots)
  else throw (.limit .pages)

structure Output where
  page : PlainV1Writer.Encoded
  after : Chunk.State

def Output.wire (output : Output) : Bytes := output.page.wire

def Output.frame (output : Output) : Page.Frame :=
  ⟨output.page.header, ⟨0, output.page.headerBytes.length⟩,
    ⟨output.page.headerBytes.length, output.wire.length⟩⟩

def serialize (limits : Chunk.Limits) (input : Input) : Except Error Output := do
  let measured ← measure limits input
  let payload := body input
  if payload.length ≠ measured.bytes then throw .measureMismatch
  let declared := header input payload
  let some headerBytes ← pure (PlainV1Writer.encodeHeaderWithChecksum
    input.atoms.length payload.length declared.crc) | throw .headerInteger
  if headerBytes.length > limits.framing.maxHeaderBytes then throw (.limit .header)
  if headerBytes.length + payload.length > limits.maxChunkBytes then throw (.limit .chunk)
  return ⟨⟨declared, headerBytes, payload⟩, measured.after⟩

def agrees (input : Input) (after : Chunk.State) (checked : Chunk.DecodedPage) : Bool :=
  checked.levels.isEqv (input.atoms.map (·.levels)) (fun a b => decide (a = b)) &&
  checked.words.isEqv (input.atoms.map (·.word)) (fun a b => decide (a = b)) &&
  decide (checked.after = after)

/-- Frame the entire emitted carrier and run the original page decoder
at the supplied state. The expected frame end is the exact byte length. -/
def certify (limits : Chunk.Limits) (input : Input) (output : Output) : Except Error Unit := do
  let frame ← (Page.readPage limits.framing output.wire ⟨0, output.wire.length⟩ 0).mapError .framing
  if frame ≠ output.frame then throw .frameMismatch
  let checked ← (Chunk.decodePage limits input.leaf output.wire frame input.start
    (limits.maxSlots - input.start.slot) limits.maxRows).mapError .decode
  if agrees input output.after checked then .ok () else .error .readbackMismatch

/-- Return one native page only after strict framing and exact atom readback. -/
def emit (limits : Chunk.Limits) (input : Input) : Except Error Output := do
  let output ← serialize limits input
  certify limits input output
  return output

structure Construction (limits : Chunk.Limits) (input : Input) (output : Output) : Prop where
  measured : ∃ plan, measure limits input = .ok plan ∧
    output.page.body.length = plan.bytes ∧ output.after = plan.after
  body : output.page.body = body input
  header : output.page.header = header input output.page.body
  headerBytes : PlainV1Writer.encodeHeaderWithChecksum input.atoms.length output.page.body.length
    output.page.header.crc = some output.page.headerBytes
  headerCap : output.page.headerBytes.length ≤ limits.framing.maxHeaderBytes
  frameCap : output.wire.length ≤ limits.maxChunkBytes

structure Readback (limits : Chunk.Limits) (input : Input) (output : Output) : Prop where
  frame : Page.readPage limits.framing output.wire ⟨0, output.wire.length⟩ 0 = .ok output.frame
  exact : ∃ checked, Chunk.decodePage limits input.leaf output.wire output.frame input.start
    (limits.maxSlots - input.start.slot) limits.maxRows = .ok checked ∧
    Chunk.PageWire limits input.leaf output.wire output.frame input.start
      (limits.maxSlots - input.start.slot) limits.maxRows checked ∧
    checked.levels = input.atoms.map (·.levels) ∧
    checked.words = input.atoms.map (·.word) ∧ checked.after = output.after

end

end Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer
