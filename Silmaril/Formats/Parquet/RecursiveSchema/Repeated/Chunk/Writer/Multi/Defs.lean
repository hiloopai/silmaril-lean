module

public import Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.Defs

/-! Native unindexed signed PLAIN V1 chunk emission from an explicit page partition. -/

namespace Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.Multi

open Repeated (Leaf)
open Repeated.Rows (Atom)

@[expose] public section

structure Input where
  leaf : Leaf
  rows : Nat
  pages : List (List Atom)
  checksum : Bool := false
  group : Nat := 0
  column : Nat := 0

/-- Each level entry is one value slot in ColumnMetaData, including nulls. -/
def Input.slots (input : Input) : Nat := (input.pages.map List.length).sum

/-- A zero-row group carries exactly one empty page per leaf. In a
positive group every page contributes at least one slot. -/
def Input.validPartition (input : Input) : Bool :=
  match input.rows, input.pages with
  | 0, [[]] => true
  | 0, _ => false
  | _ + 1, [] => false
  | _ + 1, _ :: _ => input.pages.all (fun atoms => !atoms.isEmpty)

inductive Error where
  | partition
  | pageLimit (actual limit : Nat)
  | slotLimit (actual limit : Nat)
  | rowLimit (actual limit : Nat)
  | page (ordinal : Nat) (original : Writer.Error)
  | readback (original : Chunk.Error)
  | readbackMismatch
  deriving DecidableEq, Repr

def Input.page (input : Input) (start : State) (atoms : List Atom) : Writer.Input :=
  ⟨input.leaf, start, atoms, input.checksum⟩

def remainingLimits (limits : Limits) (start : Cursor) : Limits :=
  { limits with maxChunkBytes := limits.maxChunkBytes - start.byte }

def frameSize (piece : Writer.Output) : Nat :=
  piece.page.headerBytes.length + piece.page.body.length

def advance (start : Cursor) (page : Writer.Output) : Cursor :=
  ⟨start.page + 1, start.byte + frameSize page, page.after⟩

structure Packed where
  pieces : List Writer.Output
  stop : Cursor

def initial : Cursor := ⟨0, 0, {}⟩

/-- The byte remainder and state are cumulative. Each page is serialized
once, leaving the strict reader to certify the assembled chunk. -/
def packPages (limits : Limits) (input : Input) : List (List Atom) → Cursor →
    List Writer.Output → Except Error Packed
  | [], start, reversed => .ok ⟨reversed.reverse, start⟩
  | atoms :: rest, start, reversed => do
    let page ← (Writer.serialize (remainingLimits limits start) (input.page start.state atoms)).mapError
      (.page start.page)
    packPages limits input rest (advance start page) (page :: reversed)

def assemble (pieces : List Writer.Output) : Bytes :=
  pieces.foldl (fun acc page => acc.append page.wire) .empty

def serialize (limits : Limits) (input : Input) : Except Error Packed :=
  if !input.validPartition then .error .partition
  else if input.pages.length > limits.framing.maxPages then
    .error (.pageLimit input.pages.length limits.framing.maxPages)
  else if input.slots > limits.maxSlots then .error (.slotLimit input.slots limits.maxSlots)
  else if input.rows > limits.maxRows then .error (.rowLimit input.rows limits.maxRows)
  else packPages limits input input.pages initial []

def carrier (input : Input) (wire : Bytes) : Carrier :=
  ⟨wire, ⟨0, wire.length⟩, input.leaf, ⟨input.group, input.column, input.leaf.site.location.path⟩,
    input.slots, input.rows⟩

def frameAt (offset : Nat) (piece : Writer.Output) : Page.Frame :=
  let payload := offset + piece.page.headerBytes.length
  ⟨piece.page.header, ⟨offset, payload⟩, ⟨payload, offset + frameSize piece⟩⟩

/-- Compare each strict observation to the corresponding original page
partition and serialized piece at the cumulative reader cursor. -/
def agrees (input : Input) (stop : Cursor) :
    Cursor → List (List Atom) → List Writer.Output → List ObservedPage → Bool
  | cursor, [], [], [] => decide (cursor = stop)
  | cursor, atoms :: rest, piece :: pieces, page :: pages =>
    decide (page.start = cursor ∧ page.frame = frameAt cursor.byte piece) &&
    Writer.agrees (input.page cursor.state atoms) piece.after page.decoded &&
    agrees input stop (cursor.advance page) rest pieces pages
  | _, _, _, _ => false

structure Output where
  wire : Bytes
  observation : Observation
  after : State

/-- The first data-page header is at the start of this chunk, even for a
zero-row group. Add the eventual in-file chunk start to relocate it. -/
def Output.dataPageOffset (_ : Output) : Nat := 0

def Output.totalCompressedSize (output : Output) : Nat := output.wire.length

def Output.totalUncompressedSize (output : Output) : Nat := output.wire.length

def Output.numValues (output : Output) : Nat := output.after.slot

def Output.numRows (output : Output) : Nat := output.after.rows

def Output.frames (output : Output) : List Page.Frame :=
  output.observation.pages.map (·.frame)

def certify (limits : Limits) (input : Input) (packed : Packed) : Except Error Output := do
  let wire := assemble packed.pieces
  let source := carrier input wire
  let pages ← (walk limits source limits.framing.maxPages initial []).mapError .readback
  if agrees input packed.stop initial input.pages packed.pieces pages then
    .ok ⟨wire, ⟨pages⟩, packed.stop.state⟩
  else .error .readbackMismatch

/-- Pack one bounded leaf chunk and certify it with the existing strict
unindexed chunk walk over the exact bytes that will be returned. -/
def emit (limits : Limits) (input : Input) : Except Error Output := do
  let packed ← serialize limits input
  certify limits input packed

inductive PiecesWire (limits : Limits) (input : Input) :
    Cursor → Cursor → List (List Atom) → List Writer.Output → Prop where
  | nil (cursor : Cursor) : PiecesWire limits input cursor cursor [] []
  | cons {start stop atoms rest piece pieces} :
      Writer.serialize (remainingLimits limits start) (input.page start.state atoms) = .ok piece →
      Writer.Construction (remainingLimits limits start) (input.page start.state atoms) piece →
      PiecesWire limits input (advance start piece) stop rest pieces →
      PiecesWire limits input start stop (atoms :: rest) (piece :: pieces)

structure Construction (limits : Limits) (input : Input) (packed : Packed) : Prop where
  partition : input.validPartition = true
  pageCap : input.pages.length ≤ limits.framing.maxPages
  slotCap : input.slots ≤ limits.maxSlots
  rowCap : input.rows ≤ limits.maxRows
  byteCap : (assemble packed.pieces).length ≤ limits.maxChunkBytes
  extent : packed.stop.byte = (assemble packed.pieces).length
  pieces : PiecesWire limits input initial packed.stop input.pages packed.pieces

inductive PageAgreement :
    Cursor → Cursor → List (List Atom) → List Writer.Output → List ObservedPage → Prop where
  | nil (cursor : Cursor) : PageAgreement cursor cursor [] [] []
  | cons {start stop atoms rest piece pieces page pages} :
      page.start = start →
      page.frame = frameAt start.byte piece →
      page.decoded.levels = atoms.map (·.levels) →
      page.decoded.words = atoms.map (·.word) →
      page.decoded.after = piece.after →
      PageAgreement (start.advance page) stop rest pieces pages →
      PageAgreement start stop (atoms :: rest) (piece :: pieces) (page :: pages)

/-- The strict walk covers the whole emitted carrier from a closed state.
The checked pages correspond to the exact input partition in wire order. -/
structure Readback (limits : Limits) (input : Input) (packed : Packed) (output : Output) : Prop where
  bytes : output.wire = assemble packed.pieces
  walked : walk limits (carrier input output.wire) limits.framing.maxPages initial [] =
    .ok output.observation.pages
  chain : ChainWire limits (carrier input output.wire) initial packed.stop output.observation.pages
  frames : Page.Chain ⟨0, output.wire.length⟩ 0 output.wire.length output.frames
  finalByte : packed.stop.byte = output.wire.length
  finalState : output.after = packed.stop.state
  slots : output.numValues = input.slots
  rows : output.numRows = input.rows
  agreement : PageAgreement initial packed.stop input.pages packed.pieces output.observation.pages

end

end Silmaril.Formats.Parquet.RecursiveSchema.Repeated.Chunk.Writer.Multi
