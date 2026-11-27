module

public import Silmaril.Formats.Compression.Brotli.Literal.Defs
public import Silmaril.Formats.Compression.Brotli.BlockTypes.Switch.Defs

/-! One RFC 7932 literal selection first debits the type run, then
    uses the selected type's mode and the original context map. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Brotli.Literal.Switch

open Huffman.Description (Table)

structure State where
  history : History
  runs : BlockTypes.Switch.State
  deriving DecidableEq, Repr

def State.push (state : State) (byte : UInt8) (runs : BlockTypes.Switch.State) : State :=
  ⟨state.history.push byte, runs⟩

def tableFor (header : CompressedHeader.Header) (history : History) (type : Nat) : Except Literal.Error Table := do
  let some mode := header.initial.fields.modes[type]? | throw .modes
  let index := 64 * type + (contextId mode history).val
  let some ordinal := lookup header.literalMap index | throw .contextEntry
  let some table := header.literalTrees[ordinal]? | throw .treeIndex
  return table

structure TableWire (header : CompressedHeader.Header) (history : History) (type : Nat) (table : Table) : Prop where
  parts : ∃ mode ordinal,
    header.initial.fields.modes[type]? = some mode ∧
    lookup header.literalMap (64 * type + (contextId mode history).val) = some ordinal ∧
    header.literalTrees[ordinal]? = some table

inductive StepError where
  | switch (reason : BlockTypes.Switch.Error)
  | literal (bit : Nat) (reason : Literal.Error)
  deriving DecidableEq, Repr

def StepError.bit : StepError → Nat
  | .switch reason => reason.bit
  | .literal bit _ => bit

structure Error where
  index : Nat
  cause : StepError
  deriving DecidableEq, Repr

def Error.bit (error : Error) : Nat := error.cause.bit

def readOne (header : CompressedHeader.Header) (bitLimit : Nat) (initial : State)
    (before : LSBReader) : Except StepError (UInt8 × State × LSBReader) := do
  let (runs, atCode) ←
    (BlockTypes.Switch.select header.initial.controls .literal bitLimit initial.runs before).mapError StepError.switch
  let table ← (tableFor header initial.history runs.literal.current).mapError (StepError.literal atCode.totalRead)
  let (byte, after) ← (Literal.readByte table (bitLimit - (atCode.totalRead - before.totalRead)) atCode).mapError
    (StepError.literal atCode.totalRead)
  return (byte, initial.push byte runs, after)

/-- The switch bits precede selection of the original context table
    and the byte's own Huffman code. -/
structure StepWire (header : CompressedHeader.Header) (initial : State) (used : List Bool)
    (byte : UInt8) (final : State) : Prop where
  insertCopy : final.runs.insertCopy = initial.runs.insertCopy
  distance : final.runs.distance = initial.runs.distance
  history : final.history = initial.history.push byte
  parts : ∃ switchBits table code width,
    used = switchBits ++ msbBits code width ∧
    BlockTypes.Switch.Wire header.initial.controls.literal initial.runs.literal switchBits final.runs.literal ∧
    TableWire header initial.history final.runs.literal.current table ∧ table.alphabetSize = 256 ∧
    table.codeFor byte.toNat = some (code, width) ∧ width ≤ 15

inductive Wire (header : CompressedHeader.Header) :
    State → List Bool → List UInt8 → State → Prop where
  | done (state : State) : Wire header state [] [] state
  | step {initial next final : State} {head tail : List Bool} {byte : UInt8} {bytes : List UInt8} :
      StepWire header initial head byte next → Wire header next tail bytes final →
      Wire header initial (head ++ tail) (byte :: bytes) final

namespace Internal

def scan (header : CompressedHeader.Header) :
    Nat → Nat → Nat → State → List UInt8 → LSBReader → Except Error (List UInt8 × State × LSBReader)
  | 0, _, _, state, reversed, reader => .ok (reversed.reverse, state, reader)
  | count + 1, index, limit, state, reversed, reader => do
    let (byte, next, after) ← (readOne header limit state reader).mapError (fun reason => ⟨index, reason⟩)
    scan header count (index + 1) (limit - (after.totalRead - reader.totalRead))
      next (byte :: reversed) after

end Internal

/-- Decode the exact literal quota already checked by the command
    executor. The quota also bounds zero-bit literal work. -/
def read (header : CompressedHeader.Header) (count bitLimit : Nat) (initial : State)
    (before : LSBReader) : Except Error (List UInt8 × State × LSBReader) :=
  Internal.scan header count 0 bitLimit initial [] before

/-- The original input suffix at a later stage of the same operation. -/
structure Source (before after : LSBReader) (input used suffix : List Bool) : Prop where
  split : input = used ++ suffix
  rep : after.Rep suffix
  count : after.count < 8
  position : after.totalRead = before.totalRead + used.length

inductive FailedSymbol (header : CompressedHeader.Header) (history : History) (type limit : Nat)
    (before : LSBReader) : Literal.Error → Prop where
  | table {reason : Literal.Error} :
      tableFor header history type = .error reason → FailedSymbol header history type limit before reason
  | code {table : Table} {reason : Literal.Error} :
      tableFor header history type = .ok table → Literal.readByte table limit before = .error reason →
      FailedSymbol header history type limit before reason

inductive StepFailure (header : CompressedHeader.Header) (limit : Nat) (state : State)
    (before : LSBReader) (input : List Bool) : StepError → Prop where
  | switch {reason : BlockTypes.Switch.Error} :
      BlockTypes.Switch.Failure .literal header.initial.controls.literal limit state.runs.literal before input reason →
      StepFailure header limit state before input (.switch reason)
  | symbol {reason : Literal.Error} {runs : BlockTypes.Switch.State} {atCode : LSBReader} {used suffix : List Bool} :
      BlockTypes.Switch.select header.initial.controls .literal limit state.runs before = .ok (runs, atCode) →
      BlockTypes.Switch.Wire header.initial.controls.literal state.runs.literal used runs.literal →
      Source before atCode input used suffix → used.length ≤ limit →
      FailedSymbol header state.history runs.literal.current (limit - (atCode.totalRead - before.totalRead))
        atCode reason →
      StepFailure header limit state before input (.literal atCode.totalRead reason)

/-- Every earlier literal was emitted before the failing selection or
    code read. No successor is returned for the failed command. -/
inductive Failure (header : CompressedHeader.Header) :
    Nat → Nat → Nat → State → LSBReader → List Bool → Error → Prop where
  | here {count index limit : Nat} {state : State} {before : LSBReader}
      {input : List Bool} {cause : StepError} :
      StepFailure header limit state before input cause →
      Failure header (count + 1) index limit state before input ⟨index, cause⟩
  | next {count index limit : Nat} {state next : State} {before after : LSBReader}
      {input used suffix : List Bool} {byte : UInt8} {error : Error} :
      readOne header limit state before = .ok (byte, next, after) →
      StepWire header state used byte next → Source before after input used suffix → used.length ≤ limit →
      Failure header count (index + 1) (limit - (after.totalRead - before.totalRead)) next after suffix error →
      Failure header (count + 1) index limit state before input error

end Silmaril.Formats.Compression.Brotli.Literal.Switch
