module

public import Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Defs

/-! Execute a compressed Brotli meta-block payload with all three
    block-switch categories and a dictionary-free copy profile. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch

open LiteralSwitch (remainingBits)

inductive BlockError where
  | initialOutput (bit : Nat)
  | command (index : Nat) (reason : Error)
  | fuel (index bit : Nat)
  deriving DecidableEq, Repr

def BlockError.bit : BlockError → Nat
  | .initialOutput bit | .fuel _ bit => bit
  | .command _ reason => reason.bit

/-- Read a payload after its checked compressed header. MLEN measures
    new bytes, while the output cap includes incoming history. Each
    block initializes all three runs and inherits history and the ring. -/
def readBlock (header : CompressedHeader.Header) (window length : Nat) (limits : Limits)
    (initial : Execute.State) (before : LSBReader) : Except BlockError (InsertCopy.State × LSBReader) :=
  if limits.output < initial.output.size then .error (.initialOutput before.totalRead)
  else
    let block : Block := ⟨window, initial.output.size, length⟩
    LiteralSwitch.Internal.runWith (read header block) BlockError.command BlockError.fuel block limits before
      length 0 (InsertCopy.State.start header initial) before

/-- Each command accounts for its original bits and its appended bytes,
    and strictly reduces the number of bytes remaining in this block. -/
inductive CommandsWire (header : CompressedHeader.Header) (block : Block) :
    InsertCopy.State → List Bool → List (List UInt8) → InsertCopy.State → Prop where
  | done {state : InsertCopy.State} : state.execution.output.size = block.endOutput →
      CommandsWire header block state [] [] state
  | step {initial final : InsertCopy.State} {result : InsertCopy.Result} {head tail : List Bool}
      {chunk : List UInt8} {chunks : List (List UInt8)} :
      Wire header block initial head result →
      result.execution.state.output.toList = initial.execution.output.toList ++ chunk →
      block.endOutput - result.execution.state.output.size < block.endOutput - initial.execution.output.size →
      CommandsWire header block result.state tail chunks final →
      CommandsWire header block initial (head ++ tail) (chunk :: chunks) final

/-- Zero-based command index and successful prefixes in wire order.
    Each preceding command advances from its actual state and cursor. -/
inductive BlockFailure (header : CompressedHeader.Header) (block : Block) (limits : Limits)
    (origin : LSBReader) (command : Nat) (reason : Error) :
    Nat → Nat → InsertCopy.State → LSBReader → List Bool → Prop where
  | here {fuel : Nat} {state : InsertCopy.State} {before : LSBReader} {input : List Bool} :
      state.execution.output.size ≠ block.endOutput →
      read header block {limits with bits := remainingBits limits.bits origin before} state before = .error reason →
      Failure header block {limits with bits := remainingBits limits.bits origin before} state before input reason →
      BlockFailure header block limits origin command reason (fuel + 1) command state before input
  | next {fuel index : Nat} {state : InsertCopy.State} {result : InsertCopy.Result} {before after : LSBReader}
      {input used suffix : List Bool} :
      state.execution.output.size ≠ block.endOutput →
      read header block {limits with bits := remainingBits limits.bits origin before} state before = .ok (result, after) →
      Wire header block state used result → Literal.Switch.Source before after input used suffix →
      BlockFailure header block limits origin command reason fuel (index + 1) result.state after suffix →
      BlockFailure header block limits origin command reason (fuel + 1) index state before input

end Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch
