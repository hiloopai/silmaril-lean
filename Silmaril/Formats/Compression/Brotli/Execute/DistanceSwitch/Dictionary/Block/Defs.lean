module

public import Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Block.Defs
public import Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary.Defs

/-! A checked compressed meta-block payload with the RFC 7932 static dictionary. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary

open LiteralSwitch (remainingBits)
open Literal.Switch (Source)

structure BlockResult where
  state : InsertCopy.State
  cursor : LSBReader
  remainingCommands : Nat

/-- The same bounded payload loop returns its unused command slots to a caller
    composing multiple meta-blocks. An empty emission still takes a slot. -/
def readBlockCounted (header : CompressedHeader.Header) (window length commandCap : Nat) (limits : Limits)
    (initial : Execute.State) (before : LSBReader) : Except BlockError BlockResult :=
  if limits.output < initial.output.size then .error (.initialOutput before.totalRead)
  else
    let block : Block := ⟨window, initial.output.size, length⟩
    LiteralSwitch.Internal.runWithResult (fun remaining state cursor => ⟨state, cursor, remaining⟩)
      (read header block) BlockError.command BlockError.fuel block limits before
      commandCap 0 (InsertCopy.State.start header initial) before

/-- Read a payload after its checked header and project its execution state
    and cursor. The completed block needs no additional command slot. -/
def readBlock (header : CompressedHeader.Header) (window length commandCap : Nat) (limits : Limits)
    (initial : Execute.State) (before : LSBReader) : Except BlockError (InsertCopy.State × LSBReader) :=
  (readBlockCounted header window length commandCap limits initial before).map fun result =>
    (result.state, result.cursor)

/-- Each step connects an original command, its reader transition, and
    its actual output chunk to the input state of the following step. -/
inductive CommandsWire (header : CompressedHeader.Header) (block : Block) (limits : Limits) (origin : LSBReader) :
    InsertCopy.State → LSBReader → List Bool → List Bool → List (List UInt8) → InsertCopy.State → LSBReader → Prop where
  | done {state : InsertCopy.State} {cursor : LSBReader} {input : List Bool} :
      state.execution.output.size = block.endOutput →
      CommandsWire header block limits origin state cursor input input [] state cursor
  | step {initial final : InsertCopy.State} {result : InsertCopy.Result} {before after stop : LSBReader}
      {input used tail suffix : List Bool} {chunk : List UInt8} {chunks : List (List UInt8)} :
      read header block {limits with bits := remainingBits limits.bits origin before} initial before =
        .ok (result, after) →
      Wire header block {limits with bits := remainingBits limits.bits origin before} initial used result →
      Source before after input used tail →
      result.execution.state.output.toList = initial.execution.output.toList ++ chunk →
      CommandsWire header block limits origin result.state after tail suffix chunks final stop →
      CommandsWire header block limits origin initial before input suffix (chunk :: chunks) final stop

/-- A failure follows exactly the successful preceding commands. Fuel
    exhaustion is recorded at the first pending command without a slot. -/
inductive FailurePath (header : CompressedHeader.Header) (block : Block) (limits : Limits) (origin : LSBReader) :
    Nat → Nat → InsertCopy.State → LSBReader → List Bool → BlockError → Prop where
  | fuel {index : Nat} {state : InsertCopy.State} {before : LSBReader} {input : List Bool} :
      state.execution.output.size ≠ block.endOutput →
      FailurePath header block limits origin 0 index state before input (.fuel index before.totalRead)
  | command {fuel index : Nat} {state : InsertCopy.State} {before : LSBReader} {input : List Bool}
      {reason : Error} :
      state.execution.output.size ≠ block.endOutput →
      read header block {limits with bits := remainingBits limits.bits origin before} state before = .error reason →
      Failure header block {limits with bits := remainingBits limits.bits origin before} state before input reason
        Internal.finishCopy →
      FailurePath header block limits origin (fuel + 1) index state before input (.command index reason)
  | next {fuel index : Nat} {state : InsertCopy.State} {result : InsertCopy.Result} {before after : LSBReader}
      {input used tail : List Bool} {error : BlockError} :
      state.execution.output.size ≠ block.endOutput →
      read header block {limits with bits := remainingBits limits.bits origin before} state before = .ok (result, after) →
      Wire header block {limits with bits := remainingBits limits.bits origin before} state used result →
      Source before after input used tail →
      FailurePath header block limits origin fuel (index + 1) result.state after tail error →
      FailurePath header block limits origin (fuel + 1) index state before input error

end Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Dictionary
