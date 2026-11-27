module

public import Silmaril.Formats.Compression.Brotli.Execute.InsertCopy.Defs
public import Silmaril.Formats.Compression.Brotli.Literal.Switch.Defs

/-! Execute a compressed meta-block payload with independent literal
    and insert-and-copy switching and a single distance block type. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Brotli.Execute.LiteralSwitch

open Huffman.Description (Table)

inductive Error where
  | distanceBlockTypes (bit : Nat)
  | bounds (bit : Nat) (reason : Execute.Error)
  | insertCopySwitch (reason : BlockTypes.Switch.Error)
  | commandTree (bit ordinal : Nat)
  | command (bit : Nat) (reason : Command.Error)
  | literal (reason : Literal.Switch.Error)
  | tail (bit : Nat) (reason : Execute.Error)
  deriving DecidableEq, Repr

def Error.bit : Error → Nat
  | .distanceBlockTypes bit | .bounds bit _ | .commandTree bit _ | .command bit _ | .tail bit _ => bit
  | .insertCopySwitch reason => reason.bit
  | .literal reason => reason.bit

def remainingBits (limit : Nat) (before after : LSBReader) : Nat :=
  limit - (after.totalRead - before.totalRead)

structure Prefix where
  command : Command.Value
  runs : BlockTypes.Switch.State

def Prefix.literalState (pref : Prefix) (initial : InsertCopy.State) : Literal.Switch.State :=
  ⟨initial.execution.literalHistory, pref.runs⟩

/-- Preflight and read the command. The insertion's entire output
    debit is checked before any literal or literal switch is attempted. -/
def readPrefix (header : CompressedHeader.Header) (block : Block) (limits : Limits)
    (initial : InsertCopy.State) (before : LSBReader) : Except Error (Prefix × LSBReader) :=
  match header.initial.controls.distance with
  | .multiple .. => .error (.distanceBlockTypes before.totalRead)
  | .single =>
    if block.windowBits < 10 ∨ 24 < block.windowBits then .error (.bounds before.totalRead .window)
    else if initial.execution.output.size < block.start ∨ block.endOutput ≤ initial.execution.output.size then
      .error (.bounds before.totalRead .metaBlockExtent)
    else if limits.output < initial.execution.output.size then .error (.bounds before.totalRead .outputLimit)
    else do
      let (runs, atCommand) ←
        (BlockTypes.Switch.select header.initial.controls .insertCopy limits.bits initial.runs before).mapError
          Error.insertCopySwitch
      let ordinal := runs.insertCopy.current
      let some tree := header.insertCopyTrees[ordinal]? | throw (.commandTree atCommand.totalRead ordinal)
      let (command, atLiteral) ←
        (Command.read tree (remainingBits limits.bits before atCommand) atCommand).mapError
          (Error.command atCommand.totalRead)
      let produced := initial.execution.output.size + command.insertLength
      if block.endOutput < produced then .error (.bounds atLiteral.totalRead .metaBlockExtent)
      else if limits.output < produced then .error (.bounds atLiteral.totalRead .outputLimit)
      else .ok (⟨command, runs⟩, atLiteral)

def read (header : CompressedHeader.Header) (block : Block) (limits : Limits)
    (initial : InsertCopy.State) (before : LSBReader) : Except Error (InsertCopy.Result × LSBReader) := do
  let (pref, atLiterals) ← readPrefix header block limits initial before
  let (literals, state, atTail) ←
    (Literal.Switch.read header pref.command.insertLength (remainingBits limits.bits before atLiterals)
      (pref.literalState initial) atLiterals).mapError Error.literal
  if initial.execution.output.size + literals.length = block.endOutput then
    let output := initial.execution.output ++ literals.toArray
    return (⟨⟨⟨output, initial.execution.ring⟩, pref.command, none⟩, state.runs⟩, atTail)
  else
    let (executed, after) ←
      (Execute.Internal.copyTail header block limits initial.execution pref.command literals
        (remainingBits limits.bits before atTail) atTail).mapError (Error.tail atTail.totalRead)
    return (⟨executed, state.runs⟩, after)

structure PrefixWire (header : CompressedHeader.Header) (initial : InsertCopy.State) (bits : List Bool)
    (pref : Prefix) : Prop where
  literal : pref.runs.literal = initial.runs.literal
  distance : pref.runs.distance = initial.runs.distance
  parts : ∃ switchBits commandBits tree,
    bits = switchBits ++ commandBits ∧
    BlockTypes.Switch.Wire header.initial.controls.insertCopy initial.runs.insertCopy switchBits pref.runs.insertCopy ∧
    header.insertCopyTrees[pref.runs.insertCopy.current]? = some tree ∧ Command.Wire tree commandBits pref.command

structure Wire (header : CompressedHeader.Header) (block : Block) (initial : InsertCopy.State)
    (bits : List Bool) (result : InsertCopy.Result) : Prop where
  distanceSingle : header.initial.controls.distance = .single
  parts : ∃ prefixBits literalBits tailBits pref literalState literals matched,
    bits = prefixBits ++ literalBits ++ tailBits ∧ PrefixWire header initial prefixBits pref ∧
    Literal.Switch.Wire header (pref.literalState initial) literalBits literals literalState ∧
    literals.length = pref.command.insertLength ∧
    result.execution.command = pref.command ∧ result.runs = literalState.runs ∧
    TailWire header block pref.command initial.execution.ring (initial.execution.output.toList ++ literals)
      tailBits matched result.execution.distance result.execution.state.ring ∧
    result.execution.state.output.toList = initial.execution.output.toList ++ literals ++ matched

/-- The source and successful prefix for an operation following the
    command-symbol stage. -/
structure CommandPrefix (header : CompressedHeader.Header) (block : Block) (limits : Limits)
    (initial : InsertCopy.State) (before atLiterals : LSBReader) (input suffix : List Bool) (pref : Prefix) : Prop where
  read : readPrefix header block limits initial before = .ok (pref, atLiterals)
  extent : ∃ used, PrefixWire header initial used pref ∧
    Literal.Switch.Source before atLiterals input used suffix ∧ used.length ≤ limits.bits

inductive Failure (header : CompressedHeader.Header) (block : Block) (limits : Limits)
    (initial : InsertCopy.State) (before : LSBReader) (input : List Bool) : Error → Prop where
  | beforeLiterals {reason : Error} : readPrefix header block limits initial before = .error reason →
      Failure header block limits initial before input reason
  | literal {pref : Prefix} {cursor : LSBReader} {suffix : List Bool} {reason : Literal.Switch.Error} :
      CommandPrefix header block limits initial before cursor input suffix pref →
      Literal.Switch.Failure header pref.command.insertLength 0 (remainingBits limits.bits before cursor)
        (pref.literalState initial) cursor suffix reason →
      Failure header block limits initial before input (.literal reason)
  | tail {pref : Prefix} {atLiterals atTail : LSBReader} {suffix used tail : List Bool}
      {bytes : List UInt8} {state : Literal.Switch.State} {reason : Execute.Error} :
      CommandPrefix header block limits initial before atLiterals input suffix pref →
      Literal.Switch.read header pref.command.insertLength (remainingBits limits.bits before atLiterals)
        (pref.literalState initial) atLiterals = .ok (bytes, state, atTail) →
      Literal.Switch.Source atLiterals atTail suffix used tail →
      initial.execution.output.size + bytes.length ≠ block.endOutput →
      Execute.Internal.copyTail header block limits initial.execution pref.command bytes
        (remainingBits limits.bits before atTail) atTail = .error reason →
      Failure header block limits initial before input (.tail atTail.totalRead reason)

inductive BlockError where
  | initialOutput (bit : Nat)
  | command (index : Nat) (reason : Error)
  | fuel (index bit : Nat)
  deriving DecidableEq, Repr

namespace Internal

def run (header : CompressedHeader.Header) (block : Block) (limits : Limits) (origin : LSBReader) :
    Nat → Nat → InsertCopy.State → LSBReader → Except BlockError (InsertCopy.State × LSBReader)
  | fuel, index, state, before =>
    if state.execution.output.size = block.endOutput then .ok (state, before)
    else match fuel with
    | 0 => .error (.fuel index before.totalRead)
    | fuel + 1 => do
      let (result, after) ←
        (read header block {limits with bits := remainingBits limits.bits origin before} state before).mapError
          (BlockError.command index)
      run header block limits origin fuel (index + 1) result.state after

end Internal

/-- Bounded exact-output payload execution. Decoding a new compressed
    meta-block resets the category runs and inherits bytes and distances. -/
def readBlock (header : CompressedHeader.Header) (window length : Nat) (limits : Limits)
    (initial : Execute.State) (before : LSBReader) : Except BlockError (InsertCopy.State × LSBReader) :=
  if limits.output < initial.output.size then .error (.initialOutput before.totalRead)
  else Internal.run header ⟨window, initial.output.size, length⟩ limits before length 0
    (InsertCopy.State.start header initial) before

inductive CommandsWire (header : CompressedHeader.Header) (block : Block) :
    InsertCopy.State → List Bool → List (List UInt8) → InsertCopy.State → Prop where
  | done {state : InsertCopy.State} : state.execution.output.size = block.endOutput →
      CommandsWire header block state [] [] state
  | step {initial final : InsertCopy.State} {result : InsertCopy.Result} {head tail : List Bool}
      {chunk : List UInt8} {chunks : List (List UInt8)} :
      Wire header block initial head result →
      result.execution.state.output.toList = initial.execution.output.toList ++ chunk → 0 < chunk.length →
      CommandsWire header block result.state tail chunks final →
      CommandsWire header block initial (head ++ tail) (chunk :: chunks) final

/-- Successful earlier commands thread the chosen runs and original
    source cursors before the first failed command. -/
inductive BlockFailure (header : CompressedHeader.Header) (block : Block) (limits : Limits)
    (origin : LSBReader) (command : Nat) (reason : Error) :
    Nat → Nat → InsertCopy.State → LSBReader → List Bool → Prop where
  | here {fuel : Nat} {state : InsertCopy.State} {before : LSBReader} {input : List Bool} :
      read header block {limits with bits := remainingBits limits.bits origin before} state before = .error reason →
      Failure header block {limits with bits := remainingBits limits.bits origin before} state before input reason →
      BlockFailure header block limits origin command reason (fuel + 1) command state before input
  | next {fuel index : Nat} {state : InsertCopy.State} {result : InsertCopy.Result} {before after : LSBReader}
      {input used suffix : List Bool} :
      read header block {limits with bits := remainingBits limits.bits origin before} state before = .ok (result, after) →
      Wire header block state used result → Literal.Switch.Source before after input used suffix →
      BlockFailure header block limits origin command reason fuel (index + 1) result.state after suffix →
      BlockFailure header block limits origin command reason (fuel + 1) index state before input

end Silmaril.Formats.Compression.Brotli.Execute.LiteralSwitch
