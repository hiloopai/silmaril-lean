module

public import Silmaril.Formats.Compression.Brotli.Execute.LiteralSwitch.Defs

/-! One bounded RFC 7932 command with independent L, I and D block-type
    runs. A dictionary address still has a typed rejection. -/

@[expose] public section

namespace Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch

open Execute.LiteralSwitch (remainingBits)
open Literal.Switch (Source)

inductive Error where
  | commandPrefix (reason : LiteralSwitch.Error)
  | literal (reason : Literal.Switch.Error)
  | distanceSwitch (reason : BlockTypes.Switch.Error)
  | distance (bit : Nat) (reason : Distance.Error)
  | copy (bit : Nat) (reason : Execute.Error)
  deriving DecidableEq, Repr

def Error.bit : Error → Nat
  | .commandPrefix reason => reason.bit
  | .literal reason => reason.bit
  | .distanceSwitch reason => reason.bit
  | .distance bit _ | .copy bit _ => bit

namespace Internal

/-- Only an explicit distance symbol debits the distance block length. -/
def select (header : CompressedHeader.Header) (command : Command.Value) (bitLimit : Nat)
    (runs : BlockTypes.Switch.State) (before : LSBReader) : Except BlockTypes.Switch.Error (BlockTypes.Switch.State × LSBReader) :=
  match command.distance with
  | .implicitZero => .ok (runs, before)
  | .explicit => BlockTypes.Switch.select header.initial.controls .distance bitLimit runs before

def resolve (header : CompressedHeader.Header) (command : Command.Value) (bounds : Distance.Bounds)
    (ring : Distance.Ring) (bitLimit : Nat) (runs : BlockTypes.Switch.State) (before : LSBReader) :
    Except Error (Distance.Result × BlockTypes.Switch.State × LSBReader) := do
  let (next, atCode) ← (select header command bitLimit runs before).mapError Error.distanceSwitch
  let (distance, after) ← (Distance.Internal.readAt header next.distance.current command bounds ring
    (remainingBits bitLimit before atCode) atCode).mapError (Error.distance atCode.totalRead)
  return (distance, next, after)

end Internal

/-- Execute one command from its I run selection through its emitted bytes.
    A final insertion reaches MLEN without selecting a distance. -/
def read (header : CompressedHeader.Header) (block : Block) (limits : Limits) (initial : InsertCopy.State)
    (before : LSBReader) : Except Error (InsertCopy.Result × LSBReader) := do
  let (pref, atLiterals) ← (LiteralSwitch.readPrefixCore header block limits initial before).mapError Error.commandPrefix
  let (literals, state, atDistance) ←
    (Literal.Switch.read header pref.command.insertLength (remainingBits limits.bits before atLiterals)
      (pref.literalState initial) atLiterals).mapError Error.literal
  let produced := initial.execution.output.size + literals.length
  if produced = block.endOutput then
    let output := initial.execution.output ++ literals.toArray
    return (⟨⟨⟨output, initial.execution.ring⟩, pref.command, none⟩, state.runs⟩, atDistance)
  else
    let (resolved, runs, after) ← Internal.resolve header pref.command ⟨block.windowBits, produced⟩
      initial.execution.ring (remainingBits limits.bits before atDistance) state.runs atDistance
    let executed ← (Execute.Internal.applyCopy block limits initial.execution pref.command literals resolved).mapError
      (Error.copy after.totalRead)
    return (⟨executed, runs⟩, after)

inductive SelectionWire (control : BlockTypes.Control) (command : Command.Value) (initial : BlockTypes.Switch.State) :
    List Bool → BlockTypes.Switch.State → Prop where
  | implicit : command.distance = .implicitZero → SelectionWire control command initial [] initial
  | explicit {bits : List Bool} {next : BlockTypes.Switch.State} :
      command.distance = .explicit →
      next.distance.Valid control →
      BlockTypes.Switch.Wire control initial.distance bits next.distance →
      next.literal = initial.literal → next.insertCopy = initial.insertCopy →
      SelectionWire control command initial bits next

inductive TailWire (header : CompressedHeader.Header) (block : Block) (command : Command.Value)
    (ring : Distance.Ring) (beforeCopy : List UInt8) (runs : BlockTypes.Switch.State) :
    List Bool → List UInt8 → Option Nat → Distance.Ring → BlockTypes.Switch.State → Prop where
  | terminal : beforeCopy.length = block.endOutput →
      TailWire header block command ring beforeCopy runs [] [] none ring runs
  | copy {switchBits distanceBits : List Bool} {matched : List UInt8} {distance : Nat}
      {resolved : Distance.Result} {next : BlockTypes.Switch.State} :
      beforeCopy.length < block.endOutput →
      SelectionWire header.initial.controls.distance command runs switchBits next →
      Distance.WireAt header command ⟨block.windowBits, beforeCopy.length⟩ ring
        next.distance.current distanceBits resolved →
      resolved.target = .backReference distance →
      HistoryCopy.Wire distance beforeCopy matched → matched.length = command.copyLength →
      TailWire header block command ring beforeCopy runs (switchBits ++ distanceBits) matched
        (some distance) resolved.ring next

structure Wire (header : CompressedHeader.Header) (block : Block) (initial : InsertCopy.State)
    (bits : List Bool) (result : InsertCopy.Result) : Prop where
  parts : ∃ prefixBits literalBits tailBits pref literalState literals matched,
    bits = (prefixBits ++ literalBits) ++ tailBits ∧
    LiteralSwitch.PrefixWire header initial prefixBits pref ∧
    Literal.Switch.Wire header (pref.literalState initial) literalBits literals literalState ∧
    literals.length = pref.command.insertLength ∧ result.execution.command = pref.command ∧
    TailWire header block pref.command initial.execution.ring (initial.execution.output.toList ++ literals)
      literalState.runs tailBits matched result.execution.distance result.execution.state.ring result.runs ∧
    result.execution.state.output.toList = initial.execution.output.toList ++ literals ++ matched

/-- A failing distance switch precedes the value reader. A failure in
    value resolution is anchored at the distance code after selection. -/
inductive ResolveFailure (header : CompressedHeader.Header) (command : Command.Value)
    (bounds : Distance.Bounds) (ring : Distance.Ring) (bitLimit : Nat) (runs : BlockTypes.Switch.State)
    (before : LSBReader) (input : List Bool) : Error → Prop where
  | switch {reason : BlockTypes.Switch.Error} :
      command.distance = .explicit →
      BlockTypes.Switch.Failure .distance header.initial.controls.distance bitLimit runs.distance before input reason →
      ResolveFailure header command bounds ring bitLimit runs before input (.distanceSwitch reason)
  | value {next : BlockTypes.Switch.State} {atCode : LSBReader} {used suffix : List Bool} {reason : Distance.Error} :
      Internal.select header command bitLimit runs before = .ok (next, atCode) →
      SelectionWire header.initial.controls.distance command runs used next →
      Source before atCode input used suffix →
      Distance.Internal.readAt header next.distance.current command bounds ring
        (remainingBits bitLimit before atCode) atCode = .error reason →
      ResolveFailure header command bounds ring bitLimit runs before input (.distance atCode.totalRead reason)

structure PrefixPath (header : CompressedHeader.Header) (block : Block) (limits : Limits)
    (initial : InsertCopy.State) (before atLiterals : LSBReader) (input suffix : List Bool)
    (pref : LiteralSwitch.Prefix) : Prop where
  parsed : LiteralSwitch.readPrefixCore header block limits initial before = .ok (pref, atLiterals)
  extent : ∃ used, LiteralSwitch.PrefixWire header initial used pref ∧ Source before atLiterals input used suffix

structure LiteralPath (header : CompressedHeader.Header) (block : Block) (limits : Limits)
    (initial : InsertCopy.State) (before atDistance : LSBReader) (input tail : List Bool)
    (pref : LiteralSwitch.Prefix) (literals : List UInt8) (state : Literal.Switch.State) : Prop where
  parts : ∃ atLiterals suffix used,
    PrefixPath header block limits initial before atLiterals input suffix pref ∧
    Literal.Switch.read header pref.command.insertLength (remainingBits limits.bits before atLiterals)
      (pref.literalState initial) atLiterals = .ok (literals, state, atDistance) ∧
    Source atLiterals atDistance suffix used tail ∧
    initial.execution.output.size + literals.length ≠ block.endOutput

/-- Ordered failure path. Successful prefixes justify the original
    cursor of the first failing operation. -/
inductive Failure (header : CompressedHeader.Header) (block : Block) (limits : Limits)
    (initial : InsertCopy.State) (before : LSBReader) (input : List Bool) : Error → Prop where
  | commandPrefix {reason : LiteralSwitch.Error} :
      LiteralSwitch.readPrefixCore header block limits initial before = .error reason →
      Failure header block limits initial before input (.commandPrefix reason)
  | literal {pref : LiteralSwitch.Prefix} {atLiterals : LSBReader} {suffix : List Bool}
      {reason : Literal.Switch.Error} :
      PrefixPath header block limits initial before atLiterals input suffix pref →
      Literal.Switch.Failure header pref.command.insertLength 0 (remainingBits limits.bits before atLiterals)
        (pref.literalState initial) atLiterals suffix reason →
      Failure header block limits initial before input (.literal reason)
  | resolve {pref : LiteralSwitch.Prefix} {literals : List UInt8} {state : Literal.Switch.State}
      {atDistance : LSBReader} {tail : List Bool} {reason : Error} :
      LiteralPath header block limits initial before atDistance input tail pref literals state →
      ResolveFailure header pref.command ⟨block.windowBits, initial.execution.output.size + literals.length⟩
        initial.execution.ring (remainingBits limits.bits before atDistance) state.runs atDistance tail reason →
      Failure header block limits initial before input reason
  | copy {pref : LiteralSwitch.Prefix} {literals : List UInt8} {state : Literal.Switch.State}
      {atDistance after : LSBReader} {used tail suffix : List Bool} {resolved : Distance.Result}
      {runs : BlockTypes.Switch.State} {reason : Execute.Error} :
      LiteralPath header block limits initial before atDistance input tail pref literals state →
      Internal.resolve header pref.command ⟨block.windowBits, initial.execution.output.size + literals.length⟩
        initial.execution.ring (remainingBits limits.bits before atDistance) state.runs atDistance =
          .ok (resolved, runs, after) →
      Source atDistance after tail used suffix →
      Execute.Internal.applyCopy block limits initial.execution pref.command literals resolved = .error reason →
      Failure header block limits initial before input (.copy after.totalRead reason)

end Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch
