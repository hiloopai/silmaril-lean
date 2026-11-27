module

import Lean
import Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Defs
import Silmaril.Formats.Compression.Brotli.Stream.LiteralSwitch.Defs
import Silmaril.Formats.Compression.Brotli.Stream.InsertCopy.Defs
meta import Silmaril.Formats.Compression.Brotli.Execute.DistanceSwitch.Defs
meta import Silmaril.Formats.Compression.Brotli.Stream.LiteralSwitch.Defs
meta import Silmaril.Formats.Compression.Brotli.Stream.InsertCopy.Defs

open Lean Silmaril.Formats.Compression Silmaril.Formats.Compression.Brotli
open Silmaril.Formats.Compression.Brotli.Execute.LiteralSwitch (remainingBits)

private def requireIO {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .error error => throw (IO.userError (reprStr error))
  | .ok value => pure value

private def ringJson (ring : Distance.Ring) : Json :=
  toJson [ring.latest, ring.second, ring.third, ring.fourth]

private def errorJson (index : Nat) (error : Execute.DistanceSwitch.Error) : Json :=
  let (stage, cause) := match error with
    | .distanceSwitch error => match error.cause with
      | .typeSymbol reason => ("switch-type", toJson (reprStr reason))
      | .length reason => ("switch-length", toJson (reprStr reason))
      | reason => ("switch", toJson (reprStr reason))
    | .distance _ reason => ("distance", toJson (reprStr reason))
    | .copy _ (.unsupportedDictionary distance length word) => ("dictionary", toJson [distance, length, word])
    | .copy _ reason => ("copy", toJson (reprStr reason))
    | .literal reason => ("literal", toJson (reprStr reason.cause))
    | .commandPrefix reason => ("prefix", toJson (reprStr reason))
  Json.mkObj [("stage", toJson stage), ("bit", toJson error.bit), ("command", toJson index), ("cause", cause)]

private def trace (header : CompressedHeader.Header) (block : Execute.Block)
    (limits : Execute.Limits) (before after : LSBReader) (state : Execute.InsertCopy.State)
    (result : Execute.InsertCopy.Result) : IO Json := do
  let (pref, atLiterals) ← requireIO (Execute.LiteralSwitch.readPrefixCore header block limits state before)
  let (literals, literalState, atDistance) ← requireIO
    (Literal.Switch.read header pref.command.insertLength (remainingBits limits.bits before atLiterals)
      (pref.literalState state) atLiterals)
  let mut codeStart := atDistance.totalRead
  let mut selection : Option (List Nat) := none
  let mut code : Option (List Nat) := none
  if result.execution.distance.isSome then
    let budget := remainingBits limits.bits before atDistance
    let (runs, atCode) ← requireIO
      (Execute.DistanceSwitch.Internal.select header pref.command budget literalState.runs atDistance)
    let (resolved, endRead) ← requireIO (Distance.Internal.readAt header runs.distance.current pref.command
      ⟨block.windowBits, state.execution.output.size + literals.length⟩ state.execution.ring
      (remainingBits budget atDistance atCode) atCode)
    unless endRead.totalRead = after.totalRead ∧ runs = result.runs ∧
        resolved.ring = result.execution.state.ring ∧ result.execution.distance = some resolved.target.distance do
      throw (IO.userError "distance trace differs from executed result")
    codeStart := atCode.totalRead
    if pref.command.distance == .explicit then
      let some tree := Distance.treeIndexAt? header.distanceMap runs.distance.current pref.command.copyLength
        | throw (IO.userError "missing selected context entry")
      selection := some [Distance.contextId pref.command.copyLength, tree]
      code := some [resolved.code, resolved.extra]
  let run := result.runs.distance
  return Json.mkObj [("symbol", toJson pref.command.symbol.val), ("before", toJson before.totalRead),
    ("atLiterals", toJson atLiterals.totalRead), ("atDistance", toJson atDistance.totalRead),
    ("atCode", toJson codeStart), ("end", toJson after.totalRead), ("selection", toJson selection),
    ("code", toJson code), ("run", toJson [run.current, run.previous, run.remaining]),
    ("distance", toJson result.execution.distance), ("outputLength", toJson result.execution.state.output.size),
    ("ring", ringJson result.execution.state.ring)]

public def main (args : List String) : IO UInt32 := do
  let [path, output, bits] := args | return 2
  let some output := output.toNat? | return 2
  let some bits := bits.toNat? | return 2
  let wire ← IO.FS.readBinFile path
  let extent := 8 * wire.size
  let (window, afterWindow) ← requireIO (Brotli.Internal.readWindow (Brotli.Internal.start wire.data.toList))
  let (framing, tables) ← requireIO (Stream.Internal.readHeader afterWindow)
  let .compressed true length := framing | throw (IO.userError "fixture needs one last compressed block")
  let (header, payload) ← requireIO (CompressedHeader.read ⟨17408, 768, extent - tables.totalRead⟩ tables)
  let block : Execute.Block := ⟨window, 0, length.size⟩
  let mut state := Execute.InsertCopy.State.start header Execute.State.start
  let mut cursor := payload
  let mut commands := #[]
  for index in [:length.size] do
    if state.execution.output.size == length.size then break
    let caps : Execute.Limits := ⟨output, bits - cursor.totalRead⟩
    match Execute.DistanceSwitch.read header block caps state cursor with
    | .error reason =>
      IO.println (Json.mkObj [("failure", errorJson index reason)]).compress
      return 0
    | .ok (result, after) =>
      commands := commands.push (← trace header block caps cursor after state result)
      state := result.state
      cursor := after
  unless state.execution.output.size = length.size do throw (IO.userError "wrong meta-block extent")
  let limits : Stream.Limits := ⟨wire.size, output, windowSize 24, bits, 1, 17408, 768⟩
  let _ ← requireIO (Stream.Internal.finish limits cursor)
  let previous := (Stream.LiteralSwitch.decode limits wire.data.toList,
    Stream.InsertCopy.decode limits wire.data.toList, Stream.decode limits wire.data.toList)
  let refused := match previous with
    | (.error (.block 0 (.command 0 (.distanceBlockTypes bit))),
        .error (.command 0 0 (.distanceBlockTypes oldBit)),
        .error ⟨_, some 0, none, .command .blockTypes⟩) => bit = payload.totalRead && oldBit = payload.totalRead
    | _ => false
  IO.println (Json.mkObj [("output", toJson (state.execution.output.toList.map UInt8.toNat)),
    ("ring", ringJson state.execution.ring), ("commands", toJson commands), ("previousRefusals", toJson refused)]).compress
  return 0
