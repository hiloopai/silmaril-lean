module

import Lean
import Silmaril.Formats.Compression.Brotli.Execute.LiteralSwitch.Defs
import Silmaril.Formats.Compression.Brotli.Stream.Defs
meta import Silmaril.Formats.Compression.Brotli.Execute.LiteralSwitch.Defs
meta import Silmaril.Formats.Compression.Brotli.Stream.Defs

open Lean Silmaril.Formats.Compression
open Silmaril.Formats.Compression.Brotli

private def requireIO {ε α : Type} [Repr ε] (result : Except ε α) : IO α :=
  match result with
  | .error error => throw (IO.userError (reprStr error))
  | .ok value => pure value

private def switchDetail (error : BlockTypes.Switch.Error) : String × Json :=
  match error.cause with
  | .typeSymbol reason => ("type", toJson (reprStr reason))
  | .length reason => ("length", toJson (reprStr reason))
  | reason => ("run", toJson (reprStr reason))

private def failureJSON (block : Nat) (error : Execute.LiteralSwitch.BlockError) : Json :=
  match error with
  | .command index reason =>
    let (kind, literal, cause) : String × Option Nat × Json :=
      match reason with
      | .distanceBlockTypes _ => ("distanceBlockTypes", none, .null)
      | .insertCopySwitch error =>
        let (stage, cause) := switchDetail error
        ("insertCopy-" ++ stage, none, cause)
      | .literal error =>
        match error.cause with
        | .switch reason =>
          let (stage, cause) := switchDetail reason
          ("literal-" ++ stage, some error.index, cause)
        | .literal _ reason => ("literal-code", some error.index, toJson (reprStr reason))
      | .bounds _ reason => ("bounds", none, toJson (reprStr reason))
      | .tail _ (.unsupportedDictionary distance size word) => ("dictionary", none, toJson [distance, size, word])
      | reason => ("command", none, toJson (reprStr reason))
    Json.mkObj [("block", toJson block), ("command", toJson index), ("literal", toJson literal),
      ("bit", toJson reason.bit), ("kind", toJson kind), ("cause", cause)]
  | reason => Json.mkObj [("block", toJson block), ("cause", toJson (reprStr reason))]

private def traceBlock (header : CompressedHeader.Header) (block : Execute.Block)
    (initial : Execute.State) (output bits index : Nat) (before : LSBReader) :
    IO (Array (List Nat) × Array (List Nat) × Execute.InsertCopy.State × LSBReader) := do
  let mut commands := #[]
  let mut literals := #[]
  let mut state := Execute.InsertCopy.State.start header initial
  let mut cursor := before
  for command in [:block.length] do
    if state.execution.output.size == block.endOutput then break
    let limits : Execute.Limits := ⟨output, bits - cursor.totalRead⟩
    let (pref, first) ← requireIO (Execute.LiteralSwitch.readPrefix header block limits state cursor)
    let run := pref.runs.insertCopy
    commands := commands.push [index, command, run.current, run.previous, run.remaining,
      pref.command.symbol.val, pref.command.insertLength, first.totalRead]
    let mut literalState := pref.literalState state
    let mut literalCursor := first
    for ordinal in [:pref.command.insertLength] do
      let remaining := bits - literalCursor.totalRead
      let (runs, atCode) ← requireIO
        (BlockTypes.Switch.select header.initial.controls .literal remaining literalState.runs literalCursor)
      let run := runs.literal
      let history := literalState.history
      let some mode := header.initial.fields.modes[run.current]? | throw (IO.userError "missing literal mode")
      let context := (Literal.contextId mode history).val
      let some tree := Literal.lookup header.literalMap (64 * run.current + context) |
        throw (IO.userError "missing literal context")
      let (byte, next, after) ← requireIO (Literal.Switch.readOne header remaining literalState literalCursor)
      literals := literals.push [index, command, ordinal, run.current, run.previous, run.remaining, mode.code,
        history.mostRecent.toNat, history.secondRecent.toNat, context, tree, byte.toNat, atCode.totalRead, after.totalRead]
      literalState := next
      literalCursor := after
    let (result, after) ← requireIO (Execute.LiteralSwitch.read header block limits state cursor)
    state := result.state
    cursor := after
  pure (commands, literals, state, cursor)

public def main (args : List String) : IO UInt32 := do
  let [path, output, bits] := args | return 2
  let some output := output.toNat? | return 2
  let some bits := bits.toNat? | return 2
  let wire ← IO.FS.readBinFile path
  let (window, afterWindow) ← requireIO (Brotli.Internal.readWindow (LSBReader.ofByteArray wire))
  let mut cursor := afterWindow
  let mut execution := Execute.State.start
  let mut commands : Array (List Nat) := #[]
  let mut literals : Array (List Nat) := #[]
  let mut ended := false
  for block in [:8] do
    let (metadata, body) ← requireIO (Stream.Internal.readHeader cursor)
    let .compressed last length := metadata | throw (IO.userError "fixture requires compressed meta-blocks")
    let (header, payload) ← requireIO (CompressedHeader.read ⟨17408, 768, bits - body.totalRead⟩ body)
    match Execute.LiteralSwitch.readBlock header window length.size ⟨output, bits - payload.totalRead⟩ execution payload with
    | .error reason =>
      IO.println (Json.mkObj [("failure", failureJSON block reason)]).compress
      return 0
    | .ok (final, after) =>
      let desc : Execute.Block := ⟨window, execution.output.size, length.size⟩
      let (observedCommands, observedLiterals, observedState, observedCursor) ←
        traceBlock header desc execution output bits block payload
      unless observedState = final ∧ observedCursor.totalRead = after.totalRead do
        throw (IO.userError "command trace and payload decoder differ")
      commands := commands ++ observedCommands
      literals := literals ++ observedLiterals
      execution := final.execution
      cursor := after
      if last then
        ended := true
        break
  unless ended do throw (IO.userError "missing fixture last flag")
  let _ ← requireIO (Stream.Internal.finish ⟨wire.size, output, windowSize 24, bits, 8, 17408, 768⟩ cursor)
  let ring := execution.ring
  IO.println (Json.mkObj [
    ("output", toJson (execution.output.toList.map UInt8.toNat)),
    ("ring", toJson [ring.latest, ring.second, ring.third, ring.fourth]),
    ("commands", toJson commands), ("literals", toJson literals), ("end", toJson cursor.totalRead)]).compress
  return 0
