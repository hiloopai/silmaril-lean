module

import Lean
import Silmaril.Formats.Compression.Brotli.Stream.LiteralSwitch.Defs
import Silmaril.Formats.Compression.Brotli.Stream.InsertCopy.Defs
meta import Silmaril.Formats.Compression.Brotli.Stream.LiteralSwitch.Defs
meta import Silmaril.Formats.Compression.Brotli.Stream.InsertCopy.Defs

open Lean Silmaril.Formats.Compression.Brotli

private def stateJson (state : Execute.State) : Json :=
  Json.mkObj [("output", toJson (state.output.toList.map UInt8.toNat)),
    ("ring", toJson [state.ring.latest, state.ring.second, state.ring.third, state.ring.fourth])]

private def switchDetail (error : BlockTypes.Switch.Error) : String × Json :=
  match error.cause with
  | .typeSymbol reason => ("type", toJson (reprStr reason))
  | .length reason => ("length", toJson (reprStr reason))
  | reason => ("run", toJson (reprStr reason))

private def commandJson (block command : Nat) (reason : Execute.LiteralSwitch.Error) : Json :=
  let (kind, literal, cause) : String × Option Nat × Json := match reason with
    | .distanceBlockTypes _ => ("distanceBlockTypes", none, .null)
    | .insertCopySwitch error =>
      let (stage, cause) := switchDetail error
      ("insertCopy-" ++ stage, none, cause)
    | .literal error => match error.cause with
      | .switch reason =>
        let (stage, cause) := switchDetail reason
        ("literal-" ++ stage, some error.index, cause)
      | .literal _ reason => ("literal-code", some error.index, toJson (reprStr reason))
    | .tail _ (.unsupportedDictionary distance size word) => ("dictionary", none, toJson [distance, size, word])
    | reason => ("command", none, toJson (reprStr reason))
  Json.mkObj [("kind", toJson kind), ("bit", toJson reason.bit), ("block", toJson block),
    ("command", toJson command), ("literal", toJson literal), ("cause", cause)]

private def failureJson (error : Stream.LiteralSwitch.Error) : Json :=
  match error with
  | .envelope reason =>
    Json.mkObj [("kind", toJson "envelope"), ("bit", toJson reason.bit), ("block", toJson reason.block),
      ("command", toJson reason.command), ("literal", .null), ("cause", toJson (reprStr reason.cause))]
  | .block block (.command command reason) => commandJson block command reason
  | .block block reason =>
    Json.mkObj [("kind", toJson "block"), ("bit", toJson error.bit),
      ("block", toJson block), ("cause", toJson (reprStr reason))]

public def main (args : List String) : IO UInt32 := do
  let [path, input, output, bits, blocks] := args | return 2
  let some input := input.toNat? | return 2
  let some output := output.toNat? | return 2
  let some bits := bits.toNat? | return 2
  let some blocks := blocks.toNat? | return 2
  let bytes ← IO.FS.readBinFile path
  let limits : Stream.Limits := ⟨input, output, windowSize 24, bits, blocks, 17408, 768⟩
  let previous := match Stream.InsertCopy.decode limits bytes.data.toList with
    | .ok state => stateJson state
    | .error error => toJson (reprStr error)
  let current := match Stream.LiteralSwitch.decode limits bytes.data.toList with
    | .ok state => stateJson state
    | .error error => failureJson error
  IO.println (Json.mkObj [("previous", previous), ("current", current)]).compress
  return 0
