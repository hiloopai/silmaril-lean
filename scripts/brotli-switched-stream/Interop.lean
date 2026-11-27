module

import Lean
import Silmaril.Formats.Compression.Brotli.Stream.InsertCopy.Defs
meta import Silmaril.Formats.Compression.Brotli.Stream.InsertCopy.Defs

open Lean Silmaril.Formats.Compression.Brotli

private def stateJson (state : Execute.State) : Json :=
  Json.mkObj [("output", toJson (state.output.toList.map UInt8.toNat)),
    ("ring", toJson [state.ring.latest, state.ring.second, state.ring.third, state.ring.fourth])]

private def envelopeJson (error : Stream.Error) : Json :=
  Json.mkObj [("kind", toJson "envelope"), ("bit", toJson error.bit), ("block", toJson error.block),
    ("command", toJson error.command), ("cause", toJson (reprStr error.cause))]

private def commandJson (block command : Nat) (error : Execute.InsertCopy.Error) : Json :=
  let (kind, bit, cause) :=
    match error with
    | .literalBlockTypes bit => ("literalBlockTypes", bit, Json.null)
    | .distanceBlockTypes bit => ("distanceBlockTypes", bit, Json.null)
    | .commandTree bit ordinal => ("commandTree", bit, toJson ordinal)
    | .execute bit (.unsupportedDictionary distance size wordId) =>
      ("dictionary", bit, toJson [distance, size, wordId])
    | .execute bit reason => ("execute", bit, toJson (reprStr reason))
    | .switch error =>
      match error.cause with
      | .typeSymbol reason => ("type", error.bit, toJson (reprStr reason))
      | .length reason => ("length", error.bit, toJson (reprStr reason))
      | reason => ("switch", error.bit, toJson (reprStr reason))
  Json.mkObj [("kind", toJson kind), ("bit", toJson bit), ("block", toJson block),
    ("command", toJson command), ("cause", cause)]

public def main (args : List String) : IO UInt32 := do
  let [path, output, bits, blocks] := args | return 2
  let some output := output.toNat? | return 2
  let some bits := bits.toNat? | return 2
  let some blocks := blocks.toNat? | return 2
  let input ← IO.FS.readBinFile path
  let limits : Stream.Limits := ⟨input.size, output, windowSize 24, bits, blocks, 17408, 768⟩
  let legacy := match Stream.decode limits input.data.toList with
    | .ok state => stateJson state
    | .error error => envelopeJson error
  let switched := match Stream.InsertCopy.decode limits input.data.toList with
    | .ok state => stateJson state
    | .error (.envelope error) => envelopeJson error
    | .error (.command block command reason) => commandJson block command reason
  IO.println (Json.mkObj [("legacy", legacy), ("switched", switched)]).compress
  return 0
