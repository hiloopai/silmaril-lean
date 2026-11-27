module

import Lean
import Silmaril.Formats.Compression.Brotli.Stream.Defs
meta import Silmaril.Formats.Compression.Brotli.Stream.Defs

open Lean Silmaril.Formats.Compression.Brotli

private def showCause : Stream.Cause → Json
  | .command (.unsupportedDictionary distance length wordId) =>
    Json.mkObj [("dictionary", toJson [distance, length, wordId])]
  | .command .blockTypes => toJson "unsupported block switching"
  | cause => toJson (reprStr cause)

public def main (args : List String) : IO UInt32 := do
  let [path, output, bits, blocks] := args | return 2
  let some output := output.toNat? | return 2
  let some bits := bits.toNat? | return 2
  let some blocks := blocks.toNat? | return 2
  let input ← IO.FS.readBinFile path
  let limits : Stream.Limits := ⟨input.size, output, windowSize 24, bits, blocks, 17408, 768⟩
  let message :=
    match Stream.decode limits input.data.toList with
    | .ok state => Json.mkObj [
      ("output", toJson (state.output.toList.map UInt8.toNat)),
      ("ring", toJson [state.ring.latest, state.ring.second, state.ring.third, state.ring.fourth])]
    | .error failure => Json.mkObj [
      ("bit", toJson failure.bit), ("block", toJson failure.block), ("command", toJson failure.command),
      ("cause", showCause failure.cause)]
  IO.println message.compress
  return 0
