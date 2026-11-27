module

import Lean
import Silmaril.Formats.Compression.Brotli.Stream.DistanceSwitch.Defs
import Silmaril.Formats.Compression.Brotli.Stream.LiteralSwitch.Defs
meta import Silmaril.Formats.Compression.Brotli.Stream.DistanceSwitch.Defs
meta import Silmaril.Formats.Compression.Brotli.Stream.LiteralSwitch.Defs

open Lean Silmaril.Formats.Compression.Brotli

private def failureJson (failure : Stream.DistanceSwitch.Error) : Json :=
  let (block, command, stage, cause) : Option Nat × Option Nat × String × Json :=
    match failure with
    | .envelope error => (error.block, error.command, "envelope", toJson (reprStr error.cause))
    | .block block reason =>
      match reason with
      | .initialOutput _ => (some block, none, "initialOutput", .null)
      | .fuel index _ => (some block, some index, "fuel", .null)
      | .command index reason =>
        let (stage, cause) := match reason with
          | .distanceSwitch error => match error.cause with
            | .typeSymbol reason => ("switch-type", toJson (reprStr reason))
            | .length reason => ("switch-length", toJson (reprStr reason))
            | reason => ("switch", toJson (reprStr reason))
          | .distance _ reason => ("distance", toJson (reprStr reason))
          | .copy _ (.unsupportedDictionary distance length word) => ("dictionary", toJson [distance, length, word])
          | .copy _ reason => ("copy", toJson (reprStr reason))
          | .literal reason => ("literal", toJson (reprStr reason.cause))
          | .commandPrefix reason => ("prefix", toJson (reprStr reason))
        (some block, some index, stage, cause)
  Json.mkObj [("block", toJson block), ("command", toJson command), ("stage", toJson stage),
    ("bit", toJson failure.bit), ("cause", cause)]

public def main (args : List String) : IO UInt32 := do
  let [path, inputCap, outputCap, windowCap, bitCap, blockCap] := args | return 2
  let some inputCap := inputCap.toNat? | return 2
  let some outputCap := outputCap.toNat? | return 2
  let some windowCap := windowCap.toNat? | return 2
  let some bitCap := bitCap.toNat? | return 2
  let some blockCap := blockCap.toNat? | return 2
  let wire ← IO.FS.readBinFile path
  let bytes := wire.data.toList
  let limits : Stream.Limits := ⟨inputCap, outputCap, windowCap, bitCap, blockCap, 17408, 768⟩
  let result := match Stream.DistanceSwitch.decode limits bytes with
    | .error error => Json.mkObj [("failure", failureJson error)]
    | .ok state =>
      let literalRefuses := match Stream.LiteralSwitch.decode limits bytes with
        | .error (.block _ (.command _ (.distanceBlockTypes _))) => true
        | _ => false
      let defaultRefuses := match Stream.decode limits bytes with
        | .error ⟨_, _, _, .command .blockTypes⟩ => true
        | _ => false
      let ring := state.ring
      Json.mkObj [("output", toJson (state.output.toList.map UInt8.toNat)),
        ("ring", toJson [ring.latest, ring.second, ring.third, ring.fourth]),
        ("literalRefuses", toJson literalRefuses), ("defaultRefuses", toJson defaultRefuses)]
  IO.println result.compress
  return 0
