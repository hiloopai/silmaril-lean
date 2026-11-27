module

import Lean
import Silmaril.Formats.Compression.Brotli.Stream.Dictionary.Defs
meta import Silmaril.Formats.Compression.Brotli.Stream.Dictionary.Defs

open Lean Silmaril.Formats.Compression.Brotli

private def failure (error : Stream.DistanceSwitch.Error) : Json :=
  let (block, command, stage, cause) := match error with
    | .envelope env =>
      let cause := match env.cause with
        | .framing reason => reprStr reason
        | .bitLimit => "bitLimit"
        | reason => reprStr reason
      (env.block, env.command, "envelope", cause)
    | .block index reason =>
      match reason with
      | .initialOutput _ => (some index, none, "initialOutput", "")
      | .fuel slot _ => (some index, some slot, "fuel", "")
      | .command slot reason =>
        let (stage, cause) := match reason with
          | .distance _ reason => ("distance", reprStr reason)
          | .copy _ reason => ("copy", reprStr reason)
          | reason => ("command", reprStr reason)
        (some index, some slot, stage, cause)
  Json.mkObj [("block", toJson block), ("command", toJson command), ("stage", toJson stage),
    ("cause", toJson cause), ("bit", toJson error.bit)]

public def main (args : List String) : IO UInt32 := do
  let [path, inputArg, outputArg, windowArg, bitsArg, blocksArg, commandsArg] := args | return 2
  let (some maxInput, some maxOutput, some maxWindow, some maxBits, some maxBlocks, some maxCommands) :=
    (inputArg.toNat?, outputArg.toNat?, windowArg.toNat?, bitsArg.toNat?, blocksArg.toNat?, commandsArg.toNat?) | return 2
  let wire := (← IO.FS.readBinFile path).data.toList
  let framing : Stream.Limits := ⟨maxInput, maxOutput, maxWindow, maxBits, maxBlocks, 17408, 768⟩
  match Stream.Dictionary.decode ⟨framing, maxCommands⟩ wire with
  | .error error => IO.println (Json.mkObj [("failure", failure error)]).compress
  | .ok result =>
    let ring := result.execution.ring
    let refused := match Stream.DistanceSwitch.decode framing wire with
      | .error (.block _ (.command _ (.copy _ (.unsupportedDictionary ..)))) => true
      | _ => false
    IO.println (Json.mkObj [("output", toJson (result.execution.output.toList.map UInt8.toNat)),
      ("ring", toJson [ring.latest, ring.second, ring.third, ring.fourth]),
      ("remainingCommands", toJson result.remainingCommands), ("strictRefused", toJson refused)]).compress
  return 0
