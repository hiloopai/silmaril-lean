module

import Silmaril.Formats.Json.Fast.Parser.Defs
import Lean.Data.Json.Parser
meta import Silmaril.Formats.Json.Fast.Parser.Defs

open Silmaril.Formats

public def main (args : List String) : IO UInt32 := do
  let [mode, path] := args | throw (IO.userError "expected parser and fixture path")
  let bytes ← IO.FS.readBinFile path
  let start ← IO.monoNanosNow
  let accepted ← IO.mkRef <| match mode with
    | "wire" => (JsonWire.parse? ⟨bytes⟩).isSome
    | "fast" => (Json.Fast.parseBytes bytes).isOk
    | "lean" => ((String.fromUTF8? bytes).map fun text => (Lean.Json.parse text).isOk).getD false
    | _ => false
  let elapsed := (← IO.monoNanosNow) - start
  let accepted ← accepted.get
  IO.println s!"parse_ns={elapsed} accepted={accepted}"
  return if accepted then 0 else 1
