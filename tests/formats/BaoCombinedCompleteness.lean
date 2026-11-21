module

import Silmaril.Formats.Blake3Cas.RangeFacts.Combined.Thms
meta import Silmaril.Formats.Blake3Cas.RangeFacts.Combined.Defs
meta import Silmaril.Formats.Blake3Cas.RangeFacts.Thms
meta import Silmaril.Formats.Iroh.Vectors

open Silmaril.Crypto.Blake3
open Silmaril.Formats
open Silmaril.Formats.Blake3Cas.RangeFacts

private def require (label : String) (condition : Bool) : IO Unit :=
  unless condition do throw (IO.userError label)

set_option maxRecDepth 8192

#eval do
  let (digest, combined, _, _, _) := Iroh.Vectors.baoFixtures
  let original : Bytes := List.replicate 2049 0
  require "combined encoder reproduces the Bao fixture" (Combined.encode? original == some combined)
  require "false longer extent cannot finish a combined frame"
    (decodeCombined? 2050 digest (.toEnd 0) (Bao.putLE64 2050 ++ combined.drop 8)).isNone
  for size in [0, 1024, 1025, 2048, 2049, 3073] do
    let bytes := (List.range size).map (fun index => UInt8.ofNat (index % 251))
    let some root := hash? (some ∘ compress32) bytes | throw (IO.userError "combined fixture hash")
    let some wire := Combined.encode? bytes | throw (IO.userError "combined encode")
    let some response := decodeCombined? size root (.toEnd 0) wire | throw (IO.userError "combined decode")
    let some whole := response.suffix? | throw (IO.userError "combined EOF")
    require "combined response promotes to the exact whole payload"
      (response.claim == size && whole.stop == size && whole.bytes == bytes)
    if size > 0 then
      require "combined frame exceeds the verifier cap" (decodeCombined? (size - 1) root (.toEnd 0) wire).isNone

#print axioms Combined.fullPlan_geometry
#print axioms Combined.complete
