module

import Silmaril.Wasm.Binary.Core.Decode
import Silmaril.Wasm.Binaryen.Continuation.Examples
import Silmaril.Wasm.Binaryen.Exe.Encode
import Silmaril.Wasm.Validation.Check.Validate
meta import Silmaril.Wasm.Binary.Core.Decode
meta import Silmaril.Wasm.Binaryen.Continuation.Examples
meta import Silmaril.Wasm.Binaryen.Exe.Encode
meta import Silmaril.Wasm.Validation.Check.Validate

open Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Binaryen.Continuation
open Validation

#print axioms Raw.coreEquiv
#print axioms Raw.ofBinaryen_eq_some_iff
#print axioms Code.binaryen_square
#print axioms Code.sound
#print axioms Code.same_erasure_iff
#print axioms Code.core_image_iff
#print axioms Code.lift_core
#print axioms Examples.folded_core

private def readModule (path : System.FilePath) : IO Module := do
  let .ok mod := Binary.Core.Decode.decodeModule (← IO.FS.readBinFile path)
    | throw (IO.userError s!"Core decoding failed: {path}")
  unless (validate? mod).isSome do throw (IO.userError s!"Core validation failed: {path}")
  pure mod

public def main (args : List String) : IO Unit := do
  match args with
  | ["emit", path] =>
      let .ok bytes := Exe.encodeModule? Examples.fixture
        | throw (IO.userError "Core encoding failed")
      IO.FS.writeBinFile path ⟨bytes.toArray⟩
      let mod ← readModule path
      unless reprStr mod.funcs == reprStr Examples.fixture.funcs do
        throw (IO.userError "Core binary changed the exact continuation fixture")
      IO.println "Exact Core fixture encoded, decoded and validated"
  | ["normalized", path] =>
      let mod ← readModule path
      let some body := mod.funcs[1]? | throw (IO.userError "Missing choose function")
      unless !body.locals.isEmpty && (Raw.read body.body).isNone do
        throw (IO.userError "Expected Binaryen to materialize the block parameter in locals")
      unless Examples.observe mod 0 == some (99, 4, 7, 0) &&
          Examples.observe mod 1 == some (99, 4, 5, 45) do
        throw (IO.userError "The checked Binaryen rewrite changed the fixture observations")
      IO.println "Binaryen binary validates and leaves the fragment; returns and writes agree on the fixture"
  | _ => throw (IO.userError "expected emit|normalized PATH")
