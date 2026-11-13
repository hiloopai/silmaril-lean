import Silmaril.Project.WasmComponents.Wac.Defs

/-!
The recipe of `examples/wasm-components/lean/provider.wasm`: the component
`Silmaril.Project.WasmComponents.Wac.provider`, encoded by `Silmaril.Wasm.Component.Binary.encode`.

Run from the repository root:

    lake env lean examples/wasm-components/wac/Gen.lean

`Silmaril.Project.WasmComponents.Wac.Thms` proves that the committed file is this encoding.
-/

open Silmaril.Wasm.Component.Binary

#eval show IO Unit from do
  match encode Silmaril.Project.WasmComponents.Wac.provider with
  | some b => IO.FS.writeBinFile "examples/wasm-components/lean/provider.wasm" b
  | none => throw (IO.userError "provider.wasm: the encoder failed")
