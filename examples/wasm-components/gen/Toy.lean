import Silmaril.Project.WasmComponents.Toy.Defs
import Silmaril.Wasm.Component.Binary.Encode.Defs

/-!
The recipe of `examples/wasm-components/lean/toy.wasm` and `toy-split.wasm`: the resource
provider toy (`Silmaril.Wasm.Resource.CompToy`) as the binary components
`Silmaril.Project.WasmComponents.Toy.toyAst` (one section per run of items of one kind) and
`toySplitAst` (one item per section), encoded by `Silmaril.Wasm.Component.Binary.encode`.

Run from the repository root:

    lake env lean examples/wasm-components/gen/Toy.lean

`Silmaril.Project.WasmComponents.Toy.Thms` proves that the committed files are these encodings
(`gen.toy.is`, `gen.toy_split.is`, kernel evaluation).
-/

open Silmaril.Wasm.Component.Binary Silmaril.Project.WasmComponents.Toy

def out (f : String) : System.FilePath := "examples/wasm-components/lean" / f

#eval show IO Unit from do
  for (f, c) in [("toy.wasm", toyAst), ("toy-split.wasm", toySplitAst)] do
    match encode c with
    | some b => IO.FS.writeBinFile (out f) b
    | none => throw (IO.userError s!"{f}: the encoder failed")
