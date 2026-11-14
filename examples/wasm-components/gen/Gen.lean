import Silmaril.Wasm.Component.Binary.Example.Defs

/-!
The recipe of the Silmaril-generated binaries of the Wasm components pilot: the hand-built core
module `producer` and the components `compB` and `linked` of
`Silmaril.Wasm.Component.Binary.Example`, encoded by `Silmaril.Wasm.Component.Binary.encode`.

Run from the repository root:

    lake env lean examples/wasm-components/gen/Gen.lean

`Silmaril.Project.WasmComponents.Thms` proves that the committed files are these encodings
(`…​.is`, kernel evaluation).
-/

open Silmaril.Wasm.Component.Binary Silmaril.Wasm.Component.Binary.Example

def out (f : String) : System.FilePath := "examples/wasm-components/lean" / f

#eval show IO Unit from do
  IO.FS.writeBinFile (out "producer.wasm") producer
  for (f, c) in [("comp-b.wasm", compB), ("linked.wasm", linked)] do
    match encode c with
    | some b => IO.FS.writeBinFile (out f) b
    | none => throw (IO.userError s!"{f}: the encoder failed")
