module
public import Silmaril.Project.Defs
public import Silmaril.Wasm.Binary.Core.Decode
public import Silmaril.Wasm.Binaryen.Exe.Encode

/-!
# Format `wasm.binary.core`

The WebAssembly binary format to the Core 3.0 module AST `Silmaril.Wasm.Module`.

* Parser: silmaril-lean's executable decoder `Binary.Core.decode?`
  (`Silmaril/Wasm/Binary/Core/Decode.lean`). It covers the Binaryen profile of the binary
  format; the extension decoders (shared memory, atomics, …) are separate and not registered.
* Printer: the Binaryen encoder `Binaryen.Exe.encodeModule?`.

Laws (`Silmaril.Project.Formats.Wasm.Thms`): `sound` for the specification grammar
`Binary.Core.Encodes`, from `decode?_sound`. There is no `roundtrip` law: no theorem says
that `decode?` accepts every output of `encodeModule?`. What is proved is that the printer
is sound and that printing then parsing can only return the printed module.
-/

@[expose] public section
namespace Silmaril.Project.Formats

/-- WebAssembly binary to the Core module AST. -/
def wasm : Format blob Silmaril.Wasm.Module where
  parse b := Silmaril.Wasm.Binary.Core.decode? b.data
  print := some fun m =>
    match Silmaril.Wasm.Binaryen.Exe.encodeModule? m with
    | .ok bs => some ⟨⟨bs.toArray⟩⟩
    | .error _ => none

/-- The specification relation of `wasm.binary.core`: the binary grammar of the Core specification. -/
def WasmRel (b : Silmaril.Formats.Bytes) (m : Silmaril.Wasm.Module) : Prop :=
  Silmaril.Wasm.Binary.Core.Encodes b.toList m

end Silmaril.Project.Formats

silmaril format wasm.binary.core := Silmaril.Project.Formats.wasm
  (doc := "WebAssembly binary to the Core module AST (Binary.Core.decode?); printer Binaryen.Exe.encodeModule?")
silmaril format_default wasm := wasm.binary.core
