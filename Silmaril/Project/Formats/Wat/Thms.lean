module
public import Silmaril.Project.Formats.Wat.Defs
public import Silmaril.Project.Formats.Wasm.Thms
public import Silmaril.Wasm.Binaryen.Toolkit.WatSyntaxSound
public import Silmaril.Data.IncludeBytes
meta import Silmaril.Project.Formats.Wat.Defs
import Silmaril.Proofs.Project.Formats.Wat
meta import Silmaril.Wasm.Binaryen.Exe.Encode

/-!
# Format `wat.sexp`: laws and examples

* `wat_sound` (registered law `sound`): the parser is sound for `WatRel`.
* `wat_print_sound`: the printer emits the UTF-8 of a text that the grammar relates to the
  module (from `moduleSyntax?_sound` and `renderWatDocument?_sound`).
* An example on `examples/project-formats/example.wat`, and the cross-format equivalence of
  `example.wat` and `example.wasm` under `wat.sexp` and `wasm.binary.core`, conditional on a re-encoding
  fact that is checked by evaluation (`ExampleWatEncodes`).
-/

@[expose] public section
namespace Silmaril.Project.Formats

open Silmaril.Wasm Silmaril.Wasm.Binaryen.Toolkit

theorem wat_sound : wat.SoundFor WatRel := Silmaril.Proofs.Project.Formats.wat_sound

theorem wat_print_sound {p} (hp : wat.print = some p) {m : Silmaril.Wasm.Module}
    {b : Silmaril.Formats.Bytes} (h : p m = some b) :
    ∃ s, b = ⟨s.toUTF8⟩ ∧ Text.Core.Encodes s m :=
  Silmaril.Proofs.Project.Formats.wat_print_sound hp h

/-- A WAT and a WASM artifact are one module when the WASM bytes are the re-encoding of the
parsed WAT (the binary grammar is functional). -/
theorem wat_wasm_equivalent_of_encodes {a b : Silmaril.Formats.Bytes}
    (hb : (wasm.parse b).isSome = true)
    (he : ((wat.parse a).bind fun m => (Binaryen.Exe.encodeModule? m).toOption) =
      some b.toList) :
    Equivalent wat wasm a b :=
  Silmaril.Proofs.Project.Formats.wat_wasm_equivalent_of_encodes hb he

/-- `examples/project-formats/example.wat`. -/
def exampleWat : Silmaril.Formats.Bytes :=
  ⟨include_bytes "../../../../examples/project-formats/example.wat"⟩

theorem exampleWat_parses : (wat.parse exampleWat).isSome = true := by decide +kernel

/-- Re-encoding the module of `example.wat` with the Binaryen encoder (the `wasm.binary.core` printer)
gives the bytes of `example.wasm`. `Silmaril.Wasm.Module` has no decidable equality, so the
statement compares bytes. The kernel does not reduce the encoder (its LEB128 helpers use
well-founded recursion), so this is checked by evaluation below, not proved. -/
def ExampleWatEncodes : Prop :=
  ((wat.parse exampleWat).bind fun m => (Binaryen.Exe.encodeModule? m).toOption) =
    some exampleWasm.toList

/-- **Cross-format equivalence**, conditional on `ExampleWatEncodes`: `example.wat` and
`example.wasm` denote the same module (the binary grammar is functional). -/
theorem example_wat_wasm_equivalent (he : ExampleWatEncodes) :
    Equivalent wat wasm exampleWat exampleWasm :=
  wat_wasm_equivalent_of_encodes exampleWasm_parses he

end Silmaril.Project.Formats

-- The evaluation check of `ExampleWatEncodes` (compiled code, not a kernel fact). The
-- interpreter cannot run `include_bytes`, so both files are read directly (Lake elaborates
-- with the package root as working directory).
#eval show IO Unit from do
  let watBytes ← IO.FS.readBinFile "examples/project-formats/example.wat"
  let wasmBytes ← IO.FS.readBinFile "examples/project-formats/example.wasm"
  let encoded := (Silmaril.Project.Formats.wat.parse ⟨watBytes⟩).bind
    fun m => (Silmaril.Wasm.Binaryen.Exe.encodeModule? m).toOption
  unless encoded == some wasmBytes.toList do
    throw <| IO.userError "example.wat does not encode to example.wasm"

silmaril format_law wat.sexp sound := Silmaril.Project.Formats.wat_sound
  (rel := Silmaril.Project.Formats.WatRel)
