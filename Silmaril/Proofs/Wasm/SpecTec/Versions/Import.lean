module

public import Silmaril.Raw.Wasm.SpecTec.Scripts
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Import

/-!
# The `WebAssembly/spec` main streams, imported a second way

`specs/spectec/e7a9df7c/` holds the three `--ast` streams of `WebAssembly/spec@e7a9df7c`
(`specs/spectec/e7a9df7c/manifest.json`).  `tools/spectec-gen` writes them as explicit Lean source
(`Silmaril.Raw.Wasm.SpecTec.Scripts.Main.WasmNN.Original`); here `spectec_import` reads the same files
at elaboration time, with the Lean reader and the decoder whose round trip is proved
(`IL.decodeScript?_scriptS`), and the kernel checks the two readings are the same term.

This is the same check `Silmaril.Proofs.Wasm.SpecTec.Scripts.Original` makes for the pinned streams;
nothing in the import machinery was changed to read the later revision.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Versions.Specs

set_option maxRecDepth 100000

spectec_import mainWasm10 from "specs/spectec/e7a9df7c/wasm-1.0.ast"
spectec_import mainWasm20 from "specs/spectec/e7a9df7c/wasm-2.0.ast"
spectec_import mainWasm30 from "specs/spectec/e7a9df7c/wasm-3.0.ast"

/-- The definition counts recorded in `specs/spectec/e7a9df7c/manifest.json`. -/
example : mainWasm10.length = 318 := by rfl
example : mainWasm20.length = 470 := by rfl
example : mainWasm30.length = 974 := by rfl

end Silmaril.Wasm.SpecTec.Versions.Specs

namespace Silmaril.Wasm.SpecTec.Versions

set_option maxRecDepth 100000

theorem generated_main_wasm10_eq :
    Silmaril.Wasm.SpecTec.Scripts.Main.Wasm10.Original.script = Specs.mainWasm10 := by rfl

theorem generated_main_wasm20_eq :
    Silmaril.Wasm.SpecTec.Scripts.Main.Wasm20.Original.script = Specs.mainWasm20 := by rfl

theorem generated_main_wasm30_eq :
    Silmaril.Wasm.SpecTec.Scripts.Main.Wasm30.Original.script = Specs.mainWasm30 := by rfl

end Silmaril.Wasm.SpecTec.Versions
