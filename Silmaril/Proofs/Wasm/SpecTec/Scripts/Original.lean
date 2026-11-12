module

public import Silmaril.Raw.Wasm.SpecTec.Scripts
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# The generated original scripts are the imported ones

`tools/spectec-gen` writes each pinned `--ast` stream as explicit Lean source
(`Silmaril.Raw.Wasm.SpecTec.Scripts.WasmNN.Original`); `spectec_import` reads the same file at
elaboration time (`Silmaril.SpecTec.Specs.wasmNN`).  The two are produced independently — a
Rust reader and emitter against a Lean reader, decoder and reflection — and the kernel checks
they are the same term.  The emitted definitions are syntactically equal to the imported ones,
so each check is a linear traversal.
-/

public section

namespace Silmaril.Wasm.SpecTec.Scripts

open Silmaril.SpecTec

set_option maxRecDepth 100000

theorem generated_wasm10_eq : Wasm10.Original.script = Specs.wasm10 := by rfl

theorem generated_wasm20_eq : Wasm20.Original.script = Specs.wasm20 := by rfl

theorem generated_wasm30_eq : Wasm30.Original.script = Specs.wasm30 := by rfl

end Silmaril.Wasm.SpecTec.Scripts
