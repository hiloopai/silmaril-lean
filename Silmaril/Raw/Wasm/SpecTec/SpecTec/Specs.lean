module

public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Import
public import Silmaril.Raw.Wasm.SpecTec.SpecTec.Crosscheck

/-!
# The pinned specifications, as Lean values

The three elaborated WebAssembly specifications, imported from the `--ast`
streams in `specs/spectec/` (`specs/spectec/README.md` records how they were
produced and `sil spectec-asts --check` re-checks their SHA-256s).

Each import adds `wasmNN.defs.i` for every top-level definition, the script
`wasmNN`, its printed form `wasmNN.sexps`, and
`wasmNN.decodes : IL.decodeScript? wasmNN.sexps = some wasmNN` — an instance
of a theorem that holds for every script, so it certifies nothing on its own.
`Silmaril/SpecTec/Import.lean` sets out precisely what the import does
establish about these files, which part of it the kernel sees, and what stays
trusted.

`spectec_crosscheck` additionally re-derives the instruction constructor
shapes from `wasm-3.0.ast` and compares them with
`Silmaril/Wasm/SpecTec/Generated.lean`, which `sil spectec` produced from the
same bytes using the third-party Rust `spectec_ast` decoder.  Two independent
decoders agreeing on all 116 constructors is the cross-check that phase 1 of
`docs/projects/spectec/README.md` asks for.
-/

@[expose] public section

namespace Silmaril.SpecTec.Specs

set_option maxRecDepth 100000

spectec_import wasm10 from "specs/spectec/wasm-1.0.ast"
spectec_import wasm20 from "specs/spectec/wasm-2.0.ast"
spectec_import wasm30 from "specs/spectec/wasm-3.0.ast"

/-- The definition counts recorded in `specs/spectec/manifest.json`. -/
example : wasm10.length = 315 := by rfl

example : wasm20.length = 467 := by rfl

example : wasm30.length = 976 := by rfl

spectec_crosscheck "specs/spectec/wasm-3.0.ast"
  with Silmaril.Wasm.SpecTec.instructionSchemas
  and Silmaril.Wasm.SpecTec.administrativeSchemas

end Silmaril.SpecTec.Specs
