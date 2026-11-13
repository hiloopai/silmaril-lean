module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionCount
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# `theory-diff`, wasm-2.0 → wasm-3.0, checked by the kernel

The tool reports 9 of wasm-2.0's 259 rules retained by wasm-3.0; so does the kernel.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Versions

open Silmaril.Wasm.SpecTec.Scripts

set_option maxRecDepth 100000 in
theorem retained_wasm20_wasm30 : retainedCount Wasm20.envOriginal Wasm30.envOriginal = 9 := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Institution.Versions
