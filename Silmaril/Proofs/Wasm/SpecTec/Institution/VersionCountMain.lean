module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionCount
public import Silmaril.Wasm.SpecTec.Versions.Defs
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# `theory-diff`, wasm-1.0 pinned → main `e7a9df7c`, checked by the kernel

The tool reports 130 of 132 rules retained (`Export_ok` and `Module_ok` are redeclared); so does
the kernel.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Versions

open Silmaril.Wasm.SpecTec.Scripts

set_option maxRecDepth 100000 in
theorem retained_wasm10_main : retainedCount Wasm10.envOriginal Versions.Main.Wasm10.env = 130 := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Institution.Versions
