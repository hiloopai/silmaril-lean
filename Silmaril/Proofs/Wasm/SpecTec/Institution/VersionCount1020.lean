module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionCount
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# `theory-diff`, wasm-1.0 → wasm-2.0, checked by the kernel

`spectec-gen theory-diff` reports 49 of wasm-1.0's 132 rules retained by wasm-2.0. The
kernel evaluates `retainedCount` to the same number; by `inTheoryB_iff_retained` it counts the
entries of `ruleList` (the rules of `theoryOf`) that lie in `retained`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Versions

open Silmaril.Wasm.SpecTec.Scripts

set_option maxRecDepth 100000 in
theorem retained_wasm10_wasm20 : retainedCount Wasm10.envOriginal Wasm20.envOriginal = 49 := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Institution.Versions
