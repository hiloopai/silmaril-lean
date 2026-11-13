module

public import Silmaril.Proofs.Wasm.SpecTec.Institution.VersionCount
import all Silmaril.Raw.Wasm.SpecTec.SpecTec.Specs

/-!
# `theory-diff` totals, checked by the kernel

The number of rules (with multiplicity) of the pinned wasm-1.0, wasm-2.0 and wasm-3.0 scripts,
the denominators of `spectec-gen theory-diff`'s rows. `ruleList env` enumerates
`theoryOf env` (`theoryOf_eq_ruleList`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Institution.Versions

open Silmaril.Wasm.SpecTec.Scripts

set_option maxRecDepth 100000 in
theorem ruleList_wasm10_length : (ruleList Wasm10.envOriginal).length = 132 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ruleList_wasm20_length : (ruleList Wasm20.envOriginal).length = 259 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ruleList_wasm30_length : (ruleList Wasm30.envOriginal).length = 566 := by
  decide +kernel

end Silmaril.Wasm.SpecTec.Institution.Versions
