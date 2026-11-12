module

public import Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Elide

/-!
# Eliding re-entry checks of the asyncify tool: theorems

Proofs in `Silmaril.Proofs.Wasm.FX.Asyncify.Tool.Elide` (Isar style); no `sorry`, no axiom beyond
Lean's.

* `Prog.elide_env`: the elision keeps the flat code, so the source program is unchanged;
  `Prog.elide_wf`: it keeps well-formedness; `DepthBound.elide_iff`: and the depth bound.
* `asyncify_elide_beh`: **the elided pass is correct** (the behaviours of the source and of the
  asyncified `P.elide` are equal, under the hypotheses of `asyncify_beh`).
* `elide_equiv`: **the guarded and the elided targets are equivalent** (equal behaviours).
* `elide_guards`: after elision there are at most as many `state ≠ 2` checks of pure statements
  as there are call statements, and no more than before (`elideS_alt`: pure statements alternate
  with calls, and none follows the last call).
* `asyncifyBytesE_spec`, `asyncifyBytesE_correct`: the tool with elided checks on bytes (the
  default of `wasm-asyncify`), end to end, with the equivalence to the guarded output.
-/
