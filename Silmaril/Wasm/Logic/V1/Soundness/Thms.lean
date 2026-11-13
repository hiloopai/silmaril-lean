module

public import Silmaril.Proofs.Wasm.Logic.V1.Soundness
public import Silmaril.Wasm.Logic.V1.Derived.Thms

/-!
# Soundness of Wasm Logic for WebAssembly 1.0

Theorem 2 of Watt, Maksimović, Krishnaswami and Gardner (ECOOP 2019), for
silmaril-lean's V1 semantics (`Silmaril.Wasm.V1.Execution`), every host relation
`host` (calls to imported functions are left to `host`; the logic itself only
verifies calls inside the module):

* `Triple.sound host n h specs : Valid host n Γ.funcs Γ.labels Γ.ret P code Q`:
  every derivable triple is valid for executions of derivation height at most
  `n`, relative to its assumed function specifications;
* `ModuleSpecs.sound`: the `[module]` rule, for mutually recursive function
  specifications;
* `ModuleSpecs.soundBig`, `Triple.soundBig`: the same against the unindexed
  big-step semantics;
* `ModuleSpecs.soundSteps`, `ModuleSpecs.not_trap`: a verified module's
  functions, run by the small-step semantics from a state satisfying the
  precondition, end in a state satisfying the postcondition and never trap.

The logic is one of **partial** correctness: `Valid` constrains terminating
executions only. Its hypotheses (`Silmaril.Wasm.Logic.V1.Judgement.Defs`) include
that the module has a linear memory (`ReifiesMem`), that its global addresses are
distinct (`ReifiesGlobals`) and that every call stays inside the module
(`ReifiesFuncs`).
-/