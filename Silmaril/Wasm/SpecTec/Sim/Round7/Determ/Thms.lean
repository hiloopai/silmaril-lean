module

public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.Determ.Agree

/-!
# SpecTec ↔ Core 3.0, round 7: `Round7.Task.envAgreeNE` is proved (round 2, pass 3)

* `typMapNoExp_A`, `detRelsOk_fixed` (kernel, `decide +kernel`): no type over `tyA` declares an
  `EXPORTS` field; every rule of every relation `Step` reaches passes the mode check.
* `evalEF` (unrefined): the evaluator keeps values `ExpFree` on harmless syntax; `matchEF`:
  matching keeps scopes `ExpFree`; `ef_inv`: inverting the evaluator on `ExpFree` values;
  `typEF`/`ef_of_hasTyp_A`: values typed over `tyA` are `ExpFree`.
* `dderivesB_E`: **determination**. In `utf8Env B`, with primitives that preserve `ExpFree`, a
  derivation of a relation `Step` reaches at an `ExpFree` input binds every quantifier to an
  `ExpFree` value (`Round7.Transfer.DDerivesBE`), and its value is `ExpFree`.
* `otherwiseAtB_iff`: `otherwise` reads alike in `utf8Env B` and `simEnv B` at an `ExpFree` input;
  `sStepB_utf8Env_iff`: so does SpecTec's `Step` at an `ExpFree` configuration.
* `builtinsEF_BI` (unrefined): round 6's primitives preserve `ExpFree` at an export-blind host.
* **`envAgreeNE : Round7.Task.envAgreeNE`**, hence `wholeStepValidREI_of_swapEquiv`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.Determ

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.Determ.detRelsOk_fixed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms detRelsOk_fixed

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.Determ.dderivesB_E' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms dderivesB_E

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.Determ.sStepB_utf8Env_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms sStepB_utf8Env_iff

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.Determ.builtinsEF_BI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms builtinsEF_BI

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.Determ.envAgreeNE' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms envAgreeNE

end Silmaril.Wasm.SpecTec.Sim.Round7.Determ
