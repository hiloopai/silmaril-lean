module

public import Silmaril.Wasm.Verify.Check.Defs
public import Silmaril.Wasm.Verify.Reach.Thms
public import Silmaril.Wasm.Verify.Guard.Thms
public import Silmaril.Proofs.Wasm.Verify.Check.Basic
public import Silmaril.Proofs.Wasm.Verify.Check.Flow
public import Silmaril.Proofs.Wasm.Verify.Check.Refute
public import Silmaril.Proofs.Wasm.Verify.Check.Start
public import Silmaril.Wasm.Verify.Refute.Thms
public import Silmaril.Wasm.Verify.Start.Thms
public import Silmaril.Wasm.Verify.Flow.Thms
public import Silmaril.Wasm.Verify.From.Thms

@[expose] public section

/-!
# The verifier: soundness and the `wasm_check` tactic

Proofs in `Silmaril.Proofs.Wasm.Verify.Check.{Basic,Instance}`. Every profile `P`.

* `closedB_sound`, `avoidsB_sound`, `storeIn_of_rootsB`: the Boolean certificate checks imply
  the invariant hypotheses; `reachIn_of_check`: a `proved` verdict gives `ReachIn` for the
  module's instance.
* **`check_sound`**: if `IsInstance m mt I` and `(check m (.neverCall i)).verdict = .proved`,
  then `Models (neverCall …) (wasmSem P) (WasmProg.ofInstance I) i`, for every profile `P`.
* `check_neverCallFrom`: "never called" gives "never called while export `e` is active".
  The per-export analysis is `checkFrom` (`Silmaril.Wasm.Verify.From`): `checkFrom_sound`,
  `checkFrom_refuted_sound`, `checkFrom_closed_world`.
* **`check_closed_world`**: under the same hypotheses, in every Core run of every export call
  against every environment `K` (`hostOf I.imports K`), no configuration is about to call
  import `i`.
* `isInstance_of_instance?`, `isInstance_instOf`: the computed instance `instance? m` is the
  module's `IsInstance`; `check_neverCall`: the soundness theorem for `progOf m`, with both
  hypotheses decidable by kernel evaluation.
* Assertions (`Silmaril.Proofs.Wasm.Verify.Check.{Assert,Flow}`): `guardedB_sound`, `closedBA_sound`,
  `arityOne_sound`, `guardIn_of_closedBA`; the flow analysis: `funcOkF_sound`, `closedBF_sound`,
  `flowIn_of_closedBF`, `assertIn_of_check`; **`check_assert_sound`**: if `IsInstance m mt I` and
  `(check m (.assertNeverFalse i)).verdict = .proved`, then
  `Models (assertNeverFalse …) (wasmSem P) (WasmProg.ofInstance I) i` for every profile `P`;
  `check_assertNeverFalse` for `progOf m`.
* Refutations (`Silmaril.Proofs.Wasm.Verify.Check.Refute`): **`check_refuted_sound`**: if
  `IsInstance m mt I` and `(check m (.neverCall i)).verdict = .refuted`, then
  `¬ Models (neverCall …) (wasmSem P) (WasmProg.ofInstance I) i` for every profile `P` admitting
  the deterministic steps of `profile refOracle` (`check_refuted_sound_spec`: every specification
  profile `Profile.spec nd {}`); `check_refuted_trace`: the reason is `counterexample x` and a trace
  calls `i` with `x.callArgs`; `check_assert_refuted_sound(_spec)`: the same for assertions;
  `check_refuted_closed_world`: some export call reaches a callout of `i` against every
  environment.
* Start functions (`Silmaril.Proofs.Wasm.Verify.Check.Start`): `cfgInB_sound`;
  **`check_start_sound`**: if `IsSpecInstance m mt I c₀`, the module has a start function and
  `check` proves `neverCall i`, no play of `I.specStrategy P c₀` (instantiation phase included)
  asks import `i`, every profile; `check_start_closed_world`; `isSpecInstance_of_specInstance?`.

## `wasm_check`, `wasm_refute`

`wasm_refute` closes `¬ Models (neverCall …) (wasmSem (Profile.spec nd {})) (progOf m) i` (and
the same for `assertNeverFalse` and `neverCallFrom`) through `check_refuted_neverCall`
(`check_refuted_assertNeverFalse`, `checkFrom_refuted_neverCallFrom`), by kernel evaluation of
the verifier and its interpreter run.

`wasm_check` closes goals `Models (neverCall …) (wasmSem P) (progOf m) i`,
`Models (assertNeverFalse …) (wasmSem P) (progOf m) i` and
`Models (neverCallFrom …) (wasmSem P) (progOf m) (i, e)` (and, given `IsInstance m mt I` in
context, the same goals about `WasmProg.ofInstance I`): it applies `check_neverCall` /
`check_assertNeverFalse` / `checkFrom_neverCallFrom` (resp. `check_sound` /
`check_assert_sound` / `checkFrom_sound`) and discharges the
instance and verdict hypotheses with `decide +kernel` (kernel evaluation of `validate?`,
`instantiateOnce?` and the analysis; no compiled evaluation).
-/

namespace Silmaril.Wasm.Verify

/-- Discharge a `neverCall`, `assertNeverFalse` or `neverCallFrom` sentence about a module by
running the verifier in the kernel. -/
macro "wasm_check" : tactic => `(tactic| first
  | (apply check_neverCall <;> decide +kernel)
  | (apply check_assertNeverFalse <;> decide +kernel)
  | (apply check_sound ‹_›; decide +kernel)
  | (apply check_assert_sound ‹_›; decide +kernel)
  | (apply checkFrom_neverCallFrom <;> decide +kernel)
  | (apply checkFrom_sound ‹_›; decide +kernel))

/-- Refute a `neverCall`, `assertNeverFalse` or `neverCallFrom` sentence about a module at a
specification profile (`¬ Models … (wasmSem (Profile.spec nd {})) (progOf m) i`) by running the
verifier, and its counterexample search, in the kernel. -/
macro "wasm_refute" : tactic => `(tactic| first
  | (apply check_refuted_neverCall <;> decide +kernel)
  | (apply check_refuted_assertNeverFalse <;> decide +kernel)
  | (apply checkFrom_refuted_neverCallFrom <;> decide +kernel))

end Silmaril.Wasm.Verify
