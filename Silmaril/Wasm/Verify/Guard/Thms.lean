module

public import Silmaril.Wasm.Verify.Guard.Defs
public import Silmaril.Wasm.Verify.Reach.Thms
public import Silmaril.Proofs.Wasm.Verify.Guard.Plays

@[expose] public section

/-!
# Guarded calls: results

Proofs in `Silmaril.Proofs.Wasm.Verify.Guard.*`. Every profile `P`; no determinism is assumed.

* `guardPl_plainOK`: the instruction predicate `GuardPl G B fs` satisfies the requirements of
  the reachability invariant, with guarded calls into `B`; so `Step.cfgIn` (reachability) applies:
  every step keeps `CfgIn G fs (GuardPl G B fs)` or is a call of a function in `B` (`BadStep`).
* `chain_expression`: a `Guarded` source sequence follows the runtime guard discipline `Chain`
  from any state.
* **`Step.pair`**: every Core 3.0 step rule (any host) keeps the guard discipline in every
  suffix context and in nested bodies (`PairPost`); the families: `ParametricStep.pair`, …,
  `AggregateStep.pair`; the contexts: `pair_ctxtInstrs`, `pair_ctxtLabel`, `pair_ctxtHandler`,
  `pair_ctxtFrame`; `fill_pair` for evaluation contexts.
* `guard_ctx`: a bad call `E.fill [call x]` under the discipline has a guard `i32.const c`,
  `c ≠ 0`, right before it; `decompose_fill`: the host-call redex of
  `E.fill (vals args ++ [ref.func a, call_ref])` is found at `E` with arguments `args`.
* `step_invA`, `reach_invA`: host-free runs keep threads invariant (`InvA`) or stop at a guarded
  call of the assertion (`GuardedA`), which is a callout with argument `[c]`
  (`guardedA_decompose`).
* `trans_hInvA`, `strategy_assertOk`: under `GuardIn I G fs i`, every import question of `i` in
  every play of `I.strategy P I.store` has a first argument other than `i32 0`.
* **`assertNeverFalse_of_guardIn`**: the program `WasmProg.ofInstance I` satisfies
  `assertNeverFalse i` in `inst assertNeverFalse (wasmSem P)`.
-/
