module

public import Silmaril.Wasm.Verify.Flow.Defs
public import Silmaril.Proofs.Wasm.Verify.Flow.Plays

@[expose] public section

/-!
# Assertion arguments through locals: results

Proofs in `Silmaril.Proofs.Wasm.Verify.Flow.*`. Every profile `P`; no determinism is assumed.

* `callPl_plainOK`: the call predicate `CallPl` meets the requirements of the reachability
  invariant (`Step.cfgIn`), with calls of the assertion as the bad steps.
* `okL_mono`, `okA_mono`: the checks are monotone in the abstract state (`FLe`: more facts, a
  more precise top of the stack); `okA_append`, `okA_expression`, `okA_vals_append`.
* **`Step.flow`**: every Core 3.0 step rule (any host) keeps the flow invariant (`FlowPost`):
  facts about stable locals stay sound (stable locals are only written with nonzero `i32`s),
  every continuation stays checked with possibly more facts, nested bodies are checked; the
  families `ParametricStep.flow`, …, `AggregateStep.flow`, `VariableStep.flow` (`flow_localGet`,
  `flow_localSet`, `flow_localTee`); `flow_ifTrue`, `flow_ifFalse`, `flow_block`, `flow_loop`,
  `flow_tryTable`, `flow_brLabelZero`, `flow_callRefFunc`; the contexts `flow_ctxtInstrs`,
  `flow_ctxtLabel`, `flow_ctxtHandler`, `flow_ctxtFrame`; `fill_flow`.
* `flow_guard`: a call of the assertion under the invariant is preceded by a value other than
  `i32 0`; `step_invF`, `reach_invF`: host-free runs keep threads invariant or stop at such a call
  (`guardedF_decompose`: a callout of the assertion with that value).
* `strategy_assertOk_flow`: under `FlowIn I G fs i`, every import question of `i` in every play of
  `I.strategy P I.store` has a first argument other than `i32 0`;
  **`assertNeverFalse_of_flowIn`**: the program satisfies `assertNeverFalse i` in
  `inst assertNeverFalse (wasmSem P)`.
-/
