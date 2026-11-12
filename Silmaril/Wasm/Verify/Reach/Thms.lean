module

public import Silmaril.Wasm.Verify.Reach.Defs
public import Silmaril.Proofs.Wasm.Verify.Reach.Plays

@[expose] public section

/-!
# Function reachability over Core 3.0 stores: results

Proofs in `Silmaril.Proofs.Wasm.Verify.Reach.*`. Every profile `P`; no determinism is assumed.

* `Step.cfgIn`: **every Core 3.0 step rule preserves the reachability invariant** `CfgIn G fs`
  (references in code, locals and store in `G`; source instructions naming only functions in
  `G`), for hosts returning the store unchanged with references in `G` (`HostIn`), given
  `FuncsClosed G fs` for the function instances (which steps never change).
  - The delegated families: `VariableStep.cfgIn`, `TableStep.cfgIn`, `MemoryStep.cfgIn`,
    `RefStep.cfgIn`, `AggregateStep.cfgIn`, `ParametricStep.out`, `NumericStep.out`,
    `VectorStep.out`.
  - The store updates: `StoreIn.setGlobal`, `setTable`, `setElemNil`, `setStructField`,
    `setArrayField`, `addStruct`, `addArray`, `addExn`.
* `reach_cfgIn`: host-free runs `Reach P` preserve it; `callout_ne`: a callout of an
  invariant thread is not an avoided import; `resume_cfgIn`: resuming with a scalar answer
  keeps it.
* `trans_hInv`, `path_hInv`: every transition of the instance's transition system keeps the
  hidden-state invariant `HInv` and never asks an avoided import.
* `strategy_no_icall`: no play of `I.strategy P I.store` asks import `i`, under `ReachIn I G fs i`.
* **`neverCall_of_reachIn`**: the program `WasmProg.ofInstance I` satisfies `neverCall i` in
  `inst neverCall (wasmSem P)`.
* **`neverCall_closed_world`**: in every Core run `Steps P (hostOf I.imports K)` of an export
  call, against every environment `K`, no configuration is about to call import `i`.
-/
