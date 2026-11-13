module

public import Silmaril.Wasm.Component.FXRes.ContRun.Defs
public import Silmaril.Proofs.Wasm.Component.FXRes.ContRun.Init

/-!
# Running the `cont` component over the WasmFX engine with a continuation table: results

Proofs in `Silmaril.Proofs.Wasm.Component.FXRes.ContRun.Init`, at every profile `P`, choice
profile and host:

* `silentRun_contInst` (kernel evaluation, `P` free): the instantiation program of `contComp`
  over `fxCE P` runs silently from the empty store to `contInst P`, observing root instance `0`
  and the exports `contEs` (`make`, `run`);
* `contInst_ctl`, `contInst_lockdown`, `contInst_nesting`: after it the host is in control, the
  store is not locked down and no call is running; `contInst_tab`: the engine's continuation
  table is empty; `contInst_vtab`: the `cont` handle table of instance `0` is empty;
* **`cont_instBehaviours`**: the only result of instantiating `contComp` is the instance at
  `contInst P` (no trap, no divergence); **`cont_instantiates`**: it is a result.

So `contComp` is instantiated concretely by the reference component machine over `fxCE P`.
The engine-generic run tools `hostRun_inv'`, `steps_ctl_nil'`, `detRunL_end'` generalize the
`core3P` ones of `Silmaril.Wasm.Component.Reference.Silent`.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRes.ContRun

/-- info: 'Silmaril.Wasm.Component.FXRes.ContRun.cont_instBehaviours' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cont_instBehaviours

/-- info: 'Silmaril.Wasm.Component.FXRes.ContRun.cont_instantiates' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms cont_instantiates

end Silmaril.Wasm.Component.FXRes.ContRun
