module

public import Silmaril.Wasm.Auto2.Calls.Defs
public import Silmaril.Raw.Wasm.Auto2.Calls.Mod

/-!
# Function summaries with inlined calls: results

Proofs in `Silmaril.Raw.Wasm.Auto2.Calls.{Run,Sound,Func,Mod}` (unrefined). For the executor of
`Silmaril.Wasm.Auto2.Calls.Defs` (loops unrolled, calls to Wasm functions of the same instance
inlined):

* `wp_callIdx_iff`: `call x` steps only to `ref.func a; call_ref` of the function it names;
* **`wp_xsexecC`**: the executor is sound against the every-run logic (both readings, every
  profile and host relation), in every typed context with a correct function environment
  (`FEnvOk`; `calleeOf_ok`: the environment read from the store is correct). A call is the
  callee's body pinned to its symbolic outcome (`Silmaril.Wasm.Auto.EquivFn.wp_call_pinned`);
* `tfspecC_of_sumOfC`, **`behaviours_of_fnSumC`**: every accepted invocation of a summarised
  export terminates and returns or traps as `fnOutX F vs` says, at every profile;
* **`modEquiv_of_fnCheckC`**, **`modEquiv_of_checkAmongC`**: the guard-aware check of
  `Silmaril.Wasm.Auto2.Summ` on these summaries proves `ModEquiv`;
* **`checkEquivC_proved`**, `checkRefinesC_proved`, `modEquiv_of_proveStageC`,
  `checkEquivC_refuted`: the front end (the basic stages, the unrolled summaries, then these;
  stage `equivc`).

Recursive callees exhaust the fuel (no summary). Calls through tables (`call_indirect`,
`call_ref`), host functions and callees of another instance are not inlined.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.Calls

/-- Close `ModEquiv R.toProp P m₁ m₂ j` by kernel evaluation of the proving stages, up to the
summaries with inlined calls. -/
macro "wasm_provec" : tactic =>
  `(tactic| exact Silmaril.Wasm.Auto2.Calls.modEquiv_of_proveStageC (by decide +kernel) _ _)

end Silmaril.Wasm.Auto2.Calls
