module

public import Silmaril.Wasm.Auto2.Summ.Defs
public import Silmaril.Raw.Wasm.Auto2.Summ.Mod

/-!
# Function summaries with unrolled loops: results

Proofs in `Silmaril.Raw.Wasm.Auto2.Summ.{Simp,Func,Mod}` (unrefined). For the summaries of
`Silmaril.Wasm.Auto2.Summ.Defs` (the unrolling executor `Silmaril.Wasm.Auto.EquivUnroll.xsexecU` run on whole bodies from the call
frame, the instance's globals and memory `0`) and the guard-aware check:

* `evX_simp2`, `evX_canon2`: the second simplifier preserves values; `holds_gkey`: a guard and
  its key hold together; `holds_of_gdead`: a dead guard never holds;
* `tfspecU_of_sumOfU`: a function with a summary has the total specification "its outcome is
  that of `fnOutX F vs`", every profile and host relation (loops unrolled: the summary exists
  only when every iteration's condition is decided, so the function terminates);
* **`behaviours_of_fnSumU`**: every accepted invocation of a summarised export terminates and
  returns or traps as `fnOutX F vs` says, at every profile;
* `out_of_sumCheckU`, **`modEquiv_of_fnCheckU`**, **`modEquiv_of_checkAmongU`**: the check proves
  `ModEquiv` (both front-end relations, every profile);
* **`checkEquivU_proved`**, `checkRefinesU_proved`, `modEquiv_of_proveStageU`: a `proved` report
  of the front end (the basic stages, then this one, stage `equivu`) proves `ModEquiv` at every
  profile; `checkEquivU_refuted`: a `refuted` report is a refutation at the deterministic
  profile.

What the statements observe is what `Silmaril.Wasm.Auto.Bridge.Thms` describes: one invocation of
the export from the instantiated store, its result or trap.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.Summ

/-- Close `ModEquiv R.toProp P m₁ m₂ j` by kernel evaluation of the proving stages: the basic
stages and summaries, then the unrolled summaries with the guard-aware check. -/
macro "wasm_proveu" : tactic =>
  `(tactic| exact Silmaril.Wasm.Auto2.Summ.modEquiv_of_proveStageU (by decide +kernel) _ _)

end Silmaril.Wasm.Auto2.Summ
