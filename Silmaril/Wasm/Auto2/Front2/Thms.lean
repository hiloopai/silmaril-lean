module

public import Silmaril.Wasm.Auto2.Front2.Defs
public import Silmaril.Raw.Wasm.Auto2.Front2.Mod

/-!
# The front end with stages `equivv` and `vcequiv`: results

Proofs in `Silmaril.Raw.Wasm.Auto2.Front2.Mod` (unrefined): **`checkEquivV_proved`**,
`checkRefinesV_proved`, `modEquiv_of_proveStageV` (a `proved` report is `ModEquiv` at every
profile, for both front-end relations) and `checkEquivV_refuted` (a `refuted` report is a
refutation at the deterministic profile). `wasm_provev` closes `ModEquiv R.toProp P m₁ m₂ j` by
kernel evaluation of the proving stages.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.Front2

/-- Close `ModEquiv R.toProp P m₁ m₂ j` by kernel evaluation of the proving stages of `checkEquivV`. -/
macro "wasm_provev" : tactic =>
  `(tactic| exact Silmaril.Wasm.Auto2.Front2.modEquiv_of_proveStageV (by decide +kernel) _ _)

end Silmaril.Wasm.Auto2.Front2

/--
info: 'Silmaril.Wasm.Auto2.Front2.checkEquivV_proved' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms Silmaril.Wasm.Auto2.Front2.checkEquivV_proved
