module

public import Silmaril.Wasm.Logic.Iris.Adequacy.Defs
public import Silmaril.Wasm.Logic.Iris.Rules.Thms
public import Silmaril.Proofs.Wasm.Logic.Iris.Adequacy

/-!
# The Iris logic of Wasm Core 3.0: adequacy

Upstream iris-lean's adequacy (`Iris.ProgramLogic.wp_adequacy`) for the language
`IExpr P host`, read back into pinned silmaril-lean's Core 3.0 semantics
`Step P host` through the every-run weakest precondition
`Silmaril.Wasm.Logic.Hoare.HWP` (proofs in `Silmaril/Proofs/Wasm/Logic/Iris/Adequacy.lean`):

* `hwp_of_adequate`: Iris's `adequate .NotStuck` for `run code` gives `HWP`;
* **`wp_hwp`**: a weakest precondition proved from the ownership of cells `ps`
  that the store holds (`Cells ps s f`, distinct locations), for every allocation
  of the ghost names, with a pure postcondition `Q` on the final store, frame
  and outcome, gives `HWP P host s f code Q`: every run is safe and every exit
  (values, branch, return, trap, exception, tail call) satisfies `Q`;
* `wp_sound` (safety), `wp_sound_vals` (terminating runs);
* **`ITriple.sound`**: an Iris triple gives the Silmaril triple
  `Silmaril.Wasm.Logic.Hoare.Triple`.

All hold for every profile and every host relation, and for every bundle of
functors with `WasmGpreS` (for example `WasmGF`).
-/