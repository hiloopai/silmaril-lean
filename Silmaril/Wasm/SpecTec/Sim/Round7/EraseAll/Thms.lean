module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseAll.All
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseAll.Shape
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseAll.Root

/-!
# Round 7, the export swap: the whole evaluator commutes with erasure (round 3, pass 2, proved)

Item 1 of the plan for `Round7.Swap.Task.stepErase`, for all 29 members of the evaluator.
Definitions are in `Round7/EraseAll/Defs.lean`; see `docs/projects/spectec/README.md`.

* `eraseAt : Hyps Q gr gd env → ∀ n, EraseAt Q gr gd env n`. At every fuel, each member of the
  evaluator (`evalExp` … `anyRule`), run at the erased scope on erased values and arguments, gives
  the erased answer of the member run on the originals, and that answer stays in the swap set
  (`SG` for scopes). `patLen`, `derives` and `anyRule` answer the same.
* Without fuel: `evalExp_erase_iff`, `allIn_of_evalExp`, `derives_erase_iff`.
* `updSafe_of_shape : QShape Q → UpdSafe Q env`: updates along `updOk` paths keep the swap set
  when the records of `Q` look like module instances; `qShape_QC`, `updSafe_QC` for `QC c`, and
  `hyps_QC`, which leaves only the script check and the builtins open at `QC c`.
* `step_updRoot`: an update whose only field write is at the root (`rootOnly`, the shape of
  `$with_tableinst`/`$with_meminst`) commutes with erasure when the root has no `EXPORTS` field.

The hypotheses `Hyps` are: `QInj Q`; the clauses of the `gd` definitions and the rules of the `gr`
relations pass the syntactic check `xExp`; the builtins of `gd` names commute with erasure
(`BIErase`); and updates along `updOk` paths keep the swap set (`UpdSafe`). At `Q := QC c` the
first and last are discharged (`hyps_QC`); the syntactic check and `BIErase` are **not**
discharged here for the wasm-3.0 script: see the doc section for which names have to be left out
of `gd`/`gr` (`$with_tableinst`, `$with_meminst`, `$hostcall` and the relation `Step`), and why.

The proof is in `Raw/…/Round7/EraseAll/`, unrefined like the other round-7 evaluator inductions:
one theorem per member and fuel step (`step_exp`, …, `step_anyRule`), assembled in `eraseAt_succ`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.eraseAt' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms eraseAt

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.evalExp_erase_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms evalExp_erase_iff

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.derives_erase_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms derives_erase_iff

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.updSafe_of_shape' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms updSafe_of_shape

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.hyps_QC' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms hyps_QC

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll.step_updRoot' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms step_updRoot

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll
