module

public import Silmaril.Wasm.SpecTec.Sim.Round7.REGap.Defs
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round7.REGap.Collide

/-!
# what separates REH from what is proved (proved)

Namespace `Silmaril.Wasm.SpecTec.Sim.Round7.REGap`; see `docs/projects/spectec/README.md`, "re (pass
1)". Definitions (`stripCloneHost`, `StoreCollides`) are in `Round7/REGap/Defs.lean`.

* `stripInj_strict`: **a valid, `BoundedSelE` configuration that fails `StripInj`**
  (`collideCfg`); it takes a step, and its only successor (`step_collide_inv`) is in
  `BoundedSelE`. `Round7.HostMods.stepValidREM_holds` and
  `Round7.Task.wholeStepValidREI` say nothing about it; `Round7.Task.wholeStepValidREH` does.
* `stripCloneHost_breaks`: **a finite, `HostOk`, export-blind host that invents modules, and one
  call of it that creates a collision** from a store with a single function instance.
  `not_stripInj_of_collide`: no configuration over the returned store has `StripInj`.

So the two hypotheses REH drops are linked. Keeping `StripInj` and dropping only `HostModsSub`
(route 1 of the round-5 re pass-3 section) gives at best a one-step theorem: its run version
needs `StripInj` at every successor, and `stripCloneHost` removes it after one host call.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.REGap

open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Sim.Round7.HostMods (HostModsSub)

/-- **`StripInj` is a real restriction**: some valid, `BoundedSelE` configuration fails it. At
every profile and host it takes a step, and every successor is in `BoundedSelE`, so it is in the
domain of both halves of `Round7.Task.wholeStepValidREH`. -/
theorem stripInj_strict {H : Type} :
    ∃ c : Config H, ConfigOk c [] ∧ BoundedSelE c ∧ ¬ StripInj c ∧
      ∀ P host, (∃ c', Step P host c c') ∧ ∀ c', Step P host c c' → BoundedSelE c' :=
  ⟨collideCfg, configOk_collide, boundedSelE_collide, not_stripInj_collide,
    fun P host => ⟨⟨_, step_collide P host⟩, fun _ h => succ_boundedSelE_collide h⟩⟩

/-- A host function instance on `Unit` whose module exports a name. -/
def expFI : FuncInst Unit :=
  { type := .defn (.group .nil) 0, module := ConfigOk.exportModule, code := .host () }

/-- **A finite, `HostOk`, export-blind host that invents modules can break `StripInj` in one
call**: at the store holding only `expFI` (no collision), it returns a store whose modules
collide. -/
theorem stripCloneHost_breaks :
    HostFinite (stripCloneHost (H := Unit)) ∧ HostOk (stripCloneHost (H := Unit)) ∧
      HostExportBlind (stripCloneHost (H := Unit)) ∧ ¬ HostModsSub (stripCloneHost (H := Unit)) ∧
      ¬ StoreCollides ({ funcs := [expFI] } : Store Unit) ∧
      ∃ s', stripCloneHost () { funcs := [expFI] } [] (.returned s' .trap) ∧ StoreCollides s' := by
  have hx : expFI.module.exports ≠ [] := by simp [expFI, ConfigOk.exportModule]
  obtain ⟨ho, hc⟩ := collides_stripClone () [] (s := { funcs := [expFI] }) (List.mem_singleton_self expFI) hx
  exact ⟨stripCloneHost_finite, stripCloneHost_ok, stripCloneHost_blind,
    not_modsSub_stripCloneHost () expFI hx, not_collides_single expFI, _, ho, hc⟩

/-! ## Axiom audit (checked by `#guard_msgs`) -/

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.REGap.stripInj_strict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stripInj_strict

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.REGap.stripCloneHost_breaks' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms stripCloneHost_breaks

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.REGap.not_stripInj_of_collide' depends on axioms: [propext, Classical.choice] -/
#guard_msgs (whitespace := lax) in #print axioms not_stripInj_of_collide

/-- info: 'Silmaril.Wasm.SpecTec.Sim.Round7.REGap.step_collide_inv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms step_collide_inv

end Silmaril.Wasm.SpecTec.Sim.Round7.REGap
