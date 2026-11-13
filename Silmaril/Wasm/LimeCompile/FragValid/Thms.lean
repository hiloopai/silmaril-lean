module

public import Silmaril.Wasm.LimeCompile.Frag.Defs

/-!
# The 3.0 → Lime compiler: `Frag.Task.lime1ValidOfCore` is false

An earlier step froze `Frag.Task.lime1ValidOfCore`: Lime1 validation reflects Core validation of the
Core image. It is **refuted** here. Lime1 validation keeps the 1.0 restriction to at most one
memory (`Lime1.Validation.ModuleValid.singleMemory`), while Core 3.0 has multiple memories:

* `twoMems`: the Lime1 module with two memories `(memory 0) (memory 0)` and nothing else;
* `twoMems_coreOk`: its Core image is valid (`ModuleOk twoMems.toCore ⟨[], []⟩`);
* `twoMems_not_lime1`: it is not Lime1-valid;
* **`not_lime1ValidOfCore`**: `¬ Frag.Task.lime1ValidOfCore`.

So the conditional results of `Frag.Thms` that assume the task (`frag_of_numFrag_task`) are
vacuous; the unconditional `container_correct_num` (Core validity of the output, derived from
the source) is the statement to use. A corrected target would have to add the single-table /
single-memory conditions (and possibly other 1.0 restrictions) to the hypothesis; that is not
attempted here.

New statements over `Silmaril.Wasm.LimeCompile.Frag`.
-/

@[expose] public section

namespace Silmaril.Wasm.LimeCompile.FragValid

open Silmaril.Wasm Silmaril.Wasm.Validation

/-- The empty memory type `(memory 0)`. -/
def mem0 : V1.MemoryType := ⟨⟨0, none⟩⟩

/-- **A Lime1 module with two memories.** -/
def twoMems : Lime1.Module where
  types := []
  imports := []
  funcs := []
  globals := []
  tables := []
  memories := [mem0, mem0]
  elems := []
  data := []
  start := none
  exports := []

/-- Its Core image is valid (Core 3.0 has multiple memories). -/
theorem twoMems_coreOk : ModuleOk twoMems.toCore ⟨[], []⟩ := by
  refine ModuleOk.mk (dts := []) (jts := []) (gts := []) (tts := []) (fdts := []) (rts := [])
    .nil .nil rfl rfl .nil .nil ?_ .nil .nil (by simp [Lime1.Module.toCore, twoMems])
    .nil (by simp [Lime1.Module.toCore, twoMems]) .nil (by simp [Lime1.Module.toCore, twoMems])
  intro mt hmt
  simp only [Lime1.Module.toCore, twoMems, List.map, List.mem_cons, List.not_mem_nil,
    or_false, or_self] at hmt
  subst hmt
  unfold MemOk MemTypeOk
  decide

/-- It is not Lime1-valid: two memories. -/
theorem twoMems_not_lime1 : ¬ Lime1.Validation.ModuleValid twoMems := by
  intro h
  have := h.singleMemory
  simp [Lime1.Validation.moduleContext, twoMems] at this

/-- **`Frag.Task.lime1ValidOfCore` is false.** -/
theorem not_lime1ValidOfCore : ¬ Frag.Task.lime1ValidOfCore :=
  fun h => twoMems_not_lime1 (h twoMems ⟨_, twoMems_coreOk⟩)

/-- info: 'Silmaril.Wasm.LimeCompile.FragValid.not_lime1ValidOfCore' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms not_lime1ValidOfCore

end Silmaril.Wasm.LimeCompile.FragValid
