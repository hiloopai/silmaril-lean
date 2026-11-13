module

public import Silmaril.Compiler.Core.Verified.Slots.Defs
/-! # Concrete witnesses for the multi-local frame rules

Two adjacent allocations, storing distinct values, overwriting one, and killing it.
The second local must retain its original bytes. The race checks distinguish touching
endpoints from a one-byte overlap, including a write on either side.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.SlotsChecks

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Cerberus.Core.Dynamics
open Mem.Concrete (LiveInt)
open Locals (Slot stored killed)
open Slots

def memory : Mem.Concrete.State :=
  {nextId := 2, lastAddress := 4096,
    allocations := (∅ : Map Int Mem.Concrete.Allocation).insert 0 {base := 4096} |>.insert 1 {base := 4100}}

theorem first_live : LiveInt memory 0 4096 := by
  refine ⟨by simp [memory], ⟨{base := 4096}, ?_, rfl, rfl, rfl, rfl⟩⟩
  simp only [memory, Map.lookup_insert_of_key_ne _ _ (show MapKey.key (0 : Int) ≠ MapKey.key (1 : Int) by decide), Map.lookup_insert]

theorem second_live : LiveInt memory 1 4100 := by
  refine ⟨by simp [memory], ⟨{base := 4100}, ?_, rfl, rfl, rfl, rfl⟩⟩
  simp [memory]

/-- The initial frame-rule hypotheses really hold for two concrete live objects. -/
theorem two_values :
    let m := stored (stored memory 0 4096 17) 1 4100 (-23)
    Slot m 0 4096 17 ∧ Slot m 1 4100 (-23) := by
  exact ⟨slot_stored (Locals.stored_slot first_live 17) 1 4100 (-23) (by unfold Apart; decide),
    Locals.stored_slot (live_stored second_live 0 4096 17) (-23)⟩

/-- Overwriting and then killing the first local preserves the adjacent second local. -/
theorem overwrite_then_kill :
    let m := stored (stored (stored memory 0 4096 17) 1 4100 (-23)) 0 4096 99
    Slot m 0 4096 99 ∧ Slot (killed m 0) 1 4100 (-23) := by
  refine ⟨Locals.stored_slot (live_stored (live_stored first_live 0 4096 17) 1 4100 (-23)) 99, ?_⟩
  exact slot_killed (slot_stored two_values.2 0 4096 99 (by unfold Apart; decide)) 0 (by decide)

/-- A third allocation below the two live objects preserves both initialized values. -/
theorem create_preserves_two :
    let m := stored (stored memory 0 4096 17) 1 4100 (-23)
    let m' := Actions.created (.other "third") [] m
    Slot m' 0 4096 17 ∧ Slot m' 1 4100 (-23) := by
  exact ⟨slot_created two_values.1 (.other "third") [] (by decide) (by unfold Apart; decide),
    slot_created two_values.2 (.other "third") [] (by decide) (by unfold Apart; decide)⟩

/-- The finite collection rule updates exactly one local's value. -/
theorem collection_store :
    let m := stored (stored memory 0 4096 17) 1 4100 (-23)
    Holds (stored m 0 4096 99) [⟨0, 4096, 99⟩, ⟨1, 4100, -23⟩] := by
  let locals : List Local := [⟨0, 4096, 17⟩, ⟨1, 4100, -23⟩]
  have h : Holds (stored (stored memory 0 4096 17) 1 4100 (-23)) locals := by
    intro l hl
    simp only [locals, List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · exact two_values.1
    · exact two_values.2
  have d : Disjoint locals := by unfold Slots.Disjoint Apart; decide
  simpa [locals] using holds_store_disjoint h d ⟨0, 4096, 17⟩ (by simp [locals]) 99

example : races ⟨none, [], true, 4096, 4⟩ ⟨none, [], false, 4100, 4⟩ = false := by decide
example : races ⟨none, [], false, 4100, 4⟩ ⟨none, [], true, 4096, 4⟩ = false := by decide
example : races ⟨none, [], true, 4096, 4⟩ ⟨none, [], false, 4099, 4⟩ = true := by decide
example : races ⟨none, [], true, 4099, 4⟩ ⟨none, [], false, 4096, 4⟩ = true := by decide
example : races ⟨some 3, [], true, 4096, 4⟩ ⟨none, [3], false, 4096, 4⟩ = false := by decide

end Silmaril.Compile.Core.Verified.SlotsChecks
