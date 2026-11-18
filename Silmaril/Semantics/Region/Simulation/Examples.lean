module

import Silmaril.Semantics.Region.Simulation.Thms

namespace Silmaril.Semantics.Region

private def branches : TransitionSystem Bool Bool Bool Bool where
  pc := id
  step initial events next := initial = false ∧ next = true ∧ (events = [] ∨ events = [true])
  halt initial stop := initial = false ∧ stop = true

example : FirstExit branches (· = false) false [] true :=
  .leave rfl ⟨rfl, rfl, .inl rfl⟩ (by decide)

example : ¬ NoUB branches (· = false) (· = false) (fun _ => False) (· = true) := by
  intro safe
  exact safe.2 false [] false true rfl (.refl rfl) ⟨rfl, rfl⟩ rfl

example : ¬ NoUB branches (· = false) (· = false) (· = true) (fun _ => False) := by
  intro safe
  exact safe.1 true rfl ⟨false, [], false, [true], true, rfl, .refl rfl, ⟨rfl, rfl, .inr rfl⟩, by simp⟩

#print axioms Realizes.transferContract
#print axioms Realizes.RefinesExits.comp

end Silmaril.Semantics.Region
