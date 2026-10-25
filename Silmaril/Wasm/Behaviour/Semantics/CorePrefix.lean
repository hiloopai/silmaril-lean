module

public import Silmaril.Wasm.Behaviour.Semantics.Core
public import Silmaril.Wasm.SingleThreaded.NoRedex

@[expose] public section

/-! # Behaviours along a uniquely determined administrative prefix

Numerics and host calls may remain nondeterministic after the prefix. Only the
individual administrative step needs a unique successor.
-/

namespace Silmaril.Wasm.Execution.Core

open Silmaril.Wasm.Numerics (Profile)
open Silmaril.Wasm.SingleThreaded

variable {H : Type}

/-- A configuration with exactly one successor has the behaviours of that successor.
This only requires uniqueness of this step, not determinism of the profile or host. -/
theorem behavioursOf_eq_of_step_unique {P : Profile} {host : HostSemantics H}
    {c c₁ : Config H} (h : Step P host c c₁)
    (hu : ∀ c', Step P host c c' → c' = c₁) :
    behavioursOf P host c = behavioursOf P host c₁ := by
  refine Set.Subset.antisymm ?_ (behavioursOf_mono_steps (.single h))
  rintro b (⟨e, r, hce, hfin, rfl⟩ | ⟨rfl, hdiv⟩)
  · rcases Relation.ReflTransGen.cases_head hce with rfl | ⟨c', hc', hc'e⟩
    · apply (Step.not_quiet h).elim
      rw [hfin]
      cases r with
      | values vs => exact quiet_vals vs
      | trap => exact quiet_trap
      | throw a => exact quiet_throwing a
    · rw [hu c' hc'] at hc'e
      exact Or.inl ⟨e, r, hc'e, hfin, rfl⟩
  · obtain ⟨c', hc', hdiv'⟩ := InfiniteTrace.unfold hdiv
    rw [hu c' hc'] at hdiv'
    exact Or.inr ⟨rfl, hdiv'⟩

end Silmaril.Wasm.Execution.Core
