module

public import Silmaril.Foundations.ForwardSim
public import Silmaril.Wasm.Behaviour.Semantics.Core

@[expose] public section

/-! # Same-language simulations of Core 3.0 and their observable consequences

`ConfigSim P host Rel` is a stuttering forward simulation of the Core 3.0 step
relation `Step P host` *with itself*, over a relation `Rel` between two
configurations (typically: same frame, related stores, related code). It is the
`Silmaril.ForwardSim` of `Silmaril/Foundations/ForwardSim.lean` (measure-bounded
stuttering) plus the one obligation that kit leaves out, result transport: a
terminal left configuration is matched by a right run to *the same* result.

This is the layer below every code-transformation proof in this directory: a
code relation is proved sound by building a `ConfigSim` (`Sim/Closure.lean`),
and `ConfigSim.behavioursOf_subset` / `ConfigSim.behavioursOf_eq` turn it into
inclusion or equality of `behavioursOf` (`Silmaril/Wasm/Behaviour/Semantics/Core.lean`),
which covers values, traps, escaping exceptions and divergence.

Unlike `Behaviour/Refinement/SimConv*` and `Compile/**/Sim*`, which relate two
*different* languages, both sides here are Core 3.0 under the same profile and
host.
-/

namespace Silmaril.Wasm.Execution.Core.Sim

open Silmaril.Wasm.Numerics (Profile)

variable {H : Type}

/-- A stuttering forward simulation of `Step P host` with itself over `Rel`, with
result transport. -/
structure ConfigSim (P : Profile) (host : HostSemantics H) (Rel : Config H → Config H → Prop)
    where
  /-- The one-step obligation, with a stuttering measure. -/
  toForwardSim : ForwardSim (Step P host) (Step P host) Rel
  /-- A terminal left configuration is matched by a right run to the same result. -/
  terminal : ∀ {c d : Config H} {r : Result}, Rel c d → c.code = r.toAdmin →
    ∃ d', Steps P host d d' ∧ d'.code = r.toAdmin

namespace ConfigSim

variable {P : Profile} {host : HostSemantics H} {Rel : Config H → Config H → Prop}

/-- **Behaviour refinement.** Related configurations: every behaviour of the left
one (result, trap, escaping exception or divergence) is a behaviour of the right. -/
theorem behavioursOf_subset (sim : ConfigSim P host Rel) {c d : Config H} (h : Rel c d) :
    behavioursOf P host c ⊆ behavioursOf P host d := by
  rintro b (⟨c', r, hs, hfin, rfl⟩ | ⟨rfl, hdiv⟩)
  · obtain ⟨d', hd, hr'⟩ := sim.toForwardSim.steps hs h
    obtain ⟨d'', hd', hfin'⟩ := sim.terminal hr' hfin
    exact Or.inl ⟨d'', r, hd.trans hd', hfin', rfl⟩
  · exact Or.inr ⟨rfl, sim.toForwardSim.diverges hdiv h⟩

/-- **Behavioural equivalence** from simulations in both directions. -/
theorem behavioursOf_eq (sim : ConfigSim P host Rel)
    (sim' : ConfigSim P host (fun c d => Rel d c)) {c d : Config H} (h : Rel c d) :
    behavioursOf P host c = behavioursOf P host d :=
  Set.Subset.antisymm (sim.behavioursOf_subset h) (sim'.behavioursOf_subset h)

end ConfigSim

end Silmaril.Wasm.Execution.Core.Sim
