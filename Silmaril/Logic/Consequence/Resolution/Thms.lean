module

public import Silmaril.Logic.Consequence.Resolution.Defs
public import Silmaril.Logic.Consequence.Derivation.Thms
import Silmaril.Proofs.Logic.Consequence.Resolution

/-!
# Propositional clause reasoning: soundness and refutations

* `locallySound`: every step preserves clause truth under every valuation of atoms (its computed
  conclusion holds, and the stated conclusion contains it).
* `derives_soundFor`: derivable clauses hold in every valuation satisfying the assumptions.
* `refutes`: **deriving the empty clause** from assumption clauses shows that no valuation satisfies
  them all; `refutes_units` for assumptions that are unit clauses (asserted formulas).
-/

@[expose] public section

namespace Silmaril.Consequence.Resolution

open Silmaril.Logic.Smt (SE)

/-- **Every step preserves truth.** -/
theorem locallySound : system.LocallySound ClauseHolds := by
  rintro v r ps c ⟨d, hd, hsub⟩ hps
  obtain ⟨t, ht, hv⟩ := Proofs.Logic.Consequence.Resolution.apply_sound v r ps d hd hps
  exact ⟨t, hsub t ht, hv⟩

/-- **Soundness** for clause truth under valuations of atoms. -/
theorem derives_soundFor : system.derives.SoundFor (listSat (SE → Prop) ClauseHolds) :=
  DerivationSystem.derives_soundFor locallySound

/-- **A refutation**: the empty clause, derived from `Γ`, shows `Γ` unsatisfiable. -/
theorem refutes {Γ : List Clause} (h : system.derives Γ []) :
    ¬ ∃ v : SE → Prop, ∀ c ∈ Γ, ClauseHolds v c := fun ⟨v, hv⟩ => by
  obtain ⟨t, ht, _⟩ := derives_soundFor Γ [] h v hv
  cases ht

/-- **A refutation of asserted formulas**: no valuation makes them all true. -/
theorem refutes_units {φs : List SE} (h : system.derives (φs.map ([·])) []) :
    ¬ ∃ v : SE → Prop, ∀ φ ∈ φs, Holds v φ := fun ⟨v, hv⟩ =>
  refutes h ⟨v, fun c hc => by
    obtain ⟨φ, hφ, rfl⟩ := List.mem_map.1 hc
    exact ⟨φ, List.mem_singleton_self φ, hv φ hφ⟩⟩

end Silmaril.Consequence.Resolution
