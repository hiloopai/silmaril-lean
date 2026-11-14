module

public import Silmaril.Servers.Context.Defs

/-!
# Proofs: what contextual equivalence does not give

Three small languages over `Bool`: in the first, no context observes anything, so all
components are equivalent, while a projection reads the component itself; in the second, the
class has only the silent context and the reading uses the other one; in the third, the reading
uses the silent context while another context tells the components apart.
-/

@[expose] public section

namespace Silmaril.Proofs.Servers.Context

open Silmaril.Servers Silmaril.Servers.Observe Silmaril.Servers.Hosts Silmaril.Servers.Context

/-- Contexts `true` observe the component; the context `false` observes nothing. -/
def boolLang : Lang := ⟨Bool, Bool, Bool, fun K c => if K then {c} else ∅⟩

/-- The behaviour that fails to initialize, or none. -/
def flag (A : Sig) (b : Bool) : Beh A := if b then {Obs.initFail} else ∅

theorem flag_ne (A : Sig) : flag A true ≠ flag A false := by
  intro h
  have : Obs.initFail ∈ flag A false := h ▸ (Set.mem_singleton _ : Obs.initFail ∈ ({Obs.initFail} : Set (Obs A)))
  simp [flag] at this

theorem not_projection (A : Sig) :
    ∃ (L : Lang) (c₁ c₂ : L.Comp) (π : L.Comp → Beh A), CtxEquiv c₁ c₂ ∧ π c₁ ≠ π c₂ :=
  ⟨⟨Bool, Unit, Unit, fun _ _ => ∅⟩, true, false, flag A, fun _ _ => rfl, flag_ne A⟩

/-- The reading that fails to initialize when the observations contain `true`. -/
def seesTrue (A : Sig) (S : Set Bool) : Beh A := {o | o = Obs.initFail ∧ true ∈ S}

theorem not_outside (A : Sig) :
    ∃ (L : Lang) (Ks : Set L.Ctx) (ρ : Reading L Unit A) (c₁ c₂ : L.Comp),
      CtxEquivOn Ks c₁ c₂ ∧ ¬ EquivAt Set.univ (ρ.beh c₁) (ρ.beh c₂) := by
  refine ⟨boolLang, {false}, ⟨fun _ => true, seesTrue A⟩, true, false, ?_, ?_⟩
  · rintro K rfl; rfl
  · intro h
    have hm : (Obs.initFail : Obs A) ∈ seesTrue A (boolLang.run true true) := ⟨rfl, by simp [boolLang]⟩
    have h1 := h () trivial
    simp only [Reading.beh] at h1
    rw [h1] at hm
    simp [seesTrue, boolLang] at hm

theorem not_reflects (A : Sig) :
    ∃ (L : Lang) (ρ : Reading L Unit A) (c₁ c₂ : L.Comp),
      EquivAt Set.univ (ρ.beh c₁) (ρ.beh c₂) ∧ ¬ CtxEquiv c₁ c₂ := by
  refine ⟨boolLang, ⟨fun _ => false, seesTrue A⟩, true, false, fun _ _ => rfl, fun h => ?_⟩
  have := h true trivial
  simp [boolLang] at this

end Silmaril.Proofs.Servers.Context
