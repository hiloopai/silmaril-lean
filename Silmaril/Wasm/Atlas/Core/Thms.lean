module

public import Silmaril.Wasm.Atlas.Thms
public import Silmaril.Wasm.Atlas.Core.Defs

/-!
# The Core chart: the profile family

`behaviours_mono`: under profile refinement (`StepLE P' P H`) every behaviour at `P'` is a
behaviour at `P` (finite runs and infinite runs both transfer). Hence the inclusion transitions
of the profile family, `P' → P`:

* `profileUniv h`: reflects universal sentences (a safety property proved at the loose profile
  `P` holds at every refinement `P'`, e.g. a deterministic profile);
* `profileExist h`: preserves existential sentences (a witness at `P'` is a witness at `P`).
-/

@[expose] public section

namespace Silmaril.Wasm.Atlas.Core

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

variable {P' P : Profile} {H : Type}

/-- **Profile refinement shrinks behaviours.** -/
theorem behaviours_mono (h : StepLE P' P H) (host : HostSemantics H) (s : Store H) (a : Nat)
    (vs : List Val) : behaviours P' host s a vs ⊆ behaviours P host s a vs := by
  rintro b (⟨c', r, hs, hc, rfl⟩ | ⟨rfl, ⟨tr, h0, ht⟩⟩)
  · exact Or.inl ⟨c', r, Relation.ReflTransGen.mono (fun x y => h host x y) _ _ hs, hc, rfl⟩
  · exact Or.inr ⟨rfl, tr, h0, fun n => h host _ _ (ht n)⟩

/-- **Profile family, universal sentences**: the inclusion `P' → P` reflects them. -/
def profileUniv (h : StepLE P' P H) : Transition (chart P' H) (chart P H) :=
  BTrans.ofSubsetUniv id id (fun _ _ => trivial)
    (fun x _ c => behaviours_mono h x.2 x.1 c.1 c.2)

/-- **Profile family, existential sentences**: the inclusion `P' → P` preserves them. -/
def profileExist (h : StepLE P' P H) : Transition (chart P' H) (chart P H) :=
  BTrans.ofSubsetExist id id (fun _ _ => trivial)
    (fun x _ c => behaviours_mono h x.2 x.1 c.1 c.2)

/-- A universal sentence proved at the loose profile `P` holds at every refinement `P'`. -/
theorem sat_of_profile (h : StepLE P' P H) (x : Pt H) {s : BSen Call (Behaviour Val)}
    (hs : s.Universal) (hP : (chart P H).Sat x s) : (chart P' H).Sat x s :=
  (profileUniv h).reflect rfl trivial hs ((BSen.sat_rename id _ s).2 hP)

theorem stepLE_refl (P : Profile) (H : Type) : StepLE P P H := fun _ _ _ h => h

theorem StepLE.trans {P'' : Profile} (h₁ : StepLE P'' P' H) (h₂ : StepLE P' P H) :
    StepLE P'' P H := fun host c c' hs => h₂ host c c' (h₁ host c c' hs)

end Silmaril.Wasm.Atlas.Core
