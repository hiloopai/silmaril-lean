module

public import Silmaril.Logic.Consequence.HOL.UserSig.Defs
public import Silmaril.Logic.HOLLight.Soundness.Thms
public import Silmaril.Logic.HOLLight.Check.Thms

/-!
# Proofs for HOL over a user signature and theory
-/

@[expose] public section

namespace Silmaril.Proofs.Logic.Consequence.HOL.UserSig

open Silmaril.Logic.HOLLight Silmaril.Consequence Silmaril.Consequence.HOL
open Silmaril.Logic.Institution.Metatheory

universe u

theorem kernelFrom_soundFor (S : HolSig) (Δ : Theory) :
    (kernelFrom S Δ).SoundFor (pointsOf.{u} S Δ) := by
  intro Γ p h x hΓ
  exact h.sound x.1.1 x.2 x.1.2.1 x.1.2.2 fun q hq => by
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 (List.mem_toFinset.1 hq)
    exact hΓ r hr

theorem cModel_models : Models cModel cTheory := by
  intro p hp
  simp only [cTheory, List.mem_singleton] at hp
  subst hp
  intro ρ ν
  exact ⟨_, .const _ (.user (s := ⟨0, .bool⟩) rfl ⟨trivial, trivial⟩ rfl (by simp)), rfl⟩

end Silmaril.Proofs.Logic.Consequence.HOL.UserSig
