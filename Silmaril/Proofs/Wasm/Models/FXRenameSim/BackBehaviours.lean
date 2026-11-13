module

public import Silmaril.Proofs.Wasm.Models.FXRenameSim.BackStep
public import Silmaril.Proofs.Wasm.Models.FXRenameSim.Behaviours

/-!
# Exception renaming, backward: runs, divergence and behaviours

From `step_rn_back` (`Silmaril.Proofs.Wasm.Models.FXRenameSim.BackStep`):

* `steps_rn_back`: every run of the renamed configuration is the renamed image of a run;
* `diverges_rn_back`: divergence of the renamed configuration gives divergence of the source;
* `result_rn_back`: renamed code is a result exactly when the code is;
* **`behaviours_rn_sup`**: every behaviour of the renamed configuration is a renamed behaviour;
* **`behaviours_rn_eq`**: with `behaviours_rn_sub`, the behaviours of the renamed configuration
  are exactly the renamed behaviours.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXRenameSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Models.FXRename
open Silmaril.Wasm.SingleThreaded.Det (noHost)

variable {H : Type} {P : Profile} {n : Nat}

theorem steps_rn_back {c : Config H} {t : Store H} (h : ExnRen n c.store t) {d : Config H}
    (hs : Steps P noHost (rnCfg n c t) d) :
    ∃ c' t', Steps P noHost c c' ∧ d = rnCfg n c' t' ∧ ExnRen n c'.store t' := by
  induction hs with
  | refl => exact ⟨c, t, .refl, rfl, h⟩
  | tail _ hstep ih =>
    obtain ⟨c₁, t₁, hs₁, rfl, h₁⟩ := ih
    obtain ⟨c₂, t₂, hs₂, rfl, h₂⟩ := step_rn_back hstep h₁ rfl
    exact ⟨c₂, t₂, hs₁.tail hs₂, rfl, h₂⟩

theorem diverges_rn_back {c : Config H} {t : Store H} (h : ExnRen n c.store t)
    (hd : Diverges P noHost (rnCfg n c t)) : Diverges P noHost c := by
  refine Silmaril.InfiniteTrace.coinduct
    (fun c => ∃ t : Store H, ExnRen n c.store t ∧ Diverges P noHost (rnCfg n c t)) ?_ ⟨t, h, hd⟩
  rintro c ⟨t, h, hd⟩
  obtain ⟨d₁, hd₁, hdiv⟩ := hd.unfold
  obtain ⟨c₁, t₁, hs₁, rfl, h₁⟩ := step_rn_back hd₁ h rfl
  exact ⟨c₁, hs₁, t₁, h₁, hdiv⟩

theorem result_rn_back {L : List Admin} {r' : Result} (h : rnAdmins n L = r'.toAdmin) :
    ∃ r, L = r.toAdmin ∧ r' = rnResult n r := by
  cases r' with
  | values vs =>
    obtain ⟨vs₀, rfl, rfl⟩ := rnAdmins_eq_vals_iff.mp h
    exact ⟨.values vs₀, rfl, rfl⟩
  | throw b =>
    obtain ⟨a, rfl, rfl⟩ := rnAdmins_eq_throwing_iff.mp h
    exact ⟨.throw a, rfl, rfl⟩
  | trap =>
    obtain ⟨a₀, L₀, rfl, h₀, h₁⟩ := rnAdmins_eq_cons_iff.mp h
    rw [rnAdmin_eq_trap_iff] at h₀
    rw [rnAdmins_eq_nil_iff'] at h₁
    subst h₀ h₁
    exact ⟨.trap, rfl, rfl⟩

/-- **The backward half of the renaming simulation on behaviours.** -/
theorem behaviours_rn_sup {c : Config H} {t : Store H} (h : ExnRen n c.store t) :
    behavioursOf P noHost (rnCfg n c t) ⊆ rnBeh n '' behavioursOf P noHost c := by
  rintro _ (⟨d, r', hs, hfin, rfl⟩ | ⟨rfl, hdiv⟩)
  · obtain ⟨c', t', hs', rfl, -⟩ := steps_rn_back h hs
    obtain ⟨r, hr, rfl⟩ := result_rn_back hfin
    exact ⟨r.toBehaviour, Or.inl ⟨c', r, hs', hr, rfl⟩, (rnResult_toBehaviour r).symm⟩
  · exact ⟨.diverges, Or.inr ⟨rfl, diverges_rn_back h hdiv⟩, rfl⟩

/-- **The renaming simulation on behaviours.** -/
theorem behaviours_rn_eq {c : Config H} {t : Store H} (h : ExnRen n c.store t) :
    behavioursOf P noHost (rnCfg n c t) = rnBeh n '' behavioursOf P noHost c :=
  Set.Subset.antisymm (behaviours_rn_sup h) (behaviours_rn_sub h)

end Silmaril.Proofs.Wasm.Models.FXRenameSim
