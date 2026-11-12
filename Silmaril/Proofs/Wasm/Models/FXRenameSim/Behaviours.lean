module

public import Silmaril.Proofs.Wasm.Models.FXRenameSim.Step

/-!
# Exception renaming: runs, divergence and behaviours (forward half)

From the one-step simulation `step_rn`:

* `steps_rn`: runs of `c` are matched by runs of the renamed configuration;
* `diverges_rn`: divergence of `c` gives divergence of the renamed configuration;
* **`behaviours_rn_sub`**: every behaviour of `c`, renamed by `rnBeh n`, is a behaviour of the
  renamed configuration over any `ExnRen n c.store` target store.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXRenameSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Models.FXRename
open Silmaril.Wasm.SingleThreaded.Det (noHost)

variable {H : Type} {P : Profile} {n : Nat}

theorem steps_rn {c c' : Config H} (hs : Steps P noHost c c') {t : Store H}
    (h : ExnRen n c.store t) :
    ∃ t', Steps P noHost (rnCfg n c t) (rnCfg n c' t') ∧ ExnRen n c'.store t' := by
  induction hs with
  | refl => exact ⟨t, .refl, h⟩
  | tail _ hstep ih =>
    obtain ⟨t₁, hs₁, h₁⟩ := ih
    obtain ⟨t₂, hs₂, h₂⟩ := step_rn hstep h₁
    exact ⟨t₂, hs₁.tail hs₂, h₂⟩

theorem diverges_rn {c : Config H} (hd : Diverges P noHost c) {t : Store H}
    (h : ExnRen n c.store t) : Diverges P noHost (rnCfg n c t) := by
  refine Silmaril.InfiniteTrace.coinduct
    (fun d => ∃ (c : Config H) (t : Store H), ExnRen n c.store t ∧ Diverges P noHost c ∧
      d = rnCfg n c t) ?_ ⟨c, t, h, hd, rfl⟩
  rintro _ ⟨c, t, h, hd, rfl⟩
  obtain ⟨c₁, hc₁, hd₁⟩ := hd.unfold
  obtain ⟨t₁, hs₁, h₁⟩ := step_rn hc₁ h
  exact ⟨_, hs₁, c₁, t₁, h₁, hd₁, rfl⟩

/-- **The forward half of the renaming simulation on behaviours.** -/
theorem behaviours_rn_sub {c : Config H} {t : Store H} (h : ExnRen n c.store t) :
    rnBeh n '' behavioursOf P noHost c ⊆ behavioursOf P noHost (rnCfg n c t) := by
  rintro _ ⟨b, (⟨c', r, hs, hfin, rfl⟩ | ⟨rfl, hdiv⟩), rfl⟩
  · obtain ⟨t', hs', _⟩ := steps_rn hs h
    refine Or.inl ⟨rnCfg n c' t', rnResult n r, hs', ?_, ?_⟩
    · show rnAdmins n c'.code = _
      rw [hfin, rnAdmins_result]
    · exact (rnResult_toBehaviour r).symm
  · exact Or.inr ⟨rfl, diverges_rn hdiv h⟩

end Silmaril.Proofs.Wasm.Models.FXRenameSim
