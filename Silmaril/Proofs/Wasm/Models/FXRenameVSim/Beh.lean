module

public import Silmaril.Proofs.Wasm.Models.FXRenameVSim.BackFX

/-!
# Exception renaming for `StepFX'`: runs, divergence and behaviours

From the one-step simulations `stepV_rn` and `stepV_rn_back` (a lock-step bisimulation between
a configuration and its renamed configurations):

* `stepsV_rn`, `divergesV_rn`, `behavioursV_rn_sub`: runs, divergence and behaviours of `c`,
  renamed, are those of the renamed configuration;
* `stepsV_rn_back`, `divergesV_rn_back`, `behavioursV_rn_sup`: and conversely;
* **`behavioursV_rn_eq`**, hence **`exnRenameBisimFX'_holds : Task.exnRenameBisimFX'`**.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXRenameVSim

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXRename
open Silmaril.Wasm.Models.FXRenameV Silmaril.Wasm.Models.FXRenameVSim
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {n : Nat}

theorem stepsV_rn {c c' : ConfigFX H} (hs : StepsFX' P noHost noFX c c') {t : Store H}
    {K₂ : List (Option ContFX)} (h : ExnRen n c.store t) (hK : KRn n c.conts K₂) :
    ∃ t' K₂', StepsFX' P noHost noFX (rnCfgV n c t K₂) (rnCfgV n c' t' K₂') ∧
      ExnRen n c'.store t' ∧ KRn n c'.conts K₂' := by
  induction hs with
  | refl => exact ⟨t, K₂, .refl, h, hK⟩
  | tail _ hstep ih =>
    obtain ⟨t₁, K₁, hs₁, h₁, hK₁⟩ := ih
    obtain ⟨t₂, K₂', hs₂, h₂, hK₂⟩ := stepV_rn hstep h₁ hK₁
    exact ⟨t₂, K₂', hs₁.tail hs₂, h₂, hK₂⟩

theorem divergesV_rn {c : ConfigFX H} (hd : Silmaril.InfiniteTrace (StepFX' P noHost noFX) c)
    {t : Store H} {K₂ : List (Option ContFX)} (h : ExnRen n c.store t) (hK : KRn n c.conts K₂) :
    Silmaril.InfiniteTrace (StepFX' P noHost noFX) (rnCfgV n c t K₂) := by
  refine Silmaril.InfiniteTrace.coinduct
    (fun d => ∃ (c : ConfigFX H) (t : Store H) (K₂ : List (Option ContFX)),
      ExnRen n c.store t ∧ KRn n c.conts K₂ ∧
      Silmaril.InfiniteTrace (StepFX' P noHost noFX) c ∧ d = rnCfgV n c t K₂) ?_
    ⟨c, t, K₂, h, hK, hd, rfl⟩
  rintro _ ⟨c, t, K₂, h, hK, hd, rfl⟩
  obtain ⟨c₁, hc₁, hd₁⟩ := hd.unfold
  obtain ⟨t₁, K₁, hs₁, h₁, hK₁⟩ := stepV_rn hc₁ h hK
  exact ⟨_, hs₁, c₁, t₁, K₁, h₁, hK₁, hd₁, rfl⟩

theorem result_rnV {r : Result} : rnL n (r.toAdmin.map AdminFX.core) =
    (rnResult n r).toAdmin.map AdminFX.core := by
  rw [rnL_map_core', Silmaril.Proofs.Wasm.Models.FXRenameSim.rnAdmins_result]

theorem result_rnV_back {L : List AdminFX} {r' : Result}
    (h : rnL n L = r'.toAdmin.map AdminFX.core) :
    ∃ r, L = r.toAdmin.map AdminFX.core ∧ r' = rnResult n r := by
  obtain ⟨cs, rfl, hcs⟩ := rnL_eq_map_core_iff.mp h
  obtain ⟨r, rfl, rfl⟩ := Silmaril.Proofs.Wasm.Models.FXRenameSim.result_rn_back hcs
  exact ⟨r, rfl, rfl⟩

/-- **The forward half of the renaming simulation on `StepFX'` behaviours.** -/
theorem behavioursV_rn_sub {c : ConfigFX H} {t : Store H} {K₂ : List (Option ContFX)}
    (h : ExnRen n c.store t) (hK : KRn n c.conts K₂) :
    rnBeh n '' behavioursFX' P noHost noFX c ⊆ behavioursFX' P noHost noFX (rnCfgV n c t K₂) := by
  rintro _ ⟨b, (⟨c', r, hs, hfin, rfl⟩ | ⟨rfl, hdiv⟩), rfl⟩
  · obtain ⟨t', K₂', hs', _, _⟩ := stepsV_rn hs h hK
    refine Or.inl ⟨rnCfgV n c' t' K₂', rnResult n r, hs', ?_, ?_⟩
    · show rnL n c'.code = _
      rw [hfin, result_rnV]
    · exact (Silmaril.Proofs.Wasm.Models.FXRenameSim.rnResult_toBehaviour r).symm
  · exact Or.inr ⟨rfl, divergesV_rn hdiv h hK⟩

theorem stepsV_rn_back {c : ConfigFX H} {t : Store H} {K₂ : List (Option ContFX)}
    (h : ExnRen n c.store t) (hK : KRn n c.conts K₂) {d : ConfigFX H}
    (hs : StepsFX' P noHost noFX (rnCfgV n c t K₂) d) :
    ∃ c' t' K₂', StepsFX' P noHost noFX c c' ∧ d = rnCfgV n c' t' K₂' ∧
      ExnRen n c'.store t' ∧ KRn n c'.conts K₂' := by
  induction hs with
  | refl => exact ⟨c, t, K₂, .refl, rfl, h, hK⟩
  | tail _ hstep ih =>
    obtain ⟨c₁, t₁, K₁, hs₁, rfl, h₁, hK₁⟩ := ih
    obtain ⟨c₂, t₂, K₂', hs₂, hd₂, h₂, hK₂⟩ := stepV_rn_back hstep h₁ hK₁ rfl rfl
    exact ⟨c₂, t₂, K₂', hs₁.tail hs₂, hd₂, h₂, hK₂⟩

theorem divergesV_rn_back {c : ConfigFX H} {t : Store H} {K₂ : List (Option ContFX)}
    (h : ExnRen n c.store t) (hK : KRn n c.conts K₂)
    (hd : Silmaril.InfiniteTrace (StepFX' P noHost noFX) (rnCfgV n c t K₂)) :
    Silmaril.InfiniteTrace (StepFX' P noHost noFX) c := by
  refine Silmaril.InfiniteTrace.coinduct
    (fun c => ∃ (t : Store H) (K₂ : List (Option ContFX)), ExnRen n c.store t ∧
      KRn n c.conts K₂ ∧ Silmaril.InfiniteTrace (StepFX' P noHost noFX) (rnCfgV n c t K₂)) ?_
    ⟨t, K₂, h, hK, hd⟩
  rintro c ⟨t, K₂, h, hK, hd⟩
  obtain ⟨d₁, hd₁, hdiv⟩ := hd.unfold
  obtain ⟨c₁, t₁, K₁, hs₁, rfl, h₁, hK₁⟩ := stepV_rn_back hd₁ h hK rfl rfl
  exact ⟨c₁, hs₁, t₁, K₁, h₁, hK₁, hdiv⟩

/-- **The backward half of the renaming simulation on `StepFX'` behaviours.** -/
theorem behavioursV_rn_sup {c : ConfigFX H} {t : Store H} {K₂ : List (Option ContFX)}
    (h : ExnRen n c.store t) (hK : KRn n c.conts K₂) :
    behavioursFX' P noHost noFX (rnCfgV n c t K₂) ⊆ rnBeh n '' behavioursFX' P noHost noFX c := by
  rintro _ (⟨d, r', hs, hfin, rfl⟩ | ⟨rfl, hdiv⟩)
  · obtain ⟨c', t', K₂', hs', rfl, -, -⟩ := stepsV_rn_back h hK hs
    obtain ⟨r, hr, rfl⟩ := result_rnV_back hfin
    exact ⟨r.toBehaviour, Or.inl ⟨c', r, hs', hr, rfl⟩,
      (Silmaril.Proofs.Wasm.Models.FXRenameSim.rnResult_toBehaviour r).symm⟩
  · exact ⟨.diverges, Or.inr ⟨rfl, divergesV_rn_back h hK hdiv⟩, rfl⟩

/-- **The renaming simulation on `StepFX'` behaviours.** -/
theorem behavioursV_rn_eq {c : ConfigFX H} {t : Store H} {K₂ : List (Option ContFX)}
    (h : ExnRen n c.store t) (hK : KRn n c.conts K₂) :
    behavioursFX' P noHost noFX (rnCfgV n c t K₂) = rnBeh n '' behavioursFX' P noHost noFX c :=
  Set.Subset.antisymm (behavioursV_rn_sup h hK) (behavioursV_rn_sub h hK)

/-- **`Task.exnRenameBisimFX'` holds.** -/
theorem exnRenameBisimFX'_holds : Task.exnRenameBisimFX' :=
  fun _ _ _ _ _ _ h hK => behavioursV_rn_eq h hK

end Silmaril.Proofs.Wasm.Models.FXRenameVSim
