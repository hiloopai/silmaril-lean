module

public import Silmaril.X86.Concurrency.Cir.Tv.CSpawnReview.Defs

/-!
# Spawn/join: kernel checks and proofs

`decide +kernel` for the mutants, the SB
checks and the `swHb` witness; `CtlOk` and `ThreadsOk` for `esJoin` by case analysis.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.TvCSpawnReview

open Silmaril.X86.Concurrency.Cir Silmaril.X86.Concurrency.Cir.Tv.CSpawnReview

set_option maxRecDepth 100000

theorem mutants_ok : mutants.all CMutant.ok = true := by decide +kernel

theorem sbKids_check : sbKids.check = true := by decide +kernel

theorem sbKidsJoin_check : sbKidsJoin.check = true := by decide +kernel

theorem swEx_swHb : swEx.swHb ⟨0, by decide⟩ ⟨3, by decide⟩ = true := by decide +kernel

theorem esJoin_ctlOk : CtlOk esJoin 1 := by
  intro i l hi k e hk hc
  obtain ⟨a, n, hf, h1, h2⟩ := hc
  simp only [esJoin] at hi
  rcases i with _ | _ | i <;> simp at hi <;> subst hi <;>
    rcases k with _ | _ | _ | k <;> simp at hk <;> subst hk <;>
    simp [evFoot] at hf <;> obtain ⟨rfl, rfl⟩ := hf <;> simp [endAddr, ctlAddr] at h1 h2 ⊢

theorem esJoin_threadsOk : Silmaril.X86.MemoryModel.OpAx.ThreadsOk esJoin := by
  intro i l hi ev hev
  simp only [esJoin] at hi
  rcases i with _ | _ | i <;> simp at hi <;> subst hi <;> simp at hev <;>
    rcases hev with rfl | rfl | rfl <;> rfl

end Silmaril.Proofs.X86.Concurrency.Cir.TvCSpawnReview
