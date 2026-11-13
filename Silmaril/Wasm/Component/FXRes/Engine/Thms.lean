module

public import Silmaril.Wasm.Component.FXRes.Engine.Defs
public import Silmaril.Wasm.Component.FXRes.Thms
public import Silmaril.Proofs.Wasm.Component.FXRes.Engine.Basic

/-!
# One-shot continuations in the threads of the WasmFX component engine (results)

Proofs of the step lemmas in `Silmaril.Proofs.Wasm.Component.FXRes.Engine.Basic`.

* `internalV_kstep`: every internal step of `fxEV P` changes the thread's continuation store by
  a `KStep`; `resumeV_conts`: resumption keeps it;
* `threadRun_ksteps`: every thread run changes it by a `KSteps`;
* **`threadRun_one_shot`**: along every run of a thread of `fxEV P`, each continuation is
  consumed at most once;
* **`threadRun_store_protocol`**: a run from a Core thread (as `invoke` starts every export call)
  has a store history accepted by the handle protocol in both roles.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRes

open Silmaril.Wasm.Resource Silmaril.Wasm.Component.FXEngine Silmaril.Wasm.Component.FXEngineV
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile}

/-- Every thread run changes the thread's store by a `KSteps`. -/
theorem threadRun_ksteps {x y : Silmaril.Wasm.Execution.Core.Store (FXCode H) × ThreadV H}
    (h : ThreadRun P x y) : ∃ evs, KSteps (threadConts x.2) (threadConts y.2) evs := by
  induction h with
  | refl => exact ⟨[], .refl _⟩
  | step hi _ ih =>
    obtain ⟨e₁, h₁⟩ := internalV_kstep hi
    obtain ⟨e₂, h₂⟩ := ih
    exact ⟨_, .cons h₁ h₂⟩
  | @resume s s' t res z _ ih =>
    obtain ⟨e, he⟩ := ih
    have hc : threadConts (resumeV s t res) = threadConts t := resumeV_conts s t res
    exact ⟨e, hc ▸ he⟩

/-- **One-shot continuations in the WasmFX component engine.** -/
theorem threadRun_one_shot {x y : Silmaril.Wasm.Execution.Core.Store (FXCode H) × ThreadV H}
    (h : ThreadRun P x y) :
    ∃ evs, KSteps (threadConts x.2) (threadConts y.2) evs ∧ ∀ k, evs.count (.free k) ≤ 1 := by
  obtain ⟨evs, hs⟩ := threadRun_ksteps h
  exact ⟨evs, hs, ksteps_count_free hs⟩

/-- **The store history of a run from a Core thread respects the handle protocol.** -/
theorem threadRun_store_protocol {s : Silmaril.Wasm.Execution.Core.Store (FXCode H)}
    {t : Silmaril.Wasm.SingleThreaded.Thread}
    {y : Silmaril.Wasm.Execution.Core.Store (FXCode H) × ThreadV H}
    (h : ThreadRun P (s, .core t) y) :
    ∃ evs, KSteps [] (threadConts y.2) evs ∧ ∀ r, (handleProto ℕ r).Accepts evs := by
  obtain ⟨evs, hs⟩ := threadRun_ksteps h
  refine ⟨evs, hs, fun r => ?_⟩
  obtain ⟨L, hL, -⟩ := ksteps_run hs r kRel_nil
  show ((handleProto ℕ r).run (some []) evs).isSome
  rw [hL]
  rfl

end Silmaril.Wasm.Component.FXRes
