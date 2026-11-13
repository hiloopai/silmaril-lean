module

public import Silmaril.Wasm.Component.FXRes.Engine.Defs
public import Silmaril.Wasm.Component.FXRes.Thms

/-!
# One-shot continuations in the threads of the WasmFX component engine (proofs)

* `internalV_kstep`: an internal step of `fxEV P` changes the thread's store by a `KStep`;
* `resumeV_conts`: resumption keeps it.

New proofs.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRes

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV Silmaril.Wasm.Component.FXEngine
open Silmaril.Wasm.Component.FXEngineV
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile}

theorem internalV_kstep_core {s s' : Store (FXCode H)} {t : SingleThreaded.Thread}
    {y : ThreadV H} (h : InternalV P (s, .core t) (s', y)) :
    ∃ evs, KStep [] (threadConts y) evs := by
  rcases h with ⟨t', hy, -⟩ | ⟨-, K, f, code, hy, hs⟩
  · have hy' : y = .core t' := hy
    rw [hy']
    exact ⟨[], .same _⟩
  · have hy' : y = .fx K f code := hy
    rw [hy']
    exact kstep_of_stepFX' hs

theorem internalV_kstep_fx {s s' : Store (FXCode H)} {K : KStore} {f : Frame}
    {code : List AdminFX} {y : ThreadV H} (h : InternalV P (s, .fx K f code) (s', y)) :
    ∃ evs, KStep K (threadConts y) evs := by
  rcases h with ⟨K', f', code', hy, hs⟩ | ⟨-, E, cs, Ec, a, h', args, -, -, hy⟩
  · have hy' : y = .fx K' f' code' := hy
    rw [hy']
    exact kstep_of_stepFX' hs
  · have hy' : y = .parked K f E Ec h' args := hy
    rw [hy']
    exact ⟨[], .same _⟩

/-- **An internal step of the WasmFX engine changes the thread's store by a `KStep`.** -/
theorem internalV_kstep {x y : Store (FXCode H) × ThreadV H} (h : InternalV P x y) :
    ∃ evs, KStep (threadConts x.2) (threadConts y.2) evs := by
  obtain ⟨s, t⟩ := x
  obtain ⟨s', u⟩ := y
  cases t with
  | core t => exact internalV_kstep_core h
  | fx K f code => exact internalV_kstep_fx h
  | parked => exact h.elim

/-- **Resumption keeps the thread's store.** -/
theorem resumeV_conts (s : Store (FXCode H)) (t : ThreadV H)
    (r : Silmaril.Wasm.Component.Engine.CallResult) : threadConts (resumeV s t r) = threadConts t := by
  cases t <;> rfl

end Silmaril.Wasm.Component.FXRes
