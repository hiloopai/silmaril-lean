module

public import Silmaril.Wasm.Component.FXEngineV.Defs
public import Silmaril.Wasm.Models.FXV.Thms
public import Silmaril.Wasm.Component.FXInv.Thms

/-!
# Threads of the engine with suspension at values

* `allV_plug`: if a context with FX values plugged with `c` is a list of Core values, so is `c`;
* `internalV_vals`: an FX thread at Core values takes no internal step (no `StepFX'` step, by
  `stepFX'_iff_allCore` and `stepFX_vals`; no parking, since `decompose?` finds no redex in
  values);
* `statusV_vals`, `statusV_vals'`: its status is the values, flattened (that of `fxE P`).

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.FXEngineV

open Silmaril.Wasm.Component.FXEngine Silmaril.Wasm.Component.FXEngineV
open Silmaril.Wasm.Execution.Core (Store Frame Val Admin vals)
open Silmaril.Wasm.Models.FX (AdminFX ContFX cvals)
open Silmaril.Wasm.Models.FXV (StepFX' CtxV FVal fvals)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile}

/-- FX code made of Core values. -/
def AllV (l : List AdminFX) : Prop := ∀ x ∈ l, ∃ v : Val, x = .core v.toAdmin

theorem allV_plug : ∀ (E : CtxV) (c : List AdminFX), AllV (E.plug c) → AllV c
  | .hole, _, h => h
  | .seq vs E rest, c, h => allV_plug E c fun x hx => h x (by
      simp only [CtxV.plug, List.mem_append]
      exact Or.inl (Or.inr hx))
  | .label _ _ _, _, h => by
      obtain ⟨v, hv⟩ := h _ (List.mem_singleton_self _)
      cases hv
  | .frame _ _ _, _, h => by
      obtain ⟨v, hv⟩ := h _ (List.mem_singleton_self _)
      cases hv
  | .handler _ _, _, h => by
      obtain ⟨v, hv⟩ := h _ (List.mem_singleton_self _)
      cases hv

theorem allV_cvals (vs : List Val) : AllV (cvals vs) := by
  intro x hx
  simp only [cvals, vals, List.map_map, List.mem_map, Function.comp] at hx
  obtain ⟨v, -, rfl⟩ := hx
  exact ⟨v, rfl⟩

theorem vals_of_allV : ∀ cs : List Admin, AllV (cs.map .core) → ∃ ws, cs = vals ws
  | [], _ => ⟨[], rfl⟩
  | c :: cs, h => by
      obtain ⟨v, hv⟩ := h _ (List.mem_cons_self ..)
      obtain ⟨ws, hws⟩ := vals_of_allV cs fun x hx => h x (List.mem_cons_of_mem _ hx)
      cases hv
      exact ⟨v :: ws, by rw [hws]; rfl⟩

/-- **An FX thread at values takes no internal step.** -/
theorem internalV_vals (s : Store (FXCode H)) (K : List (Option ContFX)) (f : Frame)
    (vs : List Val) : ¬ ∃ y, InternalV P (s, ThreadV.fx K f (cvals vs)) y := by
  rintro ⟨y, ⟨K', f', code', -, hs⟩ | ⟨-, E, cs, Ec, a, h, args, hc, hd, -⟩⟩
  · have hall : (cvals vs).all Silmaril.Proofs.Wasm.Models.FX.isCore = true :=
      Silmaril.Proofs.Wasm.Models.FX.all_isCore_cvals vs
    exact Silmaril.Wasm.Component.FXInv.stepFX_vals P vs
      ((Silmaril.Wasm.Models.FXV.stepFX'_iff_allCore (x := ⟨s, K, f, cvals vs⟩) hall).mp hs)
  · obtain ⟨ws, rfl⟩ := vals_of_allV cs (allV_plug E _ (hc ▸ allV_cvals vs))
    rw [Silmaril.Wasm.SingleThreaded.decompose?_vals_nil] at hd
    cases hd

/-- **The status of an FX thread at values** is the values, flattened. -/
theorem statusV_vals (s : Store (FXCode H)) (K : List (Option ContFX)) (f : Frame)
    (vs : List Val) :
    statusV P s (.fx K f (cvals vs)) = fxResult (H := H) (cvals vs) :=
  ite_eq_right (internalV_vals s K f vs)

/-- **The status of an FX thread at values**, computed: the values when they are flat. -/
theorem statusV_vals' (s : Store (FXCode H)) (K : List (Option ContFX)) (f : Frame)
    (vs : List Val) :
    statusV P s (.fx K f (cvals vs)) =
      match vs.mapM Silmaril.Wasm.SingleThreaded.toFlat? with
      | some fvs => .returned (.values fvs)
      | none => .stuck :=
  (statusV_vals s K f vs).trans
    ((ite_eq_right (Silmaril.Wasm.Component.FXInv.internalFX_vals P s K f vs)).symm.trans
      (Silmaril.Wasm.Component.FXInv.statusFX_vals P s K f vs))

end Silmaril.Proofs.Wasm.Component.FXEngineV
