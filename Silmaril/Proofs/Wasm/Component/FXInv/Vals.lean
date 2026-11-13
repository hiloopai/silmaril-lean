module

public import Silmaril.Proofs.Wasm.Component.FXInv.Erase

/-!
# Inversion of `StepFX`: value sequences take no step

* `stepFX_not_allVals`: the Core erasure of the left-hand side of any `StepFX` step (any host,
  any FX table) is not a sequence of values. By induction on the step: the `core` rule is a Core
  step (`SingleThreaded.Step.not_quiet`), the `seq` rule reduces to its premise, and every other
  rule has a non-value (an erased FX instruction, a label, frame or handler frame, a trap, a
  branch, `return`, `throw_ref` or a call) in its left-hand side.
* `cvals_injective`: FX value sequences determine their values.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.FXInv

open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Models.FX (AdminFX StepFX ConfigFX cvals)
open Silmaril.Wasm.Component.FXInv
open Silmaril.Wasm.Numerics (Profile)

/-- All elements of a Core code are values. -/
def AllVals (l : List Admin) : Prop := l.all (fun a => a.val?.isSome) = true

theorem allVals_vals (vs : List Execution.Core.Val) : AllVals (vals vs) := by
  simp [AllVals, vals]

theorem allVals_append {l₁ l₂ : List Admin} : AllVals (l₁ ++ l₂) ↔ AllVals l₁ ∧ AllVals l₂ := by
  simp [AllVals, List.all_append]

theorem vals_of_allVals {l : List Admin} (h : AllVals l) : ∃ vs, l = vals vs := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons a as ih =>
    have h' : (a.val?.isSome = true) ∧ AllVals as := by
      simpa only [AllVals, List.all_cons, Bool.and_eq_true] using h
    obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h'.1
    obtain ⟨vs, rfl⟩ := ih h'.2
    exact ⟨v :: vs, by rw [Admin.eq_toAdmin_of_val? hv]; rfl⟩

/-- **Value sequences take no `StepFX` step.** -/
theorem stepFX_not_allVals {P : Profile} {H : Type} {host : HostSemantics H}
    {fx : H → Option Silmaril.Wasm.Models.FX.FuncFX} {c c' : ConfigFX H}
    (hs : StepFX P host fx c c') : ¬ AllVals (eraseL c.code) := by
  induction hs with
  | core h =>
    intro hv
    obtain ⟨vs, hvs⟩ := vals_of_allVals (by simpa using hv)
    exact Silmaril.Wasm.SingleThreaded.Step.not_quiet h
      (by rw [hvs]; exact Silmaril.Wasm.SingleThreaded.quiet_vals vs)
  | seq _ _ ih =>
    intro hv
    exact ih (allVals_append.mp (allVals_append.mp (by simpa using hv)).1).2
  | @invoke _ _ _ _ _ a _ _ _ hc =>
    have hv : (Admin.ref (.func a)).val? = some (.ref (.func a)) := rfl
    simp [AllVals, eraseA, List.all_append, Admin.val?_of_IsCallRef hc, hv]
  | _ => simp [AllVals, eraseA, Admin.val?, constI32, Val.toAdmin, List.all_append, vals]

theorem cvals_injective {vs ws : List Execution.Core.Val} (h : cvals vs = cvals ws) : vs = ws :=
  Silmaril.Wasm.SingleThreaded.vals_injective (by simpa using congrArg eraseL h)

end Silmaril.Proofs.Wasm.Component.FXInv
