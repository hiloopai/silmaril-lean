module

public import Silmaril.Proofs.Wasm.Models.FXL.RefuteCore

/-!
# `StepFX'` cannot store a continuation in a local

The dynamic schedulers of the explainer keep the next thread in a local:
`(local.set $nextk (call $dequeue))`, `(local.set $nextk)` on a continuation. In `StepFX'`
(`Silmaril.Wasm.Models.FXV`) frame locals are Core values and `local.set` is a Core step, which does
not see continuation references. So (no host calls):

* `not_step_localSet_head` (in `Silmaril.Proofs.Wasm.Models.FXL.RefuteCore`): Core `local.set`
  with no operand before it does not step;
* `localSet_head_stuck`: FX code starting with `local.set` does not step;
* **`localSet_cont_stuck`**: FX values ending in a continuation reference, then `local.set`,
  then any code, do not step.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXL

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Proofs.Wasm.Models.FXVRuns
open Silmaril.Proofs.Wasm.Models.FXLower (blockFX_noHost)
open Silmaril.Wasm.SingleThreaded.Det
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {fx : H → Option FuncFX}

/-! ## `StepFX'` -/

/-- The `core` case of `localSet_head_stuck`. -/
theorem localSet_head_core {s s' : Store H} {f f' : Frame} {cs cs' : List Admin}
    {x : LocalIdx} {T : List AdminFX} (h : Step P (blockFX noHost fx) ⟨s, f, cs⟩ ⟨s', f', cs'⟩)
    (hc : cs.map .core = .core (.plain (.localSet x)) :: T) : False := by
  obtain ⟨c, cs₁, hcs, hc1, -⟩ := List.map_eq_cons_iff.mp hc
  have hc1' : c = .plain (.localSet x) := AdminFX.core.inj hc1
  have h' : Step P noHost ⟨s, f, .plain (.localSet x) :: cs₁⟩ ⟨s', f', cs'⟩ := by
    rw [← blockFX_noHost fx, ← hc1', ← hcs]
    exact h
  exact not_step_localSet_head h'

/-- **FX code starting with `local.set` does not step.** -/
theorem localSet_head_stuck {x y : ConfigFX H} (h : StepFX' P noHost fx x y) :
    ∀ i T, x.code ≠ .core (.plain (.localSet i)) :: T := by
  induction h with
  | core h => exact fun i T hc => localSet_head_core h hc
  | seq h' _ ih =>
    intro i T hc
    rcases seq_head rfl hc with hes | ⟨es₁, hes⟩
    · exact no_step_nil' h' hes
    · exact ih i es₁ hes
  | invoke _ => exact fun i T => invoke_ne_head rfl
  | _ => intro i T hx; fnvF_absurd hx

/-- The `core` case of `localSet_cont_stuck`: Core code has no continuation reference. -/
theorem localSet_cont_core {cs : List Admin} {V : List FVal} {k : Nat} {i : LocalIdx}
    {T : List AdminFX}
    (hc : cs.map .core = fvals (V ++ [.cont k]) ++ .core (.plain (.localSet i)) :: T) :
    False := by
  have hm : AdminFX.contRef k ∈ cs.map .core := by
    rw [hc]
    simp [FVal.toAdmin]
  obtain ⟨a, -, ha⟩ := List.mem_map.mp hm
  exact AdminFX.noConfusion ha

/-- A Core value is not `local.set`. -/
theorem val_ne_localSet (v : Val) (i : LocalIdx) :
    AdminFX.core v.toAdmin ≠ .core (.plain (.localSet i)) := by
  intro h
  have h1 : fval? (AdminFX.core v.toAdmin) = fval? (.core (.plain (.localSet i))) := by rw [h]
  have h2 : fval? (FVal.val v).toAdmin = some (.val v) := fval?_toAdmin _
  rw [show (FVal.val v).toAdmin = AdminFX.core v.toAdmin from rfl] at h2
  have h3 : fval? (AdminFX.core (.plain (.localSet i))) = none := rfl
  rw [h2, h3] at h1
  exact absurd h1 (by simp)

/-- The `invoke` case of `localSet_cont_stuck`: the call of an `invoke` is not `local.set`. -/
theorem localSet_cont_invoke {vs : List Val} {a : Nat} {c : Admin} (hc : c.IsCallRef)
    {V : List FVal} {i : LocalIdx} {T : List AdminFX}
    (hx : cvals vs ++ [.core (.ref (.func a)), .core c] =
      fvals V ++ .core (.plain (.localSet i)) :: T) : False := by
  have hm : AdminFX.core (.plain (.localSet i)) ∈
      cvals vs ++ [.core (.ref (.func a)), .core c] := by
    rw [hx]
    exact List.mem_append_right _ List.mem_cons_self
  rcases List.mem_append.mp hm with hv | hv
  · obtain ⟨w, hw, hwe⟩ := List.mem_map.mp hv
    obtain ⟨v, -, rfl⟩ := List.mem_map.mp hw
    exact val_ne_localSet v i hwe
  · rcases List.mem_cons.mp hv with h1 | h1
    · exact AdminFX.noConfusion h1 fun h2 => Admin.noConfusion h2
    · have hc' : c = .plain (.localSet i) := (AdminFX.core.inj (List.mem_singleton.mp h1)).symm
      rw [hc'] at hc
      exact hc

/-- **A continuation reference cannot be stored in a local**: FX values ending in `ref.cont k`,
then `local.set i`, then any code, do not step under `StepFX'`. -/
theorem localSet_cont_stuck {x y : ConfigFX H} (h : StepFX' P noHost fx x y) :
    ∀ V k i T, x.code ≠ fvals (V ++ [.cont k]) ++ .core (.plain (.localSet i)) :: T := by
  induction h with
  | core h => exact fun V k i T hc => localSet_cont_core hc
  | seq h' _ ih =>
    intro V k i T hc
    rcases seq_splitF rfl hc with ⟨U, hU⟩ | ⟨V₂, T₁, hV, hes, -⟩
    · exact absurd hU (no_step_fvals' h' U)
    · have hne : V₂ ≠ [] := fun h0 => localSet_head_stuck h' i T₁ (by rw [hes, h0]; rfl)
      obtain ⟨L, hV₂, -⟩ := suffix_concat hV hne
      exact ih L k i T₁ (by rw [hes, hV₂])
  | invoke hc => exact fun V k i T hx => localSet_cont_invoke hc hx
  | _ => intro V k i T hx; fnvF_absurd hx

end Silmaril.Proofs.Wasm.Models.FXL
