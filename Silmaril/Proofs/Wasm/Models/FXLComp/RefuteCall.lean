module

public import Silmaril.Wasm.FX.Logic.EveryRun.Thms

/-!
# `StepFX'` cannot pass a continuation to a host function

The explainer's static scheduler enqueues continuations with `call $enqueue`, an imported
function of one parameter. In `StepFX'` (`Silmaril.Wasm.Models.FXV`) a call runs through
`ref.func a; call_ref`, and the arguments of a host or FX function are Core values (`invoke`
takes `cvals`). So, with no host calls:

* **`callRef_cont_stuck`**: FX values ending in a continuation reference and then
  `ref.func a`, followed by `call_ref` and any code, have no `StepFX'` step, when `a` is a host
  function that is not an FX function of zero parameters (an FX function of zero parameters
  would be called, leaving the continuation below it).

A Core `call x` of such a function becomes `ref.func a; call_ref` first; this file does not
state that step.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXLComp

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX Silmaril.Wasm.Models.FXV
open Silmaril.Proofs.Wasm.FX.Logic.EveryRun
open Silmaril.Proofs.Wasm.Models.FXVRuns (fval?)
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {fx : H → Option FuncFX}

/-- The `invoke` case: the parameters before `ref.func a` would include the continuation. -/
theorem invoke_cont_absurd {V V₁ : List FVal} {vs : List Val} {k a a' : Nat} {n : Nat}
    (hpos : 0 < n) (hn : vs.length = n)
    (hV : V ++ [.cont k, .val (.ref (.func a))] = V₁ ++ (liftV vs ++ [.val (.ref (.func a'))])) :
    False := by
  have h2 : (V ++ [.cont k]) ++ [.val (.ref (.func a))] =
      (V₁ ++ liftV vs) ++ [.val (.ref (.func a'))] := by simpa using hV
  have h3 : V ++ [.cont k] = V₁ ++ liftV vs := (List.append_inj' h2 rfl).1
  rcases List.eq_nil_or_concat vs with rfl | ⟨vs', w, rfl⟩
  · simp at hn
    omega
  · have h5 : V ++ [.cont k] = (V₁ ++ liftV vs') ++ [.val w] := by
      rw [h3]
      simp [liftV]
    exact absurd (List.append_inj' h5 rfl).2 (by simp)

/-- A step of `vs; call_ref` at the root, below a continuation and a function reference. -/
theorem callRef_cont_root {s : Store H} {K : Silmaril.Wasm.FX.Logic.Conts} {f : Frame}
    {V V₁ V₂ : List FVal} {k a : Nat} {fi : FuncInst H} {hh : H} {c : Admin} {y : ConfigFX H}
    (hc : c.IsCallRef) (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host hh)
    (hfx : ∀ F, fx hh = some F → 0 < F.nparams)
    (hV : V ++ [.cont k, .val (.ref (.func a))] = V₁ ++ V₂)
    (hr : Root P fx s K f V₂ (.core c) y) : False := by
  have hV' : (V ++ [.cont k]) ++ [.val (.ref (.func a))] = V₁ ++ V₂ := by simpa using hV
  cases hr with
  | core h' => exact invoke_core_root hc hf hcode hV' h'
  | dropCont => simp [Admin.IsCallRef] at hc
  | trapSeq => simp [Admin.IsCallRef] at hc
  | throwSeq => simp [Admin.IsCallRef] at hc
  | @invoke _ vs a' fi' hh' F' _ hf' hcode' hfx' hn' =>
    have h2 : (V ++ [.cont k]) ++ [.val (.ref (.func a))] =
        (V₁ ++ liftV vs) ++ [.val (.ref (.func a'))] := by
      rw [hV']
      simp
    have ha : a' = a := by simpa using (List.append_inj' h2 rfl).2.symm
    subst ha
    have hh : hh' = hh := by
      rw [Option.some.inj (hf'.symm.trans hf), hcode] at hcode'
      simpa using hcode'.symm
    subst hh
    exact invoke_cont_absurd (hfx F' hfx') hn' hV

/-- **A continuation cannot be passed to a host function**: `V, ref.cont k, ref.func a;
call_ref; T` has no `StepFX'` step (no host calls), when `a` is a host function that is not an
FX function of zero parameters. -/
theorem callRef_cont_stuck {s : Store H} {K : List (Option ContFX)} {f : Frame} {V : List FVal}
    {k a : Nat} {fi : FuncInst H} {hh : H} {c : Admin} {T : List AdminFX} {y : ConfigFX H}
    (hc : c.IsCallRef) (hf : s.funcs[a]? = some fi) (hcode : fi.code = .host hh)
    (hfx : ∀ F, fx hh = some F → 0 < F.nparams) :
    ¬ StepFX' P noHost fx
      ⟨s, K, f, fvals (V ++ [.cont k, .val (.ref (.func a))]) ++ .core c :: T⟩ y := by
  intro h
  have hcv : fval? (.core c) = none := by
    simp [fval?, Silmaril.Proofs.Wasm.Models.FXLower.IsCallRef.val?_none hc]
  rcases step_split h _ _ T hcv rfl with ⟨V₁, V₂, L₀, hV, hs, -⟩ | ⟨hc', -⟩ | ⟨hc', -⟩
  · obtain ⟨V₃, V₄, y', hV₂, hroot, -⟩ := step_last hs V₂ (.core c) hcv rfl
    refine callRef_cont_root (V := V) (k := k) (V₁ := V₁ ++ V₃) hc hf hcode hfx ?_ hroot
    rw [hV, hV₂, List.append_assoc]
  · cases hc'
    exact hc
  · cases hc'
    exact hc

end Silmaril.Proofs.Wasm.Models.FXLComp
