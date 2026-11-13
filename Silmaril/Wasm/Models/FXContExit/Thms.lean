module

public import Silmaril.Proofs.Wasm.Models.FXContExit.Incl
public import Silmaril.Wasm.Models.FXPresI.Thms

/-!
# The continuation-across-label defect of `StepFX`, repaired by `StepFX'`

`StepFX` (track H) moves only Core values across a label, a frame or a handler frame, so a
continuation reference returned by any of them is stuck (`suspend_to_label_stuck`,
`FXPresI.contExit_frame`, `contExit_handler`, `contExit_label`). The corrected relation `StepFX'`
(`Silmaril.Wasm.Models.FXV`), which the WasmFX components, the suspending engine `fxEV` and the
asyncify results use, passes FX values. This module states that the repair is complete on the
typed fragment of `FXPresI`:

* **`stepFXS_sub_V`**, `stepsFXS_sub_V`: the typed relation `StepFXS` is contained in `StepFX'`
  (so `StepFXS ⊆ StepFXR ⊆ StepFXT ⊆ StepFX'`, and `StepFX ⊆ StepFX'` is `FXV.stepFX_incl`);
* **`progressV`**: a typed configuration of `envP` (`FXPresI.ConfigOk`) is `Final` or has a
  `StepFX'` step: `StepFX'` is never stuck on typed code, while `StepFX` is (the `contExit_*`
  configurations are typed and stuck under `StepFX`);
* **`safetyV`**: along typed (`StepFXS`) runs, which are `StepFX'` runs, every configuration
  reached is `Final` or has a `StepFX'` step;
* **`contExitV_frame`**, **`contExitV_handler`**, **`contExitV_label`**: the three defect
  configurations are typed, stuck under `StepFX`, and step under `StepFX'` to the returned
  continuation;
* `exitV_label`, `exitV_frame`, `exitV_handler`: in general, `StepFX'` returns any FX values
  (continuation references included) from a label, a frame of the right arity and a handler
  frame.

What this does not give: preservation for `StepFX'` itself (its `resume` and `suspend` rules
are untyped, so `StepFX'` has steps that `StepFXS` lacks, `FXPres.stepR_suspend_ambiguous`);
`Final` still contains `resume_throw` of a consumed continuation (`FXPresI.stuck_usedThrow`),
which no FX relation steps. `StepFX` itself is left as it is.

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXContExit

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXResumeT Silmaril.Wasm.Models.FXPres
open Silmaril.Wasm.Models.FXPresI
open Silmaril.Wasm.SingleThreaded.Det (noHost)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {m₀ : ModuleInst} {P : Profile} {host : HostSemantics H}
  {fx : H → Option FuncFX}

/-- **`StepFXS ⊆ StepFX'`.** -/
theorem stepFXS_sub_V {x y : ConfigFX H} (h : StepFXS P host fx x y) : StepFX' P host fx x y :=
  Silmaril.Proofs.Wasm.Models.FXContExit.stepFXS_sub_V h

/-- Runs of `StepFXS` are runs of `StepFX'`. -/
theorem stepsFXS_sub_V {x y : ConfigFX H} (h : StepsFXS P host fx x y) :
    StepsFX' P host fx x y :=
  Silmaril.Proofs.Wasm.Models.FXContExit.stepsFXS_sub_V h

/-- **Progress for `StepFX'` on `envP`**: typed configurations are final or step. -/
theorem progressV {c : ConfigFX H} {Γ : List TypeIdx} {ts : List FTy}
    (hc : ConfigOk (envP m₀) Γ c ts) :
    Final c.store c.conts c.frame c.code ∨ ∃ c', StepFX' P host fx c c' := by
  rcases progressI (P := P) (host := host) (fx := fx) hc with hf | ⟨c', hs⟩
  · exact .inl hf
  · exact .inr ⟨c', stepFXS_sub_V hs⟩

/-- **Safety along typed runs, for `StepFX'`.** -/
theorem safetyV {c c' : ConfigFX H} {Γ : List TypeIdx} {ts : List FTy}
    (hc : ConfigOk (envP m₀) Γ c ts) (h : StepsFXS P host fx c c') :
    StepsFX' P host fx c c' ∧
      (Final c'.store c'.conts c'.frame c'.code ∨ ∃ c'', StepFX' P host fx c' c'') := by
  refine ⟨stepsFXS_sub_V h, ?_⟩
  rcases safetyI hc h with hf | ⟨c'', hs⟩
  · exact .inl hf
  · exact .inr ⟨c'', stepFXS_sub_V hs⟩

/-- `StepFX'` returns FX values from a label. -/
theorem exitV_label (s : Store H) (K : List (Option ContFX)) (f : Frame) (n : Nat)
    (k : List InstrFX) (vs : List FVal) :
    StepFX' P host fx ⟨s, K, f, [.label n k (fvals vs)]⟩ ⟨s, K, f, fvals vs⟩ :=
  .labelVals

/-- `StepFX'` returns FX values from a frame of their arity. -/
theorem exitV_frame (s : Store H) (K : List (Option ContFX)) (f fi : Frame) (vs : List FVal) :
    StepFX' P host fx ⟨s, K, f, [.frame vs.length fi (fvals vs)]⟩ ⟨s, K, f, fvals vs⟩ :=
  .frameVals rfl

/-- `StepFX'` returns FX values from a handler frame. -/
theorem exitV_handler (s : Store H) (K : List (Option ContFX)) (f : Frame) (hs : List HClause)
    (vs : List FVal) :
    StepFX' P host fx ⟨s, K, f, [.handler hs (fvals vs)]⟩ ⟨s, K, f, fvals vs⟩ :=
  .handlerVals

/-- **The frame defect, repaired**: typed, stuck under `StepFX`, a `StepFX'` step. -/
theorem contExitV_frame {s : Store H} {f fi : Frame} {ct : TypeIdx} (hf : f.module = m₀)
    (hm : fi.module = m₀) :
    ConfigOk (envP m₀) [ct] ⟨s, [none], f, [.frame 1 fi [.contRef 0]]⟩ [.cont ct] ∧
      (∀ y, ¬ StepFX P noHost fx ⟨s, [none], f, [.frame 1 fi [.contRef 0]]⟩ y) ∧
      StepFX' P noHost fx ⟨s, [none], f, [.frame 1 fi [.contRef 0]]⟩
        ⟨s, [none], f, [.contRef 0]⟩ := by
  obtain ⟨h1, h2, h3⟩ := contExit_frame (P := P) (fx := fx) (s := s) (ct := ct) hf hm
  exact ⟨h1, h2, stepFXS_sub_V h3⟩

/-- **The handler defect, repaired**: typed, stuck under `StepFX`, a `StepFX'` step. -/
theorem contExitV_handler {s : Store H} {f : Frame} {ct : TypeIdx} (hf : f.module = m₀) :
    ConfigOk (envP m₀) [ct] ⟨s, [none], f, [.handler [] [.contRef 0]]⟩ [.cont ct] ∧
      (∀ y, ¬ StepFX P noHost fx ⟨s, [none], f, [.handler [] [.contRef 0]]⟩ y) ∧
      StepFX' P noHost fx ⟨s, [none], f, [.handler [] [.contRef 0]]⟩
        ⟨s, [none], f, [.contRef 0]⟩ := by
  obtain ⟨h1, h2, h3⟩ := contExit_handler (P := P) (fx := fx) (s := s) (ct := ct) hf
  exact ⟨h1, h2, stepFXS_sub_V h3⟩

/-- **The label defect, repaired**: typed, stuck under `StepFX`, a `StepFX'` step. -/
theorem contExitV_label {s : Store H} {f : Frame} {ct : TypeIdx} (hf : f.module = m₀) :
    ConfigOk (envP m₀) [ct] ⟨s, [none], f, [.label 1 [] [.contRef 0]]⟩ [.cont ct] ∧
      (∀ y, ¬ StepFX P noHost fx ⟨s, [none], f, [.label 1 [] [.contRef 0]]⟩ y) ∧
      StepFX' P noHost fx ⟨s, [none], f, [.label 1 [] [.contRef 0]]⟩
        ⟨s, [none], f, [.contRef 0]⟩ := by
  obtain ⟨h1, h2, h3⟩ := contExit_label (P := P) (fx := fx) (s := s) (ct := ct) hf
  exact ⟨h1, h2, stepFXS_sub_V h3⟩

/-- info: 'Silmaril.Wasm.Models.FXContExit.progressV' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms progressV

/-- info: 'Silmaril.Wasm.Models.FXContExit.contExitV_label' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contExitV_label

end Silmaril.Wasm.Models.FXContExit
