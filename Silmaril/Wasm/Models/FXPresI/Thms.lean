module

public import Silmaril.Proofs.Wasm.Models.FXPresI.Example
public import Silmaril.Proofs.Wasm.Models.FXPresI.Stuck
public import Silmaril.Proofs.Wasm.Models.FXPresI.ContExit

/-!
# An instance of `FXPres.CoreHyp`: statements

* **`coreHypI`**: `envI m₀ ι nt` (Core part `CtI`: integer code, `nop`, `drop`, `unreachable`,
  `trap`, `ref.exn`, `throw_ref`) satisfies `CoreHyp` for every profile, host and FX function
  table.
* **`preservationI`**, **`preservationI_steps`**: so `StepFXS` preservation holds for `envI`
  with no hypothesis.
* **`progressI`**: on `envP m₀` (declared value types read as themselves, `cont.new` at an
  operand type no value has), a typed configuration is `Final` or steps. `Final` includes an
  unhandled `suspend` and `resume_throw` of a consumed continuation: `StepFXS` has no rule for
  the latter (`resume` and `cont.bind` have one, to `trap`).
* **`safetyI`**: every configuration reachable from a typed one is `Final` or steps.
* **`stuck_usedThrow`** (a defect of the models): a typed configuration, final by the
  `usedThrow` case, with no `StepFXS` successor. The WasmFX semantics traps on `resume_throw`
  of a consumed continuation; `StepFXS` (and `StepFX`, `StepFX'`, `StepFXT`, `StepFXR`) has
  no such rule.
* **`contExit_frame`**, **`contExit_handler`**, **`contExit_label`** (the `StepFX` defect
  beyond `suspend_to_label_stuck`): a frame, a handler frame and a label that return a
  continuation are typed configurations of `envP`, stuck under `StepFX`, and step under
  `StepFXS`.
* `configOk_add`, `step_add`: a typed configuration of `envI` with a Core step.
* `naive_val_fails`, `naive_trap_fails`: Silmaril's `AdminsOk`, read directly at value types,
  is not a `CoreHyp` typing (it is not principal on values, and has no `trap` at continuation
  types).

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXPresI

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXResumeT Silmaril.Wasm.Models.FXPres
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {m₀ : ModuleInst} {ι : CValType → FTy} {nt : TypeIdx → FTy}
  {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}

/-- **`envI` satisfies `CoreHyp`.** -/
theorem coreHypI : CoreHyp (envI m₀ ι nt) P host fx :=
  Silmaril.Proofs.Wasm.Models.FXPresI.coreHypI

/-- **Preservation for `StepFXS` on `envI`**, unconditional. -/
theorem preservationI {c c' : ConfigFX H} {Γ : List TypeIdx} {ts : List FTy}
    (h : StepFXS P host fx c c') (hc : ConfigOk (envI m₀ ι nt) Γ c ts) :
    ∃ Γ', Γ <+: Γ' ∧ ExtI c.store c'.store ∧ ConfigOk (envI m₀ ι nt) Γ' c' ts :=
  preservation coreHypI h hc

/-- **Preservation along `StepFXS` runs on `envI`**, unconditional. -/
theorem preservationI_steps {c c' : ConfigFX H} {Γ : List TypeIdx} {ts : List FTy}
    (h : StepsFXS P host fx c c') (hc : ConfigOk (envI m₀ ι nt) Γ c ts) :
    ∃ Γ', Γ <+: Γ' ∧ ExtI c.store c'.store ∧ ConfigOk (envI m₀ ι nt) Γ' c' ts :=
  preservation_steps coreHypI h hc

/-- **Progress for `StepFXS` on `envP`.** -/
theorem progressI {c : ConfigFX H} {Γ : List TypeIdx} {ts : List FTy}
    (hc : ConfigOk (envP m₀) Γ c ts) :
    Final c.store c.conts c.frame c.code ∨ ∃ c', StepFXS P host fx c c' :=
  Silmaril.Proofs.Wasm.Models.FXPresI.progressI hc

/-- **Type safety for `StepFXS` on `envP`**: runs from a typed configuration never get stuck
outside `Final`. -/
theorem safetyI {c c' : ConfigFX H} {Γ : List TypeIdx} {ts : List FTy}
    (hc : ConfigOk (envP m₀) Γ c ts) (h : StepsFXS P host fx c c') :
    Final c'.store c'.conts c'.frame c'.code ∨ ∃ c'', StepFXS P host fx c' c'' := by
  obtain ⟨Γ', -, -, hc'⟩ := preservationI_steps (m₀ := m₀) (ι := FTy.val) (nt := ntP) h hc
  exact progressI hc'

/-- **`resume_throw` of a consumed continuation is stuck** (no rule in `StepFXS`). -/
theorem stuck_usedThrow {s : Store H} {f : Frame} {ct : TypeIdx} {x : TagIdx}
    {ps rs tr : List CValType} {ta : Nat} {ti : TagInst} (hf : f.module = m₀)
    (hct : contType? m₀ ct = some (ps, rs)) (hx : m₀.tags[x.toNat]? = some ta)
    (ht : s.tags[ta]? = some ti) (htt : ti.type.funcType? = some ([], tr)) :
    ConfigOk (envP m₀) [ct] ⟨s, [none], f, Silmaril.Proofs.Wasm.Models.FXPresI.usedThrowCode ct x⟩
        (vtys rs) ∧
      Final s [none] f (Silmaril.Proofs.Wasm.Models.FXPresI.usedThrowCode ct x) ∧
      ¬ ∃ c', StepFXS P host fx
        ⟨s, [none], f, Silmaril.Proofs.Wasm.Models.FXPresI.usedThrowCode ct x⟩ c' :=
  Silmaril.Proofs.Wasm.Models.FXPresI.stuck_usedThrow hf hct hx ht htt

open Silmaril.Wasm.SingleThreaded.Det (noHost) in
/-- **`StepFX` cannot return a continuation from a frame**; `StepFXS` can. -/
theorem contExit_frame {s : Store H} {f fi : Frame} {ct : TypeIdx} (hf : f.module = m₀)
    (hm : fi.module = m₀) :
    ConfigOk (envP m₀) [ct] ⟨s, [none], f, [.frame 1 fi [.contRef 0]]⟩ [.cont ct] ∧
      (∀ y, ¬ StepFX P noHost fx ⟨s, [none], f, [.frame 1 fi [.contRef 0]]⟩ y) ∧
      StepFXS P noHost fx ⟨s, [none], f, [.frame 1 fi [.contRef 0]]⟩
        ⟨s, [none], f, [.contRef 0]⟩ :=
  Silmaril.Proofs.Wasm.Models.FXPresI.contExit_frame hf hm

open Silmaril.Wasm.SingleThreaded.Det (noHost) in
/-- **`StepFX` cannot return a continuation from a handler frame**; `StepFXS` can. -/
theorem contExit_handler {s : Store H} {f : Frame} {ct : TypeIdx} (hf : f.module = m₀) :
    ConfigOk (envP m₀) [ct] ⟨s, [none], f, [.handler [] [.contRef 0]]⟩ [.cont ct] ∧
      (∀ y, ¬ StepFX P noHost fx ⟨s, [none], f, [.handler [] [.contRef 0]]⟩ y) ∧
      StepFXS P noHost fx ⟨s, [none], f, [.handler [] [.contRef 0]]⟩
        ⟨s, [none], f, [.contRef 0]⟩ :=
  Silmaril.Proofs.Wasm.Models.FXPresI.contExit_handler hf

open Silmaril.Wasm.SingleThreaded.Det (noHost) in
/-- **`StepFX` cannot return a continuation from a label**; `StepFXS` can. -/
theorem contExit_label {s : Store H} {f : Frame} {ct : TypeIdx} (hf : f.module = m₀) :
    ConfigOk (envP m₀) [ct] ⟨s, [none], f, [.label 1 [] [.contRef 0]]⟩ [.cont ct] ∧
      (∀ y, ¬ StepFX P noHost fx ⟨s, [none], f, [.label 1 [] [.contRef 0]]⟩ y) ∧
      StepFXS P noHost fx ⟨s, [none], f, [.label 1 [] [.contRef 0]]⟩
        ⟨s, [none], f, [.contRef 0]⟩ :=
  Silmaril.Proofs.Wasm.Models.FXPresI.contExit_label hf

/-- A typed configuration of `envI`. -/
theorem configOk_add {s : Store H} {f : Frame} (hf : f.module = m₀) :
    ConfigOk (envI m₀ ι nt) [] ⟨s, [], f, Silmaril.Proofs.Wasm.Models.FXPresI.addCode.map .core⟩
      [intTy .i32] :=
  Silmaril.Proofs.Wasm.Models.FXPresI.configOk_add hf

/-- It steps. -/
theorem step_add {s : Store H} {f : Frame} :
    StepFXS P host fx ⟨s, [], f, Silmaril.Proofs.Wasm.Models.FXPresI.addCode.map .core⟩
      ⟨s, [], f, [Admin.plain (.intConst .i32 3)].map .core⟩ :=
  Silmaril.Proofs.Wasm.Models.FXPresI.step_add

/-- **Silmaril's `AdminsOk`, read at value types, is not principal on values.** -/
theorem naive_val_fails (C : Context) (s : Store H) :
    Silmaril.Proofs.Wasm.Models.FXPresI.ctNaive C s (Val.i32 0).toAdmin [intTy .i32]
      [intTy .i32, intTy .i32] :=
  Silmaril.Proofs.Wasm.Models.FXPresI.naive_val_fails C s

/-- **Silmaril's `AdminsOk`, read at value types, has no `trap` at a continuation type.** -/
theorem naive_trap_fails (C : Context) (s : Store H) (ct : TypeIdx) :
    ¬ Silmaril.Proofs.Wasm.Models.FXPresI.ctNaive C s .trap [.cont ct] [] :=
  Silmaril.Proofs.Wasm.Models.FXPresI.naive_trap_fails C s ct

/-- info: 'Silmaril.Wasm.Models.FXPresI.preservationI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms preservationI

/-- info: 'Silmaril.Wasm.Models.FXPresI.preservationI_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms preservationI_steps

/-- info: 'Silmaril.Wasm.Models.FXPresI.progressI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms progressI

/-- info: 'Silmaril.Wasm.Models.FXPresI.stuck_usedThrow' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms stuck_usedThrow

/-- info: 'Silmaril.Wasm.Models.FXPresI.contExit_frame' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms contExit_frame

/-- info: 'Silmaril.Wasm.Models.FXPresI.safetyI' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms safetyI

end Silmaril.Wasm.Models.FXPresI
