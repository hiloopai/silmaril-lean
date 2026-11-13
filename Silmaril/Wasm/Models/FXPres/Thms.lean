module

public import Silmaril.Proofs.Wasm.Models.FXPres.Pres
public import Silmaril.Proofs.Wasm.Models.FXPres.Incl
public import Silmaril.Proofs.Wasm.Models.FXPres.Example
public import Silmaril.Proofs.Wasm.Models.FXPres.Cover

/-!
# Preservation for typed WasmFX: statements

`StepFXS` (`Defs`) is `StepFXR` with `suspend` and `resume_throw` taking the tag's number of
operands; `TL` types whole FX configurations (labels, frames, handler frames, continuation
references, blocks, `loop`, `if`, `br`, `return`, `cont.new`, `cont.bind`, `resume`,
`resume_throw`, `suspend`); `ContTy`/`KOk` type the continuation store; `CoreHyp` collects what
is assumed of the Core typing.

* **`preservation`**, **`preservation_config`**, **`preservation_steps`**: under `CoreHyp`,
  `StepFXS` steps and runs keep `ConfigOk` (a longer slot typing, an extended store).
* `stepFXS_incl`: `StepFXS ⊆ StepFXR`. **`stepR_suspend_ambiguous`**: under `StepFXR` the
  operands of `suspend` may be split in two ways (the refutation that motivates `StepFXS`).
* `configOk_resume_id`, `stepS_resume_id`: a typed configuration that steps.
* `typedFX_TL`: `TL` covers the straight-line judgement `TypedFX` (value types read as
  themselves, no `cont.new`, `resume` without clauses).

The results are conditional on `CoreHyp` (not a `Task`: it is a list of properties of a Core
type system, and no instance is constructed here).

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXPres

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation Silmaril.Wasm.Models.FX
open Silmaril.Wasm.Models.FXV Silmaril.Wasm.Models.FXResumeT
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {E : TyEnv H} {P : Profile} {host : HostSemantics H}
  {fx : H → Option FuncFX}

/-- **Preservation for `StepFXS`** (conditional on `CoreHyp`). -/
theorem preservation (hyp : CoreHyp E P host fx) {c c' : ConfigFX H} {Γ : List TypeIdx}
    {ts : List FTy} (h : StepFXS P host fx c c') (hc : ConfigOk E Γ c ts) :
    ∃ Γ', Γ <+: Γ' ∧ E.ext c.store c'.store ∧ ConfigOk E Γ' c' ts :=
  Silmaril.Proofs.Wasm.Models.FXPres.preservation_config hyp h hc

/-- **Preservation along runs** (conditional on `CoreHyp`). -/
theorem preservation_steps (hyp : CoreHyp E P host fx) {c c' : ConfigFX H} {Γ : List TypeIdx}
    {ts : List FTy} (h : StepsFXS P host fx c c') (hc : ConfigOk E Γ c ts) :
    ∃ Γ', Γ <+: Γ' ∧ E.ext c.store c'.store ∧ ConfigOk E Γ' c' ts :=
  Silmaril.Proofs.Wasm.Models.FXPres.preservation_steps hyp h hc

/-- `StepFXS ⊆ StepFXR`. -/
theorem stepFXS_incl {x y : ConfigFX H} (h : StepFXS P host fx x y) : StepFXR P host fx x y :=
  Silmaril.Proofs.Wasm.Models.FXPres.stepFXS_incl h

/-- **Under `StepFXR` the split of `suspend` is not unique.** -/
theorem stepR_suspend_ambiguous {s : Store H} {K : List (Option ContFX)} {f : Frame}
    {hs : List HClause} {v : FVal} {x : TagIdx} {ta : Nat} {ti : TagInst} {l : LabelIdx}
    (ht : s.tag? f x = some (ta, ti))
    (hc : hs.find? (fun c => c.tag == ta) = some (.onLabel ta l)) :
    StepFXR P host fx ⟨s, K, f, [.handler hs (fvals [v] ++ [.fx (.suspend x)])]⟩
        ⟨s, K ++ [some ⟨CtxV.hole.plug⟩], f,
          fvals [v] ++ [.contRef K.length, .core (.plain (.br l))]⟩ ∧
      StepFXR P host fx ⟨s, K, f, [.handler hs (fvals [v] ++ [.fx (.suspend x)])]⟩
        ⟨s, K ++ [some ⟨(CtxV.seq [v] .hole []).plug⟩], f,
          [.contRef K.length, .core (.plain (.br l))]⟩ ∧
      (fvals [v] ++ [.contRef K.length, .core (.plain (.br l))] : List AdminFX) ≠
        [.contRef K.length, .core (.plain (.br l))] :=
  Silmaril.Proofs.Wasm.Models.FXPres.stepR_suspend_ambiguous ht hc

/-- A typed configuration. -/
theorem configOk_resume_id {s : Store H} {f : Frame} {ct : TypeIdx} (hf : f.module = E.m₀)
    (hct : contType? E.m₀ ct = some ([], [])) :
    ConfigOk E [ct]
      ⟨s, [some Silmaril.Proofs.Wasm.Models.FXPres.idCont], f, [.contRef 0, .fx (.resume ct [])]⟩
      [] :=
  Silmaril.Proofs.Wasm.Models.FXPres.configOk_resume_id hf hct

/-- It steps under `StepFXS`. -/
theorem stepS_resume_id {s : Store H} {f : Frame} {ct : TypeIdx}
    (hct : contType? f.module ct = some ([], [])) :
    StepFXS P host fx
      ⟨s, [some Silmaril.Proofs.Wasm.Models.FXPres.idCont], f, [.contRef 0, .fx (.resume ct [])]⟩
      ⟨s, [none], f, [.handler [] []]⟩ :=
  Silmaril.Proofs.Wasm.Models.FXPres.stepS_resume_id hct

/-- **`TL` covers `TypedFX`** on code without `cont.new` and with clause-free `resume`. -/
theorem typedFX_TL {s : Store H} {Γ : List TypeIdx} {Ls : List (List FTy)}
    {R : Option (List FTy)} {core : Instr → List CValType → List CValType → Prop}
    (hι : E.ι = FTy.val)
    (hcore : ∀ {i t₁ t₂}, core i t₁ t₂ →
      E.ct s (.plain i) (vtys t₁) (vtys t₂) ∧ ¬ IsCtl (.plain i))
    {is : List InstrFX} {t₁ t₂ : List FTy} (h : TypedFX core E.m₀ is t₁ t₂)
    (hp : Silmaril.Proofs.Wasm.Models.FXPres.PlainFX is) :
    TL E s Γ Ls R (is.map InstrFX.toAdmin) t₁ t₂ :=
  Silmaril.Proofs.Wasm.Models.FXPres.typedFX_TL hι hcore h hp

/-- info: 'Silmaril.Wasm.Models.FXPres.preservation' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms preservation

/-- info: 'Silmaril.Wasm.Models.FXPres.preservation_steps' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms preservation_steps

end Silmaril.Wasm.Models.FXPres
