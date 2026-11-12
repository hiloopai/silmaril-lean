module

public import Silmaril.Wasm.Component.FXTypedEx.Defs
public import Silmaril.Wasm.Component.FXTyped.Thms
import Silmaril.Proofs.Wasm.Component.FXTypedEx.Bad
import Silmaril.Proofs.Wasm.Component.FXTypedEx.SusRun

/-!
# Components with FX functions for `SimpleFX.Typed`

* **`susC`** (code that suspends) and **`mixC`** (a Core export over the adder and an FX export
  that resumes a continuation of it) meet every hypothesis of `FXRefV.refToSpecFX`, including
  `SimpleFX.Typed`, which `FXTyped.typed_of_frag` discharges: `susC_typed`, `mixC_typed`. So
  the machine half holds for them unconditionally (`susC_refToSpec`, `mixC_refToSpec`).
* **`susC` does suspend** (`susC_run`): in the engine instance of its module, the call of `run`
  makes a continuation of `sus`, `sus` suspends, the handler branches out with the continuation,
  the second `resume` runs `sus` to its end and `run` returns no value (16 engine steps,
  following `FXSuspend.run_ex`).
* **`badC`** meets `Good`, `FloatFree`, `Inst` and `Arity`, but its FX function, declared
  `[] → [i32]`, returns an `i64` (`StepFX'` checks only arities): **`bad_not_typed`**. Hence
  `typed_not_general`: `SimpleFX.Typed` does not follow from the other hypotheses. It is a real
  condition on FX code (the model has no validation of FX function bodies), not only a gap in
  the proofs.

Proofs: `Silmaril.Proofs.Wasm.Component.FXTypedEx.{Inst,Bad,SusRun}`. New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXTypedEx

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component.FXEngine Silmaril.Wasm.Component.FXEngineV Silmaril.Wasm.Component.FXRefV
open Silmaril.Wasm.Component.FXTyped
open Silmaril.Wasm.Numerics (Profile)

open Silmaril.Proofs.Wasm.Component.FXTypedEx in
/-- **The suspending component is typed.** -/
theorem susC_typed (P : Profile) : susC.Typed P := typed_of_frag susC_inst susC_good susC_frag

open Silmaril.Proofs.Wasm.Component.FXTypedEx in
/-- **The mixed component is typed.** -/
theorem mixC_typed (P : Profile) : mixC.Typed P := typed_of_frag mixC_inst mixC_good mixC_frag

open Silmaril.Proofs.Wasm.Component.FXTypedEx in
/-- **The machine half for the suspending component**, with no hypothesis. -/
theorem susC_refToSpec (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (x : SimpleExport) (hx : x ∈ susC.exports) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList x.ty.params vs = true) :
    exportBehaviours prof (refHostE (fxEV P)) () (susC.toSimple.toRef.map susC.ofCore) [] x.name
        (vs.map toRefVal) ⊆
      exportSpecE (fxEV P) susC.emb susC.toSimple x vs :=
  refToSpecFX_frag P prof susC susC_good susC_floatFree susC_inst susC_arity susC_frag x hx vs
    hvs

open Silmaril.Proofs.Wasm.Component.FXTypedEx in
/-- **The machine half for the mixed component**, with no hypothesis. -/
theorem mixC_refToSpec (P : Profile) (prof : Silmaril.Wasm.Component.ProfileKind)
    (x : SimpleExport) (hx : x ∈ mixC.exports) (vs : List Silmaril.Wasm.Component.Val)
    (hvs : ValTy.checkList x.ty.params vs = true) :
    exportBehaviours prof (refHostE (fxEV P)) () (mixC.toSimple.toRef.map mixC.ofCore) [] x.name
        (vs.map toRefVal) ⊆
      exportSpecE (fxEV P) mixC.emb mixC.toSimple x vs :=
  refToSpecFX_frag P prof mixC mixC_good mixC_floatFree mixC_inst mixC_arity mixC_frag x hx vs
    hvs

/-- **The suspending component's `run` returns**, through a suspension and a resumption. -/
theorem susC_run (P : Profile) :
    ∃ J, instOf (fxEV P) (susC.emb susC.mod) [] susC.mod.exports = some J ∧
      some [] ∈ engineOut (fxEV P) J 1 [] :=
  ⟨_, Silmaril.Proofs.Wasm.Component.FXTypedEx.susHJ P, Silmaril.Proofs.Wasm.Component.FXTypedEx.run_out P⟩

/-- **The ill-typed component is not `Typed`**, at every profile. -/
theorem bad_not_typed (P : Profile) : ¬ badC.Typed P :=
  Silmaril.Proofs.Wasm.Component.FXTypedEx.bad_not_typed P

/-- **`SimpleFX.Typed` does not follow from the other hypotheses of `refToSpecFX`.** -/
theorem typed_not_general (P : Profile) :
    ¬ ∀ c : SimpleFX, c.toSimple.Good → c.toSimple.FloatFree → c.Inst → c.toSimple.Arity →
      c.Typed P := fun h =>
  bad_not_typed P (h badC Silmaril.Proofs.Wasm.Component.FXTypedEx.badC_good
    Silmaril.Proofs.Wasm.Component.FXTypedEx.badC_floatFree
    Silmaril.Proofs.Wasm.Component.FXTypedEx.badC_inst
    Silmaril.Proofs.Wasm.Component.FXTypedEx.badC_arity)

/-- info: 'Silmaril.Wasm.Component.FXTypedEx.susC_refToSpec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms susC_refToSpec

/-- info: 'Silmaril.Wasm.Component.FXTypedEx.typed_not_general' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms typed_not_general

end Silmaril.Wasm.Component.FXTypedEx
