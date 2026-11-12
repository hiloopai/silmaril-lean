module

public import Silmaril.Proofs.Wasm.Models.FXV.Core

/-!
# CoreFX with continuation values: relation to `StepFX`

The header of `StepFX'` (`Defs`).

* **`stepFX_incl`**, `stepsFX_incl`, **`behavioursFX_incl`**: every `StepFX` step, run and
  behaviour is one of `StepFX'`;
* **`stepFX'_iff_allCore`**: on code whose instructions are all Core, the two relations have the
  same steps (the only difference, FX values that are continuations, needs a `contRef` in the
  code);
* `stepFX'_conservativeK`: `StepFX'` is conservative over Core with any continuation store;
* **`behavioursFX'_ofCoreK`**: without FX functions, the `StepFX'` behaviours of a Core
  configuration are its Core behaviours.

The relations differ exactly where a continuation reference is a value: `StepFX` is stuck at
the branch that `suspend` leaves for an `(on x l)` clause (`suspend_to_label_stuck` in
`Silmaril.Wasm.Models.FXLower.Thms`), `StepFX'` takes it (`Silmaril.Wasm.Models.FXAbort.Thms`).

New statements.
-/

@[expose] public section

namespace Silmaril.Wasm.Models.FXV

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Models.FX
open Silmaril.Proofs.Wasm.Models.FXLower (ofCoreK)
open Silmaril.Proofs.Wasm.Models.FX (isCore)
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} {P : Profile} {host : HostSemantics H} {fx : H → Option FuncFX}

/-- Core values as FX values. -/
theorem fvals_liftV (vs : List Val) : fvals (liftV vs) = cvals vs :=
  Silmaril.Proofs.Wasm.Models.FXV.fvals_liftV vs

/-- **`StepFX ⊆ StepFX'`.** -/
theorem stepFX_incl {x y : ConfigFX H} (h : StepFX P host fx x y) : StepFX' P host fx x y :=
  Silmaril.Proofs.Wasm.Models.FXV.stepFX_incl h

/-- Runs of `StepFX` are runs of `StepFX'`. -/
theorem stepsFX_incl {x y : ConfigFX H} (h : StepsFX P host fx x y) :
    StepsFX' P host fx x y :=
  Silmaril.Proofs.Wasm.Models.FXV.stepsFX_incl h

/-- **Every `StepFX` behaviour is a `StepFX'` behaviour.** -/
theorem behavioursFX_incl (x : ConfigFX H) :
    behavioursFX P host fx x ⊆ behavioursFX' P host fx x :=
  Silmaril.Proofs.Wasm.Models.FXV.behavioursFX_incl x

/-- **On all-Core code the two relations have the same steps.** -/
theorem stepFX'_iff_allCore {x y : ConfigFX H} (hc : x.code.all isCore = true) :
    StepFX' P host fx x y ↔ StepFX P host fx x y :=
  Silmaril.Proofs.Wasm.Models.FXV.stepFX'_iff_allCore hc

/-- **Conservativity of `StepFX'` with live continuations.** -/
theorem stepFX'_conservativeK {K : List (Option ContFX)} {c : Config H}
    (hno : NoFX fx c.store) {y : ConfigFX H} :
    StepFX' P host fx (ofCoreK K c) y ↔ ∃ c', Step P (blockFX host fx) c c' ∧ y = ofCoreK K c' :=
  Silmaril.Proofs.Wasm.Models.FXV.stepFX'_conservativeK hno

/-- **Behaviours of Core configurations** (no FX functions, any continuation store). -/
theorem behavioursFX'_ofCoreK (K : List (Option ContFX)) (c : Config H) :
    behavioursFX' P host noFX (ofCoreK K c) = behavioursOf P host c :=
  Silmaril.Proofs.Wasm.Models.FXV.behavioursFX'_ofCoreK K c

/-- info: 'Silmaril.Wasm.Models.FXV.behavioursFX_incl' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms behavioursFX_incl

/-- info: 'Silmaril.Wasm.Models.FXV.behavioursFX'_ofCoreK' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms behavioursFX'_ofCoreK

end Silmaril.Wasm.Models.FXV
