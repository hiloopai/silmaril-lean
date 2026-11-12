module

public import Silmaril.Wasm.Auto2.Summ2.Defs
public import Silmaril.Wasm.Auto2.VCEquiv.Thms

/-!
# The front end with the third simplifier and shared loop contracts

`checkEquivV`/`checkRefinesV`: `Silmaril.Wasm.Auto2.Calls.checkEquivC`/`checkRefinesC` (the basic
stages, unrolled loops `equivu`, inlined calls `equivc`), then

* stage `equivv`: the same summaries with the third simplifier
  (`Silmaril.Wasm.Auto2.Summ2.fnCheckV`);
* stage `vcequiv`: a functional contract of the library `Silmaril.Wasm.Auto2.VCEquiv.eqFuns` checks
  both exports (`vcEquivAny`): loops whose trip count depends on the inputs, through invariants.

Each later stage runs only when the earlier ones leave the export unknown. Soundness:
`Silmaril.Wasm.Auto2.Front2.Thms` (`checkEquivV_proved`, `checkEquivV_refuted`,
`modEquiv_of_proveStageV`).

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.Front2

open Silmaril.Wasm
open Silmaril.Wasm.Auto.Front (Report Rel)

/-- Turn a report without a verdict into a proof (stage `st`) when `ok ()` holds (`ok` runs only
then). -/
def upgradeV (r : Report) (st : String) (ok : Unit → Bool) : Report :=
  if r.verdict == .unknown then (if ok () then ⟨.proved, .stage st⟩ else r) else r

/-- Stages `equivv` and `vcequiv` after a report. -/
def laterStages (r : Report) (m₁ m₂ : Module) (j : Nat) : Report :=
  upgradeV (upgradeV r "equivv" fun _ =>
      Silmaril.Wasm.Auto2.Summ2.fnCheckV Silmaril.Wasm.Auto2.Summ.defFuel m₁ m₂ j)
    "vcequiv" fun _ => Silmaril.Wasm.Auto2.VCEquiv.vcEquivAny Silmaril.Wasm.Auto2.VCEquiv.eqFuns m₁ m₂ j

/-- **The front end for equivalence**, with stages `equivv` and `vcequiv`. -/
def checkEquivV (R : Rel) (m₁ m₂ : Module) (j : Nat) (nRand : Nat) (identical : Bool) : Report :=
  laterStages (Silmaril.Wasm.Auto2.Calls.checkEquivC R m₁ m₂ j nRand identical) m₁ m₂ j

/-- **The front end for a refinement**, with stages `equivv` and `vcequiv` (its later stages prove equivalence). -/
def checkRefinesV (R : Rel) (impl spec : Module) (j : Nat) (nRand : Nat) (identical : Bool) :
    Report :=
  laterStages (Silmaril.Wasm.Auto2.Calls.checkRefinesC R impl spec j nRand identical) impl spec j

/-- The proving stages alone. -/
def proveStageV (m₁ m₂ : Module) (j : Nat) : Report :=
  laterStages (Silmaril.Wasm.Auto2.Calls.proveStageC m₁ m₂ j) m₁ m₂ j

end Silmaril.Wasm.Auto2.Front2
