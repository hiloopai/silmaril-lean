module

import Silmaril.Wasm.Profiles.Syntax.Components.Thms
import Silmaril.Wasm.Sublanguages.Thms
import Silmaril.Wasm.Component.Reference.Litmus.Thms
import Silmaril.Wasm.Validation.Check.ValidateFinal

open Silmaril.Wasm
open Silmaril.Wasm.Profiles.Syntax
open Silmaril.Wasm.Component.Validation Silmaril.Wasm.Component.IntrinsicWiring
open Silmaril.Wasm.Component.Reference.Litmus

private def sig : Lime1.FuncType := ⟨[.i32, .i32], [.i32]⟩

private def payload : LimeScalar.moduleWitness.Typed () := ⟨sig, {
  exportName := "f"
  fn := {
    resolved := rfl
    locals := []
    body := .step [] (.localGet ⟨0⟩ rfl) <|
      .step [.i32] (.localGet ⟨1⟩ rfl) <|
      .step [] (.intBinOp .i32 .add) (.nil [.i32]) } }⟩

private def wire := Component.Syntax.Component.map (fun _ => payload) adderS.toRef

private def limeTerm :=
  (Closed.lift? .p2 lime1Profile Lime.scalarPayloadInterface wire).get (by decide +kernel)

private def checked := (Lime.componentWitness .p2).checked limeTerm.2.val

example : ValidComponentLime1 .p2 checked.val limeTerm.1 := checked.property

example : checked.val = wire.map Lime.eraseScalarPayload :=
  (Lime.componentWitness_erase limeTerm.2.val).trans (congrArg
    (Component.Syntax.Component.map Lime.eraseScalarPayload) limeTerm.2.property)

example : limeTerm.1.exports[0]?.map Prod.fst = some "add" := by decide +kernel

example : checked.val.map Sublanguages.lime.intoCore.mod = adderS.toRef := by
  rw [show checked.val = limeTerm.2.val.erase.map Lime.eraseScalarPayload from
    Lime.componentWitness_erase limeTerm.2.val, limeTerm.2.property]
  with_unfolding_all rfl

private def coreTerm :=
  (Closed.lift? .p2 core3Profile core3ModuleType? adderS.toRef).get (by decide +kernel)

example : ValidComponentCore3 .p2 adderS.toRef coreTerm.1 :=
  (congrArg (fun raw => ValidComponentCore3 .p2 raw coreTerm.1) coreTerm.2.property).mp
    ((Core.componentWitness .p2).checked coreTerm.2.val).property

private def badModule : Lime1.Module :=
  let valid := LimeScalar.moduleWitness.erase payload
  { valid with funcs := valid.funcs.map fun fn => { fn with body := [] } }

example : (checkLime1? .p2 (adderS.toRef.map (fun _ => badModule))).isOk = true := by decide +kernel

example : (checkCore3? .p2 (adderS.toRef.map (fun _ => badModule.toCore))).isOk = false := by decide +kernel

example : ¬ ValidComponentLime1 .p2 (adderS.toRef.map (fun _ => badModule)) limeTerm.1 := by
  intro checkedBad
  have nativeBad := checkedBad.2 badModule (show badModule ∈ [badModule] from List.Mem.head _)
  have transferred : Silmaril.Wasm.Validation.ModuleValid badModule.toCore :=
    (Profiles.Injections.validLimeToWasm3 ⟨badModule, nativeBad⟩).property
  have rejected : (Silmaril.Wasm.Validation.validate? badModule.toCore).isSome = false := by decide +kernel
  exact Bool.noConfusion (rejected.symm.trans (Silmaril.Wasm.Validation.validate?_isSome_iff.mpr transferred))

example : (Closed.lift? .p2 lime1Profile Lime.scalarPayloadInterface [.component wire]).isSome = false :=
  by decide +kernel

#print axioms Core.componentWitness
#print axioms Lime.scalarWiring_sound
#print axioms Lime.componentWitness
#print axioms Lime.componentWitness_erase
#print axioms checked
