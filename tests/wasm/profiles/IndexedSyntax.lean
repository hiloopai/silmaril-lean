module

import Silmaril.Wasm.Profiles.Syntax.LimeScalar.Thms
import Silmaril.Wasm.Validation.Intrinsic.Reify
import Silmaril.Wasm.Verify.Kernel.Defs

open Silmaril.Wasm Silmaril.Wasm.Profiles
open Silmaril.Wasm.Profiles.Syntax

private def arithmeticSig : V1.FuncType := ⟨[.i32], [.i32]⟩

private def arithmetic : V1.Intrinsic.Scalar.ClosedModule arithmeticSig where
  exportName := "add7"
  fn := {
    resolved := rfl
    singleResult := Nat.le_refl 1
    locals := []
    body := .step [] (.localGet ⟨0⟩ rfl) <|
      .step [.i32] (.intConst .i32 7) <|
      .step [] (.intBinOp .i32 .add) (.nil [.i32]) }

private def v1Witness : LimeScalar.wasm1ModuleWitness.Typed () := ⟨arithmeticSig, arithmetic⟩
private def limeArithmetic := LimeScalar.fromWasm1Module.typed v1Witness

example : LimeScalar.moduleWitness.checked limeArithmetic =
    wasm1ModuleToLime.checked (LimeScalar.wasm1ModuleWitness.checked v1Witness) :=
  LimeScalar.fromWasm1Module.checked_natural v1Witness

example : LimeScalar.moduleWitness.erasureChecked (LimeScalar.fromWasm1Module.onErasure (Quot.mk _ v1Witness)) =
    wasm1ModuleToLime.checked (LimeScalar.wasm1ModuleWitness.checked v1Witness) :=
  LimeScalar.fromWasm1Module.erasureChecked_natural (Quot.mk _ v1Witness)

example : (Injections.validLimeToWasm3 (LimeScalar.moduleWitness.checked limeArithmetic)).val = arithmetic.toCore :=
  (congrArg Lime1.Module.toCore (LimeScalar.fromWasm1Module.erase_eq v1Witness)).trans arithmetic.lime_toCore_eq

private def v1Context := V1.Intrinsic.Scalar.closedContext arithmeticSig
private def v1Func : (LimeScalar.wasm1FunctionWitness v1Context).Typed arithmeticSig := ⟨⟨0⟩, arithmetic.fn⟩

example : (LimeScalar.functionWitness v1Context.toLime).checked ((LimeScalar.fromWasm1Function v1Context).typed v1Func) =
    (wasm1FunctionToLime v1Context).checked ((LimeScalar.wasm1FunctionWitness v1Context).checked v1Func) :=
  (LimeScalar.fromWasm1Function v1Context).checked_natural v1Func

private def swapSig : Lime1.FuncType := ⟨[.i32, .i64], [.i64, .i32]⟩

private def swap : LimeScalar.ClosedModule swapSig where
  exportName := "swap"
  fn := {
    resolved := rfl
    locals := []
    body := .step [] (.localGet ⟨1⟩ rfl) <|
      .step [.i64] (.localGet ⟨0⟩ rfl) (.nil [.i64, .i32]) }

private def swapTyped : LimeScalar.moduleWitness.SomeTyped := ⟨(), swapSig, swap⟩
private def swapChecked := LimeScalar.moduleWitness.someChecked swapTyped

example : (Lime.moduleSyntax.declaredEquiv.symm swapChecked).val = (swap.erase, ()) := rfl
example : (Lime.moduleSyntax.acceptedEquiv Lime.moduleIndexUnique swapChecked).val = swap.erase := rfl
example : Lime1.Validation.ModuleValid swap.erase := swapChecked.2.property
example : ¬ V1.Validation.FuncTypeValid swapSig := by change ¬ 2 ≤ 1; decide
example : swap.erase.funcs = [⟨⟨0⟩, [], [.localGet ⟨1⟩, .localGet ⟨0⟩]⟩] := rfl

example : True := by
  fail_if_success
    let wrong : LimeScalar.Body (LimeScalar.closedContext swapSig) [] [.i64, .i32] := .nil []
  fail_if_success
    let outOfBounds := LimeScalar.Instr.localGet (context := { locals := [.i32] }) ⟨1⟩ (type := .i32) rfl
  trivial

private def raw := (Injections.validLimeToWasm3 swapChecked.2).val
private def reified := Validation.Intrinsic.Reify.checked raw (by kernel_rfl)
private def coreTerm : Core.moduleWitness.Typed reified.interface := reified.typed
private def coreChecked := Core.moduleWitness.checked coreTerm

example : coreChecked.val = raw := reified.erase_eq
example : (Core.moduleSyntax.acceptedEquiv Core.moduleIndexUnique ⟨reified.interface, coreChecked⟩).val = raw :=
  reified.erase_eq
example : Intrinsic.erasureEquiv Core.moduleLifts reified.interface (Quot.mk _ coreTerm) = coreChecked := rfl
example : (Core.checkedPartsEquiv reified.interface coreChecked).val = raw.split :=
  congrArg Silmaril.Wasm.Module.split reified.erase_eq
example : Core.partsWitness.checked (Core.toPartsWitness.typed coreTerm) = Core.moduleToParts.checked coreChecked :=
  Core.toPartsWitness.checked_natural coreTerm
example : (Core.checkedPartsEquiv reified.interface).symm (Core.moduleToParts.checked coreChecked) = coreChecked :=
  (Core.checkedPartsEquiv reified.interface).left_inv coreChecked

private def strictRaw : Profiles.Module Profiles.Strict := (Profiles.Strict.check? raw).get (by kernel_rfl)
private def strictChecked : Profiles.CheckedModule Profiles.Strict reified.interface :=
  ⟨strictRaw, show Validation.ModuleOk strictRaw.val reified.interface from by
    have exactRaw : strictRaw.val = raw := by kernel_rfl
    exact (congrArg (fun mod => Validation.ModuleOk mod reified.interface)
      (reified.erase_eq.trans exactRaw.symm)).mp coreChecked.property⟩

private def allowMutation := functionalOfLE (FunctionalCore.mutation_le .disabled)

example : ((functionalToCore .mutable .disabled).checked (allowMutation.checked strictChecked)).val = raw := by
  have eq := functional_ofLE_toCore (FunctionalCore.mutation_le .disabled)
  exact (congrArg (fun arrow : (moduleFamily Profiles.Strict).Map Core.moduleSyntax => arrow.raw strictRaw) eq).trans
    (by kernel_rfl)

private def ambiguous : Family := ⟨Unit, Bool, fun _ _ => True⟩
private def checkedFalse : ambiguous.SomeChecked := ⟨false, (), trivial⟩
private def checkedTrue : ambiguous.SomeChecked := ⟨true, (), trivial⟩

example : checkedFalse ≠ checkedTrue := fun equal => Bool.noConfusion (congrArg Sigma.fst equal)
example : ambiguous.forget checkedFalse = ambiguous.forget checkedTrue := rfl

#print axioms Intrinsic.erasureEquiv
#print axioms Intrinsic.Map.erasureChecked_natural
#print axioms Family.acceptedEquiv
#print axioms Core.moduleIndexUnique
#print axioms Core.functionIndexUnique
#print axioms Core.checkedPartsEquiv
#print axioms Core.partsLifts
#print axioms Lime.functionIndexUnique
#print axioms LimeScalar.ClosedModule.sound
#print axioms LimeScalar.fromWasm1Module
#print axioms LimeScalar.fromWasm1Function
#print axioms functional_ofLE_toCore
#print axioms reified
