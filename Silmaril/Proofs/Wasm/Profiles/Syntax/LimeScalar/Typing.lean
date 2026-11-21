module

public import Silmaril.Wasm.Profiles.Syntax.LimeScalar.Defs

public section

namespace Silmaril.Proofs.Wasm.Profiles.Syntax.LimeScalar

open Silmaril.Wasm.Profiles.Syntax.LimeScalar
open Silmaril.Wasm.Lime1.Validation

theorem instr_sound {context inputs outputs} (term : Instr context inputs outputs) :
    InstrType context term.erase inputs outputs := by
  cases term with
  | intConst width bits => exact .intConst width bits
  | intBinOp width op => exact .intBinOp width op
  | intRelOp width op => exact .intRelOp width op
  | select type => exact .select type
  | localGet index found => exact .localGet index found
  | localSet index found => exact .localSet index found
  | call index found => exact .call index found

theorem body_sound {context inputs outputs} (term : Body context inputs outputs) :
    ExprType context term.erase inputs outputs := by
  induction term with
  | nil stack => exact .nil stack
  | step pre head _ ih => exact .cons (.frame pre (instr_sound head)) ih

theorem module_sound {sig} (term : ClosedModule sig) : ModuleValid term.erase where
  types := fun _ _ => trivial
  imports := by simp [ClosedModule.erase, Wasm.Scalar.Module.ofFunction]
  functions := by
    intro fn member
    have eq : fn = term.fn.erase := List.mem_singleton.mp member
    subst fn
    exact ⟨sig, term.fn.resolved, trivial, body_sound term.fn.body⟩
  tables := by simp [ClosedModule.erase, Wasm.Scalar.Module.ofFunction]
  memories := by simp [ClosedModule.erase, Wasm.Scalar.Module.ofFunction]
  globals := by simp [ClosedModule.erase, Wasm.Scalar.Module.ofFunction]
  elements := by simp [ClosedModule.erase, Wasm.Scalar.Module.ofFunction]
  data := by simp [ClosedModule.erase, Wasm.Scalar.Module.ofFunction]
  start := by simp [StartValid, ClosedModule.erase, Wasm.Scalar.Module.ofFunction]
  exports := by
    intro entry member
    have eq : entry = ⟨term.exportName, .func ⟨0⟩⟩ := List.mem_singleton.mp member
    subst entry
    exact ⟨.func sig, rfl⟩
  uniqueExports := by simp [ClosedModule.erase, Wasm.Scalar.Module.ofFunction]
  singleTable := Nat.zero_le _
  singleMemory := Nat.zero_le _

theorem body_erase_ofWasm1 {context inputs outputs} (term : Wasm.V1.Intrinsic.Scalar.Body context inputs outputs) :
    (Body.ofWasm1 term).erase = Wasm.V1.Expr.toLime term.erase := by
  induction term with
  | nil => rfl
  | step _ head _ ih =>
    have headEq : (Instr.ofWasm1 head).erase = Wasm.V1.Instr.toLime head.erase := by cases head <;> rfl
    simp only [Body.ofWasm1, Body.erase, Wasm.V1.Intrinsic.Scalar.Body.erase, Wasm.V1.Expr.toLime, headEq, ih]

end Silmaril.Proofs.Wasm.Profiles.Syntax.LimeScalar
