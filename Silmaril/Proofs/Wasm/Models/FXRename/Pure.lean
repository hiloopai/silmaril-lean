module

public import Silmaril.Proofs.Wasm.Models.FXRename.Below

/-!
# The exception renaming on the store-free reduction families

The first leaves of the renaming simulation (`Silmaril.Wasm.Models.FXRename.Task.exnRenameBisim`):
the parametric, numeric and vector families do not read the store.

* `parametric_rn`: a parametric step of `is` is a parametric step of the renamed code (values
  that are dropped or selected are renamed);
* `numeric_rn`, `vector_rn`: numeric and vector steps only hold numbers and vectors, so the
  renaming fixes both sides.

New proofs. The other families (variables, references, aggregates, tables, memories), the
control rules and the contexts are not done.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Models.FXRename

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Models.FXRename

theorem rnAdmins_singleton (n : Nat) (a : Admin) : rnAdmins n [a] = [rnAdmin n a] := rfl

theorem rnAdmin_constI32 (n : Nat) (c : BitVec 32) : rnAdmin n (constI32 c) = constI32 c := rfl

/-- **Parametric steps commute with the renaming.** -/
theorem parametric_rn (n : Nat) {is is' : List Admin} (h : ParametricStep is is') :
    ParametricStep (rnAdmins n is) (rnAdmins n is') := by
  cases h with
  | unreachable => exact .unreachable
  | nop => exact .nop
  | drop v =>
    simpa only [rnAdmins, rnAdmin_toAdmin, rnAdmin] using ParametricStep.drop (rnVal n v)
  | selectTrue hc =>
    simpa only [rnAdmins, rnAdmin_toAdmin, rnAdmin_constI32, rnAdmin] using
      ParametricStep.selectTrue hc
  | selectFalse v₁ v₂ ts =>
    simpa only [rnAdmins, rnAdmin_toAdmin, rnAdmin_constI32, rnAdmin] using
      ParametricStep.selectFalse (rnVal n v₁) (rnVal n v₂) ts

/-- Code made of plain instructions and the trap is fixed by the renaming. -/
def PlainCode : List Admin → Prop
  | [] => True
  | .plain _ :: rest => PlainCode rest
  | .trap :: rest => PlainCode rest
  | _ :: _ => False

theorem rnAdmins_plain {n : Nat} : ∀ {l : List Admin}, PlainCode l → rnAdmins n l = l
  | [], _ => rfl
  | .plain i :: rest, h => congrArg (Admin.plain i :: ·) (rnAdmins_plain (l := rest) h)
  | .trap :: rest, h => congrArg (Admin.trap :: ·) (rnAdmins_plain (l := rest) h)
  | .label .. :: _, h => h.elim
  | .handler .. :: _, h => h.elim
  | .frame .. :: _, h => h.elim
  | .ref _ :: _, h => h.elim
  | .callRefType _ :: _, h => h.elim
  | .returnCallRefType _ :: _, h => h.elim

@[simp] theorem plainCode_num (v : NumVal) (rest : List Admin) :
    PlainCode ((Val.num v).toAdmin :: rest) = PlainCode rest := by
  obtain ⟨t, b⟩ := v
  cases t <;> rfl

@[simp] theorem plainCode_i32 (b : BitVec 32) (rest : List Admin) :
    PlainCode ((Val.i32 b).toAdmin :: rest) = PlainCode rest := rfl

@[simp] theorem plainCode_plain (i : Instr) (rest : List Admin) :
    PlainCode (.plain i :: rest) = PlainCode rest := rfl

@[simp] theorem plainCode_trap (rest : List Admin) :
    PlainCode (.trap :: rest) = PlainCode rest := rfl

@[simp] theorem plainCode_nil : PlainCode [] = True := rfl

theorem numeric_plain {P : Profile} {is is' : List Admin} (h : NumericStep P is is') :
    PlainCode is ∧ PlainCode is' := by
  cases h <;> simp [constI32]

theorem vector_plain {P : Profile} {is is' : List Admin} (h : VectorStep P is is') :
    PlainCode is ∧ PlainCode is' := by
  cases h <;> simp [constI32]

/-- **Numeric steps are fixed by the renaming.** -/
theorem numeric_rn (n : Nat) {P : Profile} {is is' : List Admin} (h : NumericStep P is is') :
    NumericStep P (rnAdmins n is) (rnAdmins n is') := by
  have hp := numeric_plain h
  rw [rnAdmins_plain hp.1, rnAdmins_plain hp.2]
  exact h

/-- **Vector steps are fixed by the renaming.** -/
theorem vector_rn (n : Nat) {P : Profile} {is is' : List Admin} (h : VectorStep P is is') :
    VectorStep P (rnAdmins n is) (rnAdmins n is') := by
  have hp := vector_plain h
  rw [rnAdmins_plain hp.1, rnAdmins_plain hp.2]
  exact h

end Silmaril.Proofs.Wasm.Models.FXRename
