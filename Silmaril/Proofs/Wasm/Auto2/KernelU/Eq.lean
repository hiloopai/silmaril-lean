module

public import Silmaril.Wasm.Auto2.KernelU.Defs
public import Silmaril.Wasm.Auto2.Kernel.Thms

/-!
# The chunk checks of the function summaries over `instK?` are the specification ones

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto2.KernelU

open Silmaril.Wasm Silmaril.Wasm.Validation
open Silmaril.Wasm.Auto2.KernelU
open Silmaril.Proofs.Wasm.Auto2.Kernel (instK?_eq bytesEqL_eq)
open Silmaril.Wasm.Verify (instance?)

theorem sumCheckUK_eq : sumCheckUK = Silmaril.Wasm.Auto2.Summ.sumCheckU := by
  funext A B
  cases A <;> cases B <;> try rfl
  rename_i A B
  simp only [sumCheckUK, Silmaril.Wasm.Auto2.Summ.sumCheckU, bytesEqL_eq]
  congr 4
  simp [ByteArray.ext_iff, Array.toList_inj]

/-- **The `equivu` chunk check of a certificate over `instK?`.** -/
theorem checkAmongU_eq_K {m₁ m₂ : Module} (h₁ : (validate? m₁).isSome = true)
    (h₂ : (validate? m₂).isSome = true) (fuel : Nat) (js : List Nat) :
    Silmaril.Wasm.Auto2.Summ.checkAmongU fuel m₁ m₂ js = checkAmongUK fuel m₁ m₂ js := by
  unfold Silmaril.Wasm.Auto2.Summ.checkAmongU checkAmongUK
  rw [instK?_eq h₁, instK?_eq h₂, sumCheckUK_eq]
  cases instance? m₁ <;> cases instance? m₂ <;> rfl

/-- **The `equivc` chunk check of a certificate over `instK?`.** -/
theorem checkAmongC_eq_K {m₁ m₂ : Module} (h₁ : (validate? m₁).isSome = true)
    (h₂ : (validate? m₂).isSome = true) (fuel : Nat) (js : List Nat) :
    Silmaril.Wasm.Auto2.Calls.checkAmongC fuel m₁ m₂ js = checkAmongCK fuel m₁ m₂ js := by
  unfold Silmaril.Wasm.Auto2.Calls.checkAmongC checkAmongCK
  rw [instK?_eq h₁, instK?_eq h₂, sumCheckUK_eq]
  cases instance? m₁ <;> cases instance? m₂ <;> rfl

end Silmaril.Proofs.Wasm.Auto2.KernelU
