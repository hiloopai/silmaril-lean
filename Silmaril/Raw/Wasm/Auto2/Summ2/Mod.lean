module

public import Silmaril.Raw.Wasm.Auto2.Summ2.Simp
public import Silmaril.Wasm.Auto2.Calls.Thms
public import Silmaril.Wasm.Auto2.Kernel.Thms

/-!
# The check : module equivalence and the kernel-cheap form (unrefined)

* `out_of_sumCheckV`: the check gives equal results (as `Silmaril.Wasm.Auto2.Summ.out_of_sumCheckU`,
  with `canon3`);
* **`modEquiv_of_fnCheckV`**, **`modEquiv_of_checkAmongV`**: the check on the summaries with
  unrolled loops and inlined calls proves `ModEquiv` (every reflexive relation, every profile);
* `sumCheckVK_eq`, **`checkAmongV_eq_K`**: over the validation-free instance, given that both
  modules validate.

New proofs (unrefined).
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.Summ2

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Validation
open Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm.Auto.Bridge
open Silmaril.Wasm.Auto2.Summ (guardsOk_of_anyDead guardsOk_keys_eq)
open Silmaril.Wasm.Auto2.Calls (fnSumC? fnSumCI modEquiv_of_outC fnSumC?_of_inst)
open Silmaril.Wasm.Auto.Equiv (Env TypedVals)
open Silmaril.Wasm.Verify (instance?)
open Silmaril.Wasm.Auto.Front (ModEquiv)

variable {P : Profile} {fuel : Nat}

/-- Equal guard keys and simplified results, from the same initial memory. -/
theorem outAt_eqV {ρ : Env} {B0 : ByteArray} {S T : XState}
    (h₁ : (Silmaril.Wasm.Auto2.Summ.keys S.guards).all
      (Silmaril.Wasm.Auto2.Summ.keys T.guards).contains = true)
    (h₂ : (Silmaril.Wasm.Auto2.Summ.keys T.guards).all
      (Silmaril.Wasm.Auto2.Summ.keys S.guards).contains = true)
    (hs : slots3 S.stack = slots3 T.stack) : outAt ρ B0 S = outAt ρ B0 T := by
  have hst : S.stack.map (denX ρ B0) = T.stack.map (denX ρ B0) := by
    rw [← map_denX_slots3, hs, map_denX_slots3]
  simp only [outAt, guardsOk_keys_eq (ρ := ρ) (B0 := B0) h₁ h₂, hst]

/-- **An accepted pair of summaries gives equal results.** -/
theorem out_of_sumCheckV {A B : FnSumX} (h : sumCheckV (some A) (some B) = true) :
    A.params = B.params ∧ ∀ vs, fnOutX A vs = fnOutX B vs := by
  simp only [sumCheckV, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.or_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true] at h
  obtain ⟨⟨hp, hg⟩, hc⟩ := h
  refine ⟨hp, fun vs => ?_⟩
  have hρ : envX A vs = envX B vs := by simp only [envX, hg]
  simp only [fnOutX, hρ]
  rcases hc with ⟨hdA, hdB⟩ | ⟨⟨⟨hm, h₁⟩, h₂⟩, hs⟩
  · simp only [outAt, guardsOk_of_anyDead hdA, guardsOk_of_anyDead hdB]
    rfl
  · rcases hm with hm | hm
    · simp only [Bool.or_eq_false_iff] at hm
      rw [outAt_indep hm.1 _ A.bytes B.bytes]
      exact outAt_eqV h₁ h₂ hs
    · rw [hm]
      exact outAt_eqV h₁ h₂ hs

/-- **The check proves module equivalence**, every profile, every reflexive relation. -/
theorem modEquiv_of_fnCheckV {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b, R b b)
    {m₁ m₂ : Module} {j : Nat} (h : fnCheckV fuel m₁ m₂ j = true) : ModEquiv R P m₁ m₂ j := by
  unfold fnCheckV at h
  cases hA : fnSumC? fuel m₁ j with
  | none => rw [hA] at h; simp [sumCheckV] at h
  | some A =>
    cases hB : fnSumC? fuel m₂ j with
    | none => rw [hA, hB] at h; simp [sumCheckV] at h
    | some B =>
      rw [hA, hB] at h
      obtain ⟨hp, hout⟩ := out_of_sumCheckV h
      exact modEquiv_of_outC hR hA hB hp fun vs _ => hout vs

/-- **Entry `i` of `checkAmongV fuel m₁ m₂ js` proves module equivalence at export `js[i]`**,
every profile. -/
theorem modEquiv_of_checkAmongV {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b, R b b)
    {m₁ m₂ : Module} {js : List Nat} {i j : Nat} (hj : js[i]? = some j)
    (h : (checkAmongV fuel m₁ m₂ js)[i]? = some true) : ModEquiv R P m₁ m₂ j := by
  unfold checkAmongV at h
  split at h
  · rename_i mt₁ I₁ mt₂ I₂ h₁ h₂
    rw [List.getElem?_map, hj] at h
    simp only [Option.map_some, Option.some.injEq] at h
    apply modEquiv_of_fnCheckV hR (fuel := fuel)
    rw [fnCheckV, fnSumC?_of_inst h₁, fnSumC?_of_inst h₂]
    exact h
  · simp at h

/-! ## Kernel-cheap form -/

theorem sumCheckVK_eq : sumCheckVK = sumCheckV := by
  funext A B
  cases A <;> cases B <;> try rfl
  rename_i A B
  simp only [sumCheckVK, sumCheckV, Silmaril.Proofs.Wasm.Auto2.Kernel.bytesEqL_eq]
  congr 4
  simp [ByteArray.ext_iff, Array.toList_inj]

/-- **The chunk check of a certificate over `instK?`.** -/
theorem checkAmongV_eq_K {m₁ m₂ : Module} (h₁ : (validate? m₁).isSome = true)
    (h₂ : (validate? m₂).isSome = true) (fuel : Nat) (js : List Nat) :
    checkAmongV fuel m₁ m₂ js = checkAmongVK fuel m₁ m₂ js := by
  unfold checkAmongV checkAmongVK
  rw [Silmaril.Proofs.Wasm.Auto2.Kernel.instK?_eq h₁, Silmaril.Proofs.Wasm.Auto2.Kernel.instK?_eq h₂,
    sumCheckVK_eq]
  cases instance? m₁ <;> cases instance? m₂ <;> rfl

end Silmaril.Wasm.Auto2.Summ2
