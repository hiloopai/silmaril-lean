module

public import Silmaril.Proofs.Wasm.Auto.Bridge.EGraph
public import Silmaril.Proofs.Wasm.Auto.Bridge.Lemmas

/-!
# Every export at once

`modEquiv_of_checkAll`: entry `j` of `checkAll m₁ m₂` (the function-level stage on every export,
each module instantiated once) proves `ModEquiv` at export `j`; `egraphLiftOk_of_liftAll`: entry
`j` of `liftAll` gives the side conditions of `modEquiv_of_egraph`. Certificates evaluate
`checkAll`/`liftAll` once by the kernel and read every export's theorem off the result.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.Bridge

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Bridge
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm.Verify (instance?)
open Silmaril.Wasm.Auto.Front (ModEquiv)

theorem fnSum?_of_inst {m : Module} {mt : Validation.CModuleType} {I : Silmaril.Wasm.Game.ScalarInstance}
    (h : instance? m = some (mt, I)) (j : Nat) : fnSum? m j = fnSumI I j := by
  simp only [fnSum?, h]

theorem fnBody?_of_inst {m : Module} {mt : Validation.CModuleType}
    {I : Silmaril.Wasm.Game.ScalarInstance} (h : instance? m = some (mt, I)) (j : Nat) :
    fnBody? m j = fnBodyI I j := by
  simp only [fnBody?, h]

/-- An accepted pair of summaries gives equal results. -/
theorem out_of_sumCheck {A B : FnSum} (h : sumCheck discharged (some A) (some B) = true) :
    A.params = B.params ∧ ∀ vs, fnOut A vs = fnOut B vs := by
  simp only [sumCheck, Bool.and_eq_true, beq_iff_eq, Bool.or_eq_true] at h
  obtain ⟨hp, hs | hg⟩ := h
  · exact ⟨hp, fun vs => by simp only [fnOut, stackAt, map_den_of_slotsEq hs]⟩
  · split at hg
    · rename_i gs hgs
      exact ⟨hp, fun vs => by
        simp only [fnOut, stackAt, map_den_of_slotsGoals hgs (discharged_sound hg)]⟩
    · cases hg

/-- **Entry `j` of `checkAll` proves module equivalence at export `j`**, every profile. -/
theorem modEquiv_of_checkAll {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b, R b b)
    {P : Profile} {m₁ m₂ : Module} {j : Nat} (h : (checkAll m₁ m₂)[j]? = some true) :
    ModEquiv R P m₁ m₂ j := by
  unfold checkAll at h
  split at h
  · rename_i mt₁ I₁ mt₂ I₂ h₁ h₂
    obtain ⟨hj, hc⟩ := List.getElem?_eq_some_iff.mp h
    have hc' : sumCheck discharged (fnSumI I₁ j) (fnSumI I₂ j) = true := by
      simpa using hc
    cases hA : fnSumI I₁ j with
    | none => rw [hA] at hc'; simp [sumCheck] at hc'
    | some A =>
      cases hB : fnSumI I₂ j with
      | none => rw [hA, hB] at hc'; simp [sumCheck] at hc'
      | some B =>
        rw [hA, hB] at hc'
        obtain ⟨hp, hout⟩ := out_of_sumCheck hc'
        exact modEquiv_of_out hR (by rw [fnSum?_of_inst h₁, hA]) (by rw [fnSum?_of_inst h₂, hB])
          hp fun vs _ => hout vs
  · simp at h

/-- The Boolean side conditions, with the common local types named `Γ`. -/
theorem liftBool {A B : FnSum} {Γ Γ₂ : List IntType} {a b : List Instr}
    (hok : (A.params == B.params && Γ == Γ₂ && a.all plainI && b.all plainI &&
      decide (Γ.length < 2 ^ 32)) = true) :
    (A.params == B.params && Γ == Γ && Γ₂ == Γ && a.all plainI && b.all plainI &&
      decide (Γ.length < 2 ^ 32)) = true := by
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true, decide_eq_true_eq] at hok ⊢
  obtain ⟨⟨⟨⟨hp, hΓ⟩, hpa⟩, hpb⟩, hn⟩ := hok
  exact ⟨⟨⟨⟨⟨hp, trivial⟩, hΓ.symm⟩, hpa⟩, hpb⟩, hn⟩

/-- **Entry `j` of `liftAll` gives the e-graph side conditions at export `j`.** -/
theorem egraphLiftOk_of_liftAll {m₁ m₂ : Module} {j : Nat} {Γ : List IntType}
    (h : (liftAll m₁ m₂)[j]? = some (some Γ)) : egraphLiftOk m₁ m₂ j Γ = true := by
  unfold liftAll at h
  split at h
  · rename_i mt₁ I₁ mt₂ I₂ h₁ h₂
    obtain ⟨hj, hc⟩ := List.getElem?_eq_some_iff.mp h
    have hc' : liftCheckI I₁ I₂ j = some Γ := by simpa using hc
    unfold liftCheckI at hc'
    unfold egraphLiftOk
    rw [fnSum?_of_inst h₁, fnSum?_of_inst h₂, fnBody?_of_inst h₁, fnBody?_of_inst h₂]
    split at hc'
    · split at hc'
      · rename_i hok
        obtain rfl : _ = Γ := Option.some.inj hc'
        exact liftBool hok
      · cases hc'
    · cases hc'
  · simp at h

end Silmaril.Proofs.Wasm.Auto.Bridge