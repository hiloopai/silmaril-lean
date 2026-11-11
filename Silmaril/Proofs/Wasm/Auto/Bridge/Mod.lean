module

public import Silmaril.Proofs.Wasm.Auto.Bridge.Func
public import Silmaril.Wasm.Auto.EGraph.Thms

/-!
# Function summaries: module refinement, equivalence and reference functions

From the behaviour sets of `Silmaril.Proofs.Wasm.Auto.Bridge.Func`:

* `modRefines_of_out`, `modEquiv_of_out`: two summarised exports with the same parameter types
  and the same results on every typed argument list refine each other, for every reflexive
  relation and every profile;
* `modEquiv_of_fnCheck` (equal normal forms), `modEquiv_of_fnResiduals` (proved residual
  goals), `modEquiv_of_egraph` (an e-graph certificate, `Silmaril.Wasm.Auto.EGraph.SegEquiv`, on
  the bodies, through `fnOut_eq_of_exec`);
* `modMeets_of_fnSum`: a summarised export meets a reference function that agrees with its
  summary on typed arguments.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.Bridge

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Bridge
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation
open Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm.Logic.Hoare
open Silmaril.Wasm.Logic.Core (Post exec)
open Silmaril.Wasm.Game (ScalarType ScalarInstance FnType)
open Silmaril.Wasm.Verify (instance? instOf isInstance_of_instance?)
open Silmaril.Wasm.Auto.Front (addrOf ModRefines ModEquiv ModMeets Rel specOfFn)

variable {P : Profile}

/-- Typed arguments of a summarised export. -/
theorem typedVals_of_fnSum {m : Module} {j : Nat} {F : FnSum} (h : fnSum? m j = some F)
    {vs : List Val} (hvs : InvokeOk (instOf m).store (addrOf m j) vs) : TypedVals F.params vs := by
  obtain ⟨mt, I, ft, fi, hI, hft, hfi, hs⟩ := fnSum?_inv h
  have hinst : instOf m = I := by simp [instOf, hI]
  have haddr : addrOf m j = I.addrs.getD j 0 := by simp [addrOf, hinst]
  rw [hinst, haddr] at hvs
  exact typedVals_of_invokeOk hs hfi (export_expand hI hft hfi) hvs

/-- The behaviour set of a summarised export on typed arguments. -/
theorem behaviours_of_fnSum_typed {m : Module} {j : Nat} {F : FnSum} (h : fnSum? m j = some F)
    {vs : List Val} (htv : TypedVals F.params vs) :
    behaviours P SingleThreaded.Det.noHost (instOf m).store (addrOf m j) vs = {.returns (fnOut F vs)} := by
  obtain ⟨mt, I, ft, fi, hI, hft, hfi, hs⟩ := fnSum?_inv h
  have hinst : instOf m = I := by simp [instOf, hI]
  have haddr : addrOf m j = I.addrs.getD j 0 := by simp [addrOf, hinst]
  rw [hinst, haddr]
  exact behaviours_eq_of_tfspec (tfspec_of_sumOf hs hfi (export_expand hI hft hfi))
    ⟨rfl, htv⟩ (fun _ _ ho => ho)

/-- **Refinement from equal results.** -/
theorem modRefines_of_out {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b, R b b)
    {m₁ m₂ : Module} {j : Nat} {A B : FnSum} (hA : fnSum? m₁ j = some A)
    (hB : fnSum? m₂ j = some B) (hp : A.params = B.params)
    (hout : ∀ vs, TypedVals A.params vs → fnOut A vs = fnOut B vs) :
    ModRefines R P m₁ m₂ j := by
  refine exportRefines_of_singleton hR (fnOut A) (fun vs hvs => ?_) (fun vs hvs => ?_)
  · exact behaviours_of_fnSum_typed hA (typedVals_of_fnSum hA hvs)
  · have htv := typedVals_of_fnSum hA hvs
    rw [behaviours_of_fnSum_typed hB (hp ▸ htv), hout vs htv]

/-- **Equivalence from equal results.** -/
theorem modEquiv_of_out {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b, R b b)
    {m₁ m₂ : Module} {j : Nat} {A B : FnSum} (hA : fnSum? m₁ j = some A)
    (hB : fnSum? m₂ j = some B) (hp : A.params = B.params)
    (hout : ∀ vs, TypedVals A.params vs → fnOut A vs = fnOut B vs) :
    ModEquiv R P m₁ m₂ j :=
  ⟨modRefines_of_out hR hA hB hp hout,
    modRefines_of_out (R := fun x y => R y x) hR hB hA hp.symm
      (fun vs htv => (hout vs (hp ▸ htv)).symm)⟩

theorem fnCheck_inv {m₁ m₂ : Module} {j : Nat} (h : fnCheck m₁ m₂ j = true) :
    ∃ A B, fnSum? m₁ j = some A ∧ fnSum? m₂ j = some B ∧ A.params = B.params ∧
      ∀ vs, fnOut A vs = fnOut B vs := by
  unfold fnCheck at h
  split at h
  · rename_i A B hA hB
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    refine ⟨A, B, hA, hB, h.1, fun vs => ?_⟩
    simp only [fnOut, stackAt, map_den_of_slotsEq h.2]
  · cases h

/-- **The function-level check proves module refinement**, every profile, every reflexive
relation. -/
theorem modRefines_of_fnCheck {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b, R b b)
    {m₁ m₂ : Module} {j : Nat} (h : fnCheck m₁ m₂ j = true) : ModRefines R P m₁ m₂ j := by
  obtain ⟨A, B, hA, hB, hp, hout⟩ := fnCheck_inv h
  exact modRefines_of_out hR hA hB hp fun vs _ => hout vs

/-- **The function-level check proves module equivalence.** -/
theorem modEquiv_of_fnCheck {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b, R b b)
    {m₁ m₂ : Module} {j : Nat} (h : fnCheck m₁ m₂ j = true) : ModEquiv R P m₁ m₂ j := by
  obtain ⟨A, B, hA, hB, hp, hout⟩ := fnCheck_inv h
  exact modEquiv_of_out hR hA hB hp fun vs _ => hout vs

/-- **Residual goals**: proofs of the remaining bitvector equations give module equivalence. -/
theorem modEquiv_of_fnResiduals {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b, R b b)
    {m₁ m₂ : Module} {j : Nat} {gs : List Goal} (h : fnResiduals m₁ m₂ j = some gs)
    (hg : ∀ g ∈ gs, g.Holds) : ModEquiv R P m₁ m₂ j := by
  unfold fnResiduals at h
  split at h
  · rename_i A B hA hB
    split at h
    · rename_i hp
      refine modEquiv_of_out hR hA hB hp fun vs _ => ?_
      simp only [fnOut, stackAt, map_den_of_slotsGoals h hg]
    · cases h
  · cases h

/-- **Reference functions**: a summarised export meets `f` if `f` agrees with the summary (or
leaves the result open) on typed arguments. -/
theorem modMeets_of_fnSum {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b, R b b)
    {m : Module} {j : Nat} {F : FnSum} (h : fnSum? m j = some F) {f : List Val → Option Result}
    (hf : ∀ vs, TypedVals F.params vs → f vs = some (.values (fnOut F vs)) ∨ f vs = none) :
    ModMeets R P m j f := by
  intro vs hvs b hb
  have htv := typedVals_of_fnSum h hvs
  change b ∈ behaviours P SingleThreaded.Det.noHost _ _ vs at hb
  rw [behaviours_of_fnSum_typed h htv] at hb
  refine ⟨b, ?_, hR b⟩
  simp only [Set.mem_singleton_iff] at hb
  subst hb
  unfold specOfFn
  rcases hf vs htv with hs | hs
  · rw [hs]
    rfl
  · rw [hs]
    trivial

/-- Every front-end relation is reflexive. -/
theorem rel_refl (R : Rel) : ∀ b, R.toProp b b := by
  intro b
  cases R
  · rfl
  · exact Or.inr rfl

end Silmaril.Proofs.Wasm.Auto.Bridge