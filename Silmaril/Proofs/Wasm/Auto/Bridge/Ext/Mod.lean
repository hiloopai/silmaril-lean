module

public import Silmaril.Proofs.Wasm.Auto.Bridge.Ext.Func

/-!
# Summaries with memory, globals and traps: module equivalence

* `modEquiv_of_outX`: two summarised exports with the same parameter types and the same result
  (returning or trapping) on every typed argument list are equivalent, for every reflexive
  relation and every profile;
* `out_of_sumCheckX`, **`modEquiv_of_fnCheckX`**: the check `sumCheckX` gives equal results
  (the simplifier preserves values and guards; results that read no memory and have no guards
  do not depend on the initial memory);
* **`modEquiv_of_checkAmong`**: entry `i` of `checkAmong m₁ m₂ js` (either summariser, each
  module instantiated once) proves `ModEquiv` at export `js[i]`; `egraphLiftOk_of_liftAmong`:
  the same for the e-graph side conditions.

New proofs (unrefined: valid, not yet in Isar style).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.Bridge

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.Bridge
open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm.Auto.Equiv (Env envOfVals TypedVals)
open Silmaril.Wasm.Verify (instance? instOf)
open Silmaril.Wasm.Auto.Front (addrOf ModRefines ModEquiv ExportRefines)

variable {P : Profile}

/-- Two singleton behaviour sets, equal on every accepted argument list, give refinement for any
reflexive relation. -/
theorem exportRefines_of_singletonB {R : Behaviour Val → Behaviour Val → Prop}
    (hR : ∀ b, R b b) {s₁ s₂ : Store Nat} {a₁ a₂ : Nat} (g : List Val → Behaviour Val)
    (h₁ : ∀ vs, InvokeOk s₁ a₁ vs → behaviours P SingleThreaded.Det.noHost s₁ a₁ vs = {g vs})
    (h₂ : ∀ vs, InvokeOk s₁ a₁ vs → behaviours P SingleThreaded.Det.noHost s₂ a₂ vs = {g vs}) :
    ExportRefines R P s₁ a₁ s₂ a₂ := by
  intro vs hvs b hb
  rw [h₁ vs hvs] at hb
  refine ⟨b, ?_, hR b⟩
  rw [h₂ vs hvs]
  exact hb

/-- **Refinement from equal results.** -/
theorem modRefines_of_outX {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b, R b b)
    {m₁ m₂ : Module} {j : Nat} {A B : FnSumX} (hA : fnSumX? m₁ j = some A)
    (hB : fnSumX? m₂ j = some B) (hp : A.params = B.params)
    (hout : ∀ vs, TypedVals A.params vs → fnOutX A vs = fnOutX B vs) :
    ModRefines R P m₁ m₂ j := by
  refine exportRefines_of_singletonB hR (fun vs => (fnOutX A vs).toBehaviour)
    (fun vs hvs => ?_) (fun vs hvs => ?_)
  · exact behaviours_of_fnSumX hA hvs
  · have htv := typedVals_of_fnSumX hA hvs
    rw [behaviours_of_fnSumX_typed hB (hp ▸ htv), hout vs htv]

/-- **Equivalence from equal results.** -/
theorem modEquiv_of_outX {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b, R b b)
    {m₁ m₂ : Module} {j : Nat} {A B : FnSumX} (hA : fnSumX? m₁ j = some A)
    (hB : fnSumX? m₂ j = some B) (hp : A.params = B.params)
    (hout : ∀ vs, TypedVals A.params vs → fnOutX A vs = fnOutX B vs) :
    ModEquiv R P m₁ m₂ j :=
  ⟨modRefines_of_outX hR hA hB hp hout,
    modRefines_of_outX (R := fun x y => R y x) hR hB hA hp.symm
      (fun vs htv => (hout vs (hp ▸ htv)).symm)⟩

/-! ## The check -/

theorem evX_noLoad (ρ : Env) (B0 B1 : ByteArray) :
    ∀ (e : XT) (t : IntType), noLoad e = true → evX ρ B0 t e = evX ρ B1 t e := by
  intro e
  induction e with
  | var n => intro t _; simp [evX]
  | const c => intro t _; simp [evX]
  | un op a ih => intro t h; simp only [evX, ih t (by simpa only [noLoad] using h)]
  | bin op a b iha ihb =>
    intro t h
    have h' : noLoad a = true ∧ noLoad b = true := by simpa only [noLoad, Bool.and_eq_true] using h
    simp only [evX, iha t h'.1, ihb t h'.2]
  | rel t' op a b iha ihb =>
    intro t h
    have h' : noLoad a = true ∧ noLoad b = true := by simpa only [noLoad, Bool.and_eq_true] using h
    simp only [evX, iha t' h'.1, ihb t' h'.2]
  | wrap a ih => intro t h; simp only [evX, ih .i64 (by simpa only [noLoad] using h)]
  | ext sx a ih => intro t h; simp only [evX, ih .i32 (by simpa only [noLoad] using h)]
  | sel c a b ihc iha ihb =>
    intro t h
    have h' : (noLoad c = true ∧ noLoad a = true) ∧ noLoad b = true := by
      simpa only [noLoad, Bool.and_eq_true] using h
    simp only [evX, ihc .i32 h'.1.1, iha t h'.1.2, ihb t h'.2]
  | load m t' p a arg _ _ => intro t h; simp [noLoad] at h
  | minit => intro t _; simp [evX]
  | mstore m t' p a arg v _ _ _ => intro t _; simp [evX]

/-- A final state with no guards whose results read no memory does not depend on the initial
memory. -/
theorem outAt_indep {S : XState} (h : usesMem S = false) (ρ : Env) (B0 B1 : ByteArray) :
    outAt ρ B0 S = outAt ρ B1 S := by
  simp only [usesMem, Bool.or_eq_false_iff, Bool.not_eq_eq_eq_not, Bool.not_false,
    List.isEmpty_iff, List.all_eq_true] at h
  obtain ⟨hg, hs⟩ := h
  have hst : S.stack.map (denX ρ B0) = S.stack.map (denX ρ B1) := by
    apply List.map_congr_left
    intro p hp
    simp only [denX, evX_noLoad ρ B0 B1 p.2 p.1 (hs p hp)]
  simp only [outAt, guardsOk, hg, List.all_nil, ↓reduceIte, hst]

/-- Guards contained up to the simplifier: if those of `G'` hold, so do those of `G`. -/
theorem guardsOk_of_sub {ρ : Env} {B0 : ByteArray} {G G' : List (Guard × XState)}
    (hs : guardSub G G' = true) (h : guardsOk ρ B0 G' = true) : guardsOk ρ B0 G = true := by
  simp only [guardSub, List.all_eq_true, List.contains_iff_mem, List.mem_map] at hs
  simp only [guardsOk, List.all_eq_true] at h ⊢
  intro g hg
  obtain ⟨g', hg', he⟩ := hs g hg
  rw [← holds_canon, ← he, holds_canon]
  exact h g' hg'

theorem guardsOk_eq {ρ : Env} {B0 : ByteArray} {G G' : List (Guard × XState)}
    (h₁ : guardSub G G' = true) (h₂ : guardSub G' G = true) :
    guardsOk ρ B0 G = guardsOk ρ B0 G' := by
  cases hG : guardsOk ρ B0 G <;> cases hG' : guardsOk ρ B0 G'
  · rfl
  · rw [guardsOk_of_sub h₁ hG'] at hG
    cases hG
  · rw [guardsOk_of_sub h₂ hG] at hG'
    cases hG'
  · rfl

/-- Equal guards and simplified results, from the same initial memory. -/
theorem outAt_eq {ρ : Env} {B0 : ByteArray} {S T : XState}
    (h₁ : guardSub S.guards T.guards = true) (h₂ : guardSub T.guards S.guards = true)
    (hs : canonSlots S.stack = canonSlots T.stack) : outAt ρ B0 S = outAt ρ B0 T := by
  have hst : S.stack.map (denX ρ B0) = T.stack.map (denX ρ B0) := by
    rw [← map_denX_canonSlots, hs, map_denX_canonSlots]
  simp only [outAt, guardsOk_eq (ρ := ρ) (B0 := B0) h₁ h₂, hst]

/-- **An accepted pair of summaries gives equal results.** -/
theorem out_of_sumCheckX {A B : FnSumX} (h : sumCheckX (some A) (some B) = true) :
    A.params = B.params ∧ ∀ vs, fnOutX A vs = fnOutX B vs := by
  simp only [sumCheckX, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.or_eq_true,
    Bool.not_eq_eq_eq_not, Bool.not_true] at h
  obtain ⟨⟨⟨⟨⟨hp, hg⟩, hm⟩, h₁⟩, h₂⟩, hs⟩ := h
  refine ⟨hp, fun vs => ?_⟩
  have hρ : envX A vs = envX B vs := by simp only [envX, hg]
  simp only [fnOutX, hρ]
  rcases hm with hm | hm
  · simp only [Bool.or_eq_false_iff] at hm
    rw [outAt_indep hm.1 _ A.bytes B.bytes]
    exact outAt_eq h₁ h₂ hs
  · rw [hm]
    exact outAt_eq h₁ h₂ hs

/-- **The check proves module equivalence**, every profile, every reflexive relation. -/
theorem modEquiv_of_fnCheckX {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b, R b b)
    {m₁ m₂ : Module} {j : Nat} (h : fnCheckX m₁ m₂ j = true) : ModEquiv R P m₁ m₂ j := by
  unfold fnCheckX at h
  cases hA : fnSumX? m₁ j with
  | none => rw [hA] at h; simp [sumCheckX] at h
  | some A =>
    cases hB : fnSumX? m₂ j with
    | none => rw [hA, hB] at h; simp [sumCheckX] at h
    | some B =>
      rw [hA, hB] at h
      obtain ⟨hp, hout⟩ := out_of_sumCheckX h
      exact modEquiv_of_outX hR hA hB hp fun vs _ => hout vs

theorem fnSumX?_of_inst {m : Module} {mt : Validation.CModuleType}
    {I : Silmaril.Wasm.Game.ScalarInstance} (h : instance? m = some (mt, I)) (j : Nat) :
    fnSumX? m j = fnSumXI I j := by
  simp only [fnSumX?, h]

/-- The pass-1 summaries of export `j` of two instances agree: module equivalence. -/
theorem modEquiv_of_sumCheckI {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b, R b b)
    {m₁ m₂ : Module} {mt₁ mt₂ : Validation.CModuleType} {I₁ I₂ : Silmaril.Wasm.Game.ScalarInstance}
    (h₁ : instance? m₁ = some (mt₁, I₁)) (h₂ : instance? m₂ = some (mt₂, I₂)) {j : Nat}
    (hc : Bridge.sumCheck Bridge.discharged (Bridge.fnSumI I₁ j) (Bridge.fnSumI I₂ j) = true) :
    ModEquiv R P m₁ m₂ j := by
  cases hA : Bridge.fnSumI I₁ j with
  | none => simp [hA, Bridge.sumCheck] at hc
  | some A =>
    cases hB : Bridge.fnSumI I₂ j with
    | none => simp [hA, hB, Bridge.sumCheck] at hc
    | some B =>
      have hc' : Bridge.sumCheck Bridge.discharged (some A) (some B) = true := hA ▸ hB ▸ hc
      obtain ⟨hp, hout⟩ := Bridge.out_of_sumCheck hc'
      exact Bridge.modEquiv_of_out hR (by rw [Bridge.fnSum?_of_inst h₁, hA])
        (by rw [Bridge.fnSum?_of_inst h₂, hB]) hp fun vs _ => hout vs

/-- The extended summaries of export `j` of two instances agree: module equivalence. -/
theorem modEquiv_of_sumCheckXI {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b, R b b)
    {m₁ m₂ : Module} {mt₁ mt₂ : Validation.CModuleType} {I₁ I₂ : Silmaril.Wasm.Game.ScalarInstance}
    (h₁ : instance? m₁ = some (mt₁, I₁)) (h₂ : instance? m₂ = some (mt₂, I₂)) {j : Nat}
    (hc : sumCheckX (fnSumXI I₁ j) (fnSumXI I₂ j) = true) : ModEquiv R P m₁ m₂ j := by
  cases hA : fnSumXI I₁ j with
  | none => simp [hA, sumCheckX] at hc
  | some A =>
    cases hB : fnSumXI I₂ j with
    | none => simp [hA, hB, sumCheckX] at hc
    | some B =>
      have hc' : sumCheckX (some A) (some B) = true := hA ▸ hB ▸ hc
      obtain ⟨hp, hout⟩ := out_of_sumCheckX hc'
      exact modEquiv_of_outX hR (by rw [fnSumX?_of_inst h₁, hA])
        (by rw [fnSumX?_of_inst h₂, hB]) hp fun vs _ => hout vs

/-- **Entry `i` of `checkAmong m₁ m₂ js` proves module equivalence at export `js[i]`**, every
profile. -/
theorem modEquiv_of_checkAmong {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b, R b b)
    {m₁ m₂ : Module} {js : List Nat} {i j : Nat} (hj : js[i]? = some j)
    (h : (checkAmong m₁ m₂ js)[i]? = some true) : ModEquiv R P m₁ m₂ j := by
  unfold checkAmong at h
  split at h
  · rename_i mt₁ I₁ mt₂ I₂ h₁ h₂
    have hc : Bridge.sumCheck Bridge.discharged (Bridge.fnSumI I₁ j) (Bridge.fnSumI I₂ j) = true ∨
        sumCheckX (fnSumXI I₁ j) (fnSumXI I₂ j) = true := by
      simpa [List.getElem?_map, hj] using h
    rcases hc with hc | hc
    · exact modEquiv_of_sumCheckI hR h₁ h₂ hc
    · exact modEquiv_of_sumCheckXI hR h₁ h₂ hc
  · simp at h

/-- **Entry `i` of `liftAmong m₁ m₂ js` gives the e-graph side conditions at export `js[i]`.** -/
theorem egraphLiftOk_of_liftAmong {m₁ m₂ : Module} {js : List Nat} {i j : Nat}
    {Γ : List IntType} (hj : js[i]? = some j) (h : (liftAmong m₁ m₂ js)[i]? = some (some Γ)) :
    Bridge.egraphLiftOk m₁ m₂ j Γ = true := by
  unfold liftAmong at h
  split at h
  · rename_i mt₁ I₁ mt₂ I₂ h₁ h₂
    rw [List.getElem?_map, hj] at h
    have hc' : Bridge.liftCheckI I₁ I₂ j = some Γ := by simpa using h
    unfold Bridge.liftCheckI at hc'
    unfold Bridge.egraphLiftOk
    rw [Bridge.fnSum?_of_inst h₁, Bridge.fnSum?_of_inst h₂, Bridge.fnBody?_of_inst h₁,
      Bridge.fnBody?_of_inst h₂]
    split at hc'
    · split at hc'
      · rename_i hok
        obtain rfl : _ = Γ := Option.some.inj hc'
        exact Bridge.liftBool hok
      · cases hc'
    · cases hc'
  · simp at h

end Silmaril.Proofs.Wasm.Auto.Bridge