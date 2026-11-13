module

public import Silmaril.Raw.Wasm.Auto2.Summ.Func
public import Silmaril.Raw.Wasm.Auto2.Summ.Simp
public import Silmaril.Wasm.Auto.Front.Thms

/-!
# Summaries with unrolled loops, the guard-aware check: module equivalence (unrefined)

* `modEquiv_of_outU`: two exports summarised by the unrolling executor with the same parameter
  types and the same result (returning or trapping) on every typed argument list are equivalent,
  for every reflexive relation and every profile;
* `out_of_sumCheckU`: the check `sumCheckU` gives equal results: both always trap (dead guards),
  or the guards hold together (equal keys) and the simplified results are equal;
* **`modEquiv_of_fnCheckU`**, **`modEquiv_of_checkAmongU`**: the check proves `ModEquiv`;
* **`checkEquivU_proved`**, `checkRefinesU_proved`, `modEquiv_of_proveStageU`: a `proved` report
  of the front end proves `ModEquiv` at every profile.

New proofs (unrefined: valid, not yet in Isar style).
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.Summ

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm.Auto.Bridge
open Silmaril.Wasm.Auto.Equiv (Env envOfVals TypedVals)
open Silmaril.Wasm.Verify (instance? instOf)
open Silmaril.Wasm.Auto.Front (addrOf ModRefines ModEquiv ExportRefines Report Rel)

variable {P : Profile} {fuel : Nat}

/-- **Refinement from equal results.** -/
theorem modRefines_of_outU {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b, R b b)
    {m₁ m₂ : Module} {j : Nat} {A B : FnSumX} (hA : fnSumU? fuel m₁ j = some A)
    (hB : fnSumU? fuel m₂ j = some B) (hp : A.params = B.params)
    (hout : ∀ vs, TypedVals A.params vs → fnOutX A vs = fnOutX B vs) :
    ModRefines R P m₁ m₂ j := by
  refine exportRefines_of_singletonB hR (fun vs => (fnOutX A vs).toBehaviour)
    (fun vs hvs => ?_) (fun vs hvs => ?_)
  · exact behaviours_of_fnSumU hA hvs
  · have htv := typedVals_of_fnSumU hA hvs
    rw [behaviours_of_fnSumU_typed hB (hp ▸ htv), hout vs htv]

/-- **Equivalence from equal results.** -/
theorem modEquiv_of_outU {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b, R b b)
    {m₁ m₂ : Module} {j : Nat} {A B : FnSumX} (hA : fnSumU? fuel m₁ j = some A)
    (hB : fnSumU? fuel m₂ j = some B) (hp : A.params = B.params)
    (hout : ∀ vs, TypedVals A.params vs → fnOutX A vs = fnOutX B vs) :
    ModEquiv R P m₁ m₂ j :=
  ⟨modRefines_of_outU hR hA hB hp hout,
    modRefines_of_outU (R := fun x y => R y x) hR hB hA hp.symm
      (fun vs htv => (hout vs (hp ▸ htv)).symm)⟩

/-! ## The check -/

theorem guardsOk_of_anyDead {ρ : Env} {B0 : ByteArray} {G : List (Guard × XState)}
    (h : anyDead G = true) : guardsOk ρ B0 G = false := by
  simp only [anyDead, List.any_eq_true] at h
  obtain ⟨g, hg, hd⟩ := h
  cases hk : guardsOk ρ B0 G
  · rfl
  · simp only [guardsOk, List.all_eq_true] at hk
    have := hk g hg
    rw [holds_of_gdead hd] at this
    cases this

/-- Guard keys contained: if the guards of `G'` hold, so do those of `G`. -/
theorem guardsOk_of_keys {ρ : Env} {B0 : ByteArray} {G G' : List (Guard × XState)}
    (hs : (keys G).all (keys G').contains = true) (h : guardsOk ρ B0 G' = true) :
    guardsOk ρ B0 G = true := by
  simp only [keys, List.all_eq_true, List.mem_map, List.contains_iff_mem,
    forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hs
  simp only [guardsOk, List.all_eq_true] at h ⊢
  intro g hg
  obtain ⟨g', hg', he⟩ := hs g hg
  rw [← holds_gkey, ← he, holds_gkey]
  exact h g' hg'

theorem guardsOk_keys_eq {ρ : Env} {B0 : ByteArray} {G G' : List (Guard × XState)}
    (h₁ : (keys G).all (keys G').contains = true) (h₂ : (keys G').all (keys G).contains = true) :
    guardsOk ρ B0 G = guardsOk ρ B0 G' := by
  cases hG : guardsOk ρ B0 G <;> cases hG' : guardsOk ρ B0 G'
  · rfl
  · rw [guardsOk_of_keys h₁ hG'] at hG
    cases hG
  · rw [guardsOk_of_keys h₂ hG] at hG'
    cases hG'
  · rfl

/-- Equal guard keys and simplified results, from the same initial memory. -/
theorem outAt_eqU {ρ : Env} {B0 : ByteArray} {S T : XState}
    (h₁ : (keys S.guards).all (keys T.guards).contains = true)
    (h₂ : (keys T.guards).all (keys S.guards).contains = true)
    (hs : slots2 S.stack = slots2 T.stack) : outAt ρ B0 S = outAt ρ B0 T := by
  have hst : S.stack.map (denX ρ B0) = T.stack.map (denX ρ B0) := by
    rw [← map_denX_slots2, hs, map_denX_slots2]
  simp only [outAt, guardsOk_keys_eq (ρ := ρ) (B0 := B0) h₁ h₂, hst]

/-- **An accepted pair of summaries gives equal results.** -/
theorem out_of_sumCheckU {A B : FnSumX} (h : sumCheckU (some A) (some B) = true) :
    A.params = B.params ∧ ∀ vs, fnOutX A vs = fnOutX B vs := by
  simp only [sumCheckU, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, Bool.or_eq_true,
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
      exact outAt_eqU h₁ h₂ hs
    · rw [hm]
      exact outAt_eqU h₁ h₂ hs

/-- **The check proves module equivalence**, every profile, every reflexive relation. -/
theorem modEquiv_of_fnCheckU {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b, R b b)
    {m₁ m₂ : Module} {j : Nat} (h : fnCheckU fuel m₁ m₂ j = true) : ModEquiv R P m₁ m₂ j := by
  unfold fnCheckU at h
  cases hA : fnSumU? fuel m₁ j with
  | none => rw [hA] at h; simp [sumCheckU] at h
  | some A =>
    cases hB : fnSumU? fuel m₂ j with
    | none => rw [hA, hB] at h; simp [sumCheckU] at h
    | some B =>
      rw [hA, hB] at h
      obtain ⟨hp, hout⟩ := out_of_sumCheckU h
      exact modEquiv_of_outU hR hA hB hp fun vs _ => hout vs

theorem fnSumU?_of_inst {m : Module} {mt : Validation.CModuleType}
    {I : Silmaril.Wasm.Game.ScalarInstance} (h : instance? m = some (mt, I)) (j : Nat) :
    fnSumU? fuel m j = fnSumUI fuel I j := by
  simp only [fnSumU?, h]

/-- **Entry `i` of `checkAmongU fuel m₁ m₂ js` proves module equivalence at export `js[i]`**,
every profile. -/
theorem modEquiv_of_checkAmongU {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b, R b b)
    {m₁ m₂ : Module} {js : List Nat} {i j : Nat} (hj : js[i]? = some j)
    (h : (checkAmongU fuel m₁ m₂ js)[i]? = some true) : ModEquiv R P m₁ m₂ j := by
  unfold checkAmongU at h
  split at h
  · rename_i mt₁ I₁ mt₂ I₂ h₁ h₂
    rw [List.getElem?_map, hj] at h
    simp only [Option.map_some, Option.some.injEq] at h
    apply modEquiv_of_fnCheckU hR (fuel := fuel)
    rw [fnCheckU, fnSumU?_of_inst h₁, fnSumU?_of_inst h₂]
    exact h
  · simp at h

/-! ## The front end -/

theorem upgradeU_proved {r : Report} {ok : Bool} (h : (upgradeU r ok).verdict = .proved) :
    r.verdict = .proved ∨ ok = true := by
  unfold upgradeU at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact Or.inr hc.2
  · exact Or.inl h

theorem upgradeU_refuted {r : Report} {ok : Bool} (h : (upgradeU r ok).verdict = .refuted) :
    r.verdict = .refuted := by
  unfold upgradeU at h
  split at h
  · cases h
  · exact h

/-- **A `proved` report of `checkEquivU` proves the equivalence**, every profile (`hid`: the
`identical` flag is only set for identical modules). -/
theorem checkEquivU_proved {R : Rel} {m₁ m₂ : Module} {j n : Nat} {idt : Bool}
    (hid : idt = true → m₁ = m₂) (h : (checkEquivU R m₁ m₂ j n idt).verdict = .proved)
    (P : Profile) : ModEquiv R.toProp P m₁ m₂ j := by
  rcases upgradeU_proved h with h | h
  · exact Silmaril.Wasm.Auto.Front.checkEquiv_proved hid h P
  · exact modEquiv_of_fnCheckU (Silmaril.Wasm.Auto.Bridge.rel_refl R) h

/-- **A `proved` report of `checkRefinesU` proves the equivalence**, every profile. -/
theorem checkRefinesU_proved {R : Rel} {impl spec : Module} {j n : Nat} {idt : Bool}
    (hid : idt = true → impl = spec) (h : (checkRefinesU R impl spec j n idt).verdict = .proved)
    (P : Profile) : ModEquiv R.toProp P impl spec j := by
  rcases upgradeU_proved h with h | h
  · exact Silmaril.Wasm.Auto.Front.checkRefines_proved hid h P
  · exact modEquiv_of_fnCheckU (Silmaril.Wasm.Auto.Bridge.rel_refl R) h

/-- A `refuted` report of `checkEquivU` is a refutation at the deterministic profile. -/
theorem checkEquivU_refuted {R : Rel} {m₁ m₂ : Module} {j n : Nat} {idt : Bool}
    (h : (checkEquivU R m₁ m₂ j n idt).verdict = .refuted) :
    ¬ ModEquiv R.toProp (Silmaril.Wasm.SingleThreaded.profile Silmaril.Wasm.Verify.refOracle) m₁ m₂ j :=
  Silmaril.Wasm.Auto.Front.checkEquiv_refuted (upgradeU_refuted h)

/-- **A `proved` verdict of the proving stages is an equivalence**, every profile. -/
theorem modEquiv_of_proveStageU {m₁ m₂ : Module} {j : Nat}
    (h : (proveStageU m₁ m₂ j).verdict = .proved) (R : Rel) (P : Profile) :
    ModEquiv R.toProp P m₁ m₂ j := by
  rcases upgradeU_proved h with h | h
  · exact Silmaril.Wasm.Auto.Front.modEquiv_of_proveStage h R P
  · exact modEquiv_of_fnCheckU (Silmaril.Wasm.Auto.Bridge.rel_refl R) h

end Silmaril.Wasm.Auto2.Summ
