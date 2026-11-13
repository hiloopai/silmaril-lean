module

public import Silmaril.Raw.Wasm.Auto2.Calls.Func
public import Silmaril.Wasm.Auto2.Summ.Thms

/-!
# Summaries with inlined calls: module equivalence (unrefined)

* `modEquiv_of_outC`: two exports summarised with inlined calls, with the same parameter types
  and the same result on every typed argument list, are equivalent (every reflexive relation,
  every profile);
* **`modEquiv_of_fnCheckC`**, **`modEquiv_of_checkAmongC`**: the guard-aware check
  (`Silmaril.Wasm.Auto2.Summ.sumCheckU`, `out_of_sumCheckU`) on these summaries proves `ModEquiv`;
* **`checkEquivC_proved`**, `checkRefinesC_proved`, `modEquiv_of_proveStageC`: a `proved` report
  of the front end proves `ModEquiv` at every profile; `checkEquivC_refuted`: a `refuted` report is
  a refutation at the deterministic profile.

New proofs (unrefined: valid, not yet in Isar style).
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.Calls

open Silmaril.Wasm Silmaril.Wasm.Execution Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm.Auto.Bridge
open Silmaril.Wasm.Auto2.Summ (sumCheckU out_of_sumCheckU)
open Silmaril.Wasm.Auto.Equiv (Env envOfVals TypedVals)
open Silmaril.Wasm.Verify (instance? instOf)
open Silmaril.Wasm.Auto.Front (addrOf ModRefines ModEquiv ExportRefines Report Rel)

variable {P : Profile} {fuel : Nat}

/-- **Refinement from equal results.** -/
theorem modRefines_of_outC {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b, R b b)
    {m₁ m₂ : Module} {j : Nat} {A B : FnSumX} (hA : fnSumC? fuel m₁ j = some A)
    (hB : fnSumC? fuel m₂ j = some B) (hp : A.params = B.params)
    (hout : ∀ vs, TypedVals A.params vs → fnOutX A vs = fnOutX B vs) :
    ModRefines R P m₁ m₂ j := by
  refine exportRefines_of_singletonB hR (fun vs => (fnOutX A vs).toBehaviour)
    (fun vs hvs => ?_) (fun vs hvs => ?_)
  · exact behaviours_of_fnSumC hA hvs
  · have htv := typedVals_of_fnSumC hA hvs
    rw [behaviours_of_fnSumC_typed hB (hp ▸ htv), hout vs htv]

/-- **Equivalence from equal results.** -/
theorem modEquiv_of_outC {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b, R b b)
    {m₁ m₂ : Module} {j : Nat} {A B : FnSumX} (hA : fnSumC? fuel m₁ j = some A)
    (hB : fnSumC? fuel m₂ j = some B) (hp : A.params = B.params)
    (hout : ∀ vs, TypedVals A.params vs → fnOutX A vs = fnOutX B vs) :
    ModEquiv R P m₁ m₂ j :=
  ⟨modRefines_of_outC hR hA hB hp hout,
    modRefines_of_outC (R := fun x y => R y x) hR hB hA hp.symm
      (fun vs htv => (hout vs (hp ▸ htv)).symm)⟩

/-- **The check proves module equivalence**, every profile, every reflexive relation. -/
theorem modEquiv_of_fnCheckC {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b, R b b)
    {m₁ m₂ : Module} {j : Nat} (h : fnCheckC fuel m₁ m₂ j = true) : ModEquiv R P m₁ m₂ j := by
  unfold fnCheckC at h
  cases hA : fnSumC? fuel m₁ j with
  | none => rw [hA] at h; simp [sumCheckU] at h
  | some A =>
    cases hB : fnSumC? fuel m₂ j with
    | none => rw [hA, hB] at h; simp [sumCheckU] at h
    | some B =>
      rw [hA, hB] at h
      obtain ⟨hp, hout⟩ := out_of_sumCheckU h
      exact modEquiv_of_outC hR hA hB hp fun vs _ => hout vs

theorem fnSumC?_of_inst {m : Module} {mt : Validation.CModuleType}
    {I : Silmaril.Wasm.Game.ScalarInstance} (h : instance? m = some (mt, I)) (j : Nat) :
    fnSumC? fuel m j = fnSumCI fuel I j := by
  simp only [fnSumC?, h]

/-- **Entry `i` of `checkAmongC fuel m₁ m₂ js` proves module equivalence at export `js[i]`**,
every profile. -/
theorem modEquiv_of_checkAmongC {R : Behaviour Val → Behaviour Val → Prop} (hR : ∀ b, R b b)
    {m₁ m₂ : Module} {js : List Nat} {i j : Nat} (hj : js[i]? = some j)
    (h : (checkAmongC fuel m₁ m₂ js)[i]? = some true) : ModEquiv R P m₁ m₂ j := by
  unfold checkAmongC at h
  split at h
  · rename_i mt₁ I₁ mt₂ I₂ h₁ h₂
    rw [List.getElem?_map, hj] at h
    simp only [Option.map_some, Option.some.injEq] at h
    apply modEquiv_of_fnCheckC hR (fuel := fuel)
    rw [fnCheckC, fnSumC?_of_inst h₁, fnSumC?_of_inst h₂]
    exact h
  · simp at h

/-! ## The front end -/

theorem upgradeC_proved {r : Report} {ok : Bool} (h : (upgradeC r ok).verdict = .proved) :
    r.verdict = .proved ∨ ok = true := by
  unfold upgradeC at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact Or.inr hc.2
  · exact Or.inl h

theorem upgradeC_refuted {r : Report} {ok : Bool} (h : (upgradeC r ok).verdict = .refuted) :
    r.verdict = .refuted := by
  unfold upgradeC at h
  split at h
  · cases h
  · exact h

/-- **A `proved` report of `checkEquivC` proves the equivalence**, every profile (`hid`: the
`identical` flag is only set for identical modules). -/
theorem checkEquivC_proved {R : Rel} {m₁ m₂ : Module} {j n : Nat} {idt : Bool}
    (hid : idt = true → m₁ = m₂) (h : (checkEquivC R m₁ m₂ j n idt).verdict = .proved)
    (P : Profile) : ModEquiv R.toProp P m₁ m₂ j := by
  rcases upgradeC_proved h with h | h
  · exact Silmaril.Wasm.Auto2.Summ.checkEquivU_proved hid h P
  · exact modEquiv_of_fnCheckC (Silmaril.Wasm.Auto.Bridge.rel_refl R) h

/-- **A `proved` report of `checkRefinesC` proves the equivalence**, every profile. -/
theorem checkRefinesC_proved {R : Rel} {impl spec : Module} {j n : Nat} {idt : Bool}
    (hid : idt = true → impl = spec) (h : (checkRefinesC R impl spec j n idt).verdict = .proved)
    (P : Profile) : ModEquiv R.toProp P impl spec j := by
  rcases upgradeC_proved h with h | h
  · exact Silmaril.Wasm.Auto2.Summ.checkRefinesU_proved hid h P
  · exact modEquiv_of_fnCheckC (Silmaril.Wasm.Auto.Bridge.rel_refl R) h

/-- A `refuted` report of `checkEquivC` is a refutation at the deterministic profile. -/
theorem checkEquivC_refuted {R : Rel} {m₁ m₂ : Module} {j n : Nat} {idt : Bool}
    (h : (checkEquivC R m₁ m₂ j n idt).verdict = .refuted) :
    ¬ ModEquiv R.toProp (Silmaril.Wasm.SingleThreaded.profile Silmaril.Wasm.Verify.refOracle) m₁ m₂ j :=
  Silmaril.Wasm.Auto2.Summ.checkEquivU_refuted (upgradeC_refuted h)

/-- **A `proved` verdict of the proving stages is an equivalence**, every profile. -/
theorem modEquiv_of_proveStageC {m₁ m₂ : Module} {j : Nat}
    (h : (proveStageC m₁ m₂ j).verdict = .proved) (R : Rel) (P : Profile) :
    ModEquiv R.toProp P m₁ m₂ j := by
  rcases upgradeC_proved h with h | h
  · exact Silmaril.Wasm.Auto2.Summ.modEquiv_of_proveStageU h R P
  · exact modEquiv_of_fnCheckC (Silmaril.Wasm.Auto.Bridge.rel_refl R) h

end Silmaril.Wasm.Auto2.Calls
