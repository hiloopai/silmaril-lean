module

public import Silmaril.Wasm.SpecTec.Sim.Round5.BwdStep.Defs
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5.BwdStep.StructNew
public import Silmaril.Raw.Wasm.SpecTec.Sim.Round5.BwdStep.Vec

/-!
# Round 5: the `step` field of `RemainingV`

* `step_lt`: `Step` has 36 rules, so no rule of index `≥ 36` fires.
* `step_doneR5`: every index of `stepDoneR5` has its backward lemma under `ReadValid`, in every
  profile in which growth may both succeed and fail (`Profile.spec` is one).
* `remStep_of_open`: the `step` field of `Round4Read.RemainingV` at the concrete `B`, from the
  rules of `stepOpenR5` alone.
* `pure_lt`, `pure_vecDone`, `remPure_of_open`: the same for the `pure` field, from family V's
  `VecAgree` and the rules of `pureOpenR5`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.BwdStep

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)
open Round4Int (BI)
open Round4Read (ReadValid)

variable {H : Type} {hn : H → String} {P : Profile} {host : HostSemantics H}

set_option maxRecDepth 100000 in
/-- `Step` has 36 rules. -/
theorem baseEnv_step_length : (baseEnv.findRel? "Step").map
    (fun r => (r.1, r.2.1, r.2.2.2.length)) = some ([], "%~>%", 36) := by
  rfl

/-- **No `Step` rule of index `≥ 36` fires.** -/
theorem step_lt {B : Builtins} {i : Nat} {v : Value} (hf : Fires (simEnv B) "Step" i v) :
    i < 36 := by
  obtain ⟨t, rules, r, hrel, hi, -⟩ := hf
  have h := baseEnv_step_length
  rw [← Env.findRel?_withBuiltins baseEnv B, ← simEnv, hrel] at h
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and] at h
  exact h ▸ (List.getElem?_eq_some_iff.1 hi).1

/-- **The rules of `stepDoneR5`, backward, under `ReadValid`.** -/
theorem step_doneR5 (hPs : ∀ k a n d, P.growMaySucceed k a n d)
    (hPf : ∀ k a n d, P.growMayFail k a n d) (i : Nat) (hi : i ∈ stepDoneR5) (c : Config H)
    (w : Value) (hv : ReadValid c)
    (hf : Fires (simEnv (BI P hn host)) "Step" i (.tuple [configV hn c, w])) :
    BwdP hn P host c w := by
  simp only [stepDoneR5, List.mem_cons, List.mem_nil_iff, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  exacts [bwd_tableGrowSucceed hPs hv hf, bwd_tableGrowFail hPf hv hf, bwd_storeNumVal hv hf,
    bwd_storePackVal hv hf, bwd_memoryGrowSucceed hPs hv hf, bwd_memoryGrowFail hPf hv hf,
    bwd_structNew hf, bwd_structSetStruct hf, bwd_arrayNewFixed hf, bwd_arraySetArray hf]

/-- **The `step` field of `RemainingV`, from the open rules `stepOpenR5`**, at the concrete `B`,
in every profile in which growth may both succeed and fail. -/
theorem remStep_of_open (hPs : ∀ k a n d, P.growMaySucceed k a n d)
    (hPf : ∀ k a n d, P.growMayFail k a n d) (O : StepOpenV hn P host) :
    ∀ (i : Nat), 6 ≤ i → i ∉ Bwd.stepDone → i ∉ BwdPureStep.stepDone →
      ∀ (c : Config H) (w : Value), ReadValid c → Typed (simEnv (BI P hn host)) hn c →
      Fires (simEnv (BI P hn host)) "Step" i (.tuple [configV hn c, w]) →
      Bwd.BwdUpTo hn P host c w := by
  intro i h6 h₁ h₂ c w hv hc hf
  have hlt := step_lt hf
  by_cases hd : i ∈ stepDoneR5
  · exact Bwd.step_upTo (step_doneR5 hPs hPf i hd c w hv hf)
  · refine O i ?_ c w hv hc hf
    simp only [Bwd.stepDone, BwdPureStep.stepDone, stepDoneR5, stepOpenR5, List.mem_cons,
      List.mem_nil_iff, or_false] at h₁ h₂ hd ⊢
    omega

set_option maxRecDepth 100000 in
/-- `Step_pure` has 79 rules. -/
theorem baseEnv_pure_length : (baseEnv.findRel? "Step_pure").map
    (fun r => (r.1, r.2.1, r.2.2.2.length)) = some ([], "%~>%", 79) := by
  rfl

/-- **No `Step_pure` rule of index `≥ 79` fires.** -/
theorem pure_lt {B : Builtins} {i : Nat} {v : Value} (hf : Fires (simEnv B) "Step_pure" i v) :
    i < 79 := by
  obtain ⟨t, rules, r, hrel, hi, -⟩ := hf
  have h := baseEnv_pure_length
  rw [← Env.findRel?_withBuiltins baseEnv B, ← simEnv, hrel] at h
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq, true_and] at h
  exact h ▸ (List.getElem?_eq_some_iff.1 hi).1

/-- **The vector rules of `pureVecDone`, backward**, given family V's `VecAgree` (`VecDecode`
is discharged, `vecDecode`). -/
theorem pure_vecDone (A : Vec.VecAgree (simEnv (BI P hn host)) P) (i : Nat)
    (hi : i ∈ pureVecDone) (s : Store H) (f : Frame) (is : List Admin) (w : Value)
    (hf : Fires (simEnv (BI P hn host)) "Step_pure" i (.tuple [.list (adminsToV is), w])) :
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToV js) ∧
      Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  obtain ⟨is', hw, hs⟩ := Vec.bwd_vectorRules (Vec.hasVectorRules_simEnv _) vecDecode A i hi hf
  exact ⟨is', is', Bwd.CodeEq.refl _, hw, hs⟩

/-- **The `pure` field of `RemainingV`, from `VecAgree` and the open rules `pureOpenR5`**, at the
concrete `B`. -/
theorem remPure_of_open (A : Vec.VecAgree (simEnv (BI P hn host)) P)
    (O : PureOpenV hn P host) :
    ∀ i, i ∉ Bwd.pureDone → i ∉ Integrate.floatDone → i ∉ BwdPureStep.pureDone →
      ∀ (s : Store H) (f : Frame) (is : List Admin) (w : Value), ReadValid ⟨s, f, is⟩ →
      Typed (simEnv (BI P hn host)) hn ⟨s, f, is⟩ →
      Fires (simEnv (BI P hn host)) "Step_pure" i (.tuple [.list (adminsToV is), w]) →
      ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToV js) ∧
        Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩ := by
  intro i h₁ h₂ h₃ s f is w hv hc hf
  have hlt := pure_lt hf
  by_cases hd : i ∈ pureVecDone
  · exact pure_vecDone A i hd s f is w hf
  · refine O i ?_ s f is w hv hc hf
    simp only [Bwd.pureDone, Integrate.floatDone, BwdPureStep.pureDone, pureVecDone, pureOpenR5,
      List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at h₁ h₂ h₃ hd ⊢
    omega

end Silmaril.Wasm.SpecTec.Sim.Round5.BwdStep
