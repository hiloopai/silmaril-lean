module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round7.EraseDer.Step
public import Silmaril.Wasm.SpecTec.Sim.Round7.Swap.Thms

/-!
# Round 7, moving derivations across erasure: `Task.stepErase` from the four excluded rules
(unrefined)

At a configuration in the domain of `Round7.Swap.Task.stepErase` (`StripInj c`, `BoundedSelE c`,
round 6's primitives), the hypotheses of `stepFwd`/`stepBwd` hold on the swap set `QC c`, apart
from the four rules of `Step` that use an excluded name. So:

* `sStepB_QC_fwd`, `sStepB_QC_bwd`: SpecTec's `Step` commutes with erasure at `QC c`, given those
  four rules (`RuleFwd`, `RuleBwd`);
* `stepErase_of_stepExc : Task.stepExc → Round7.Swap.Task.stepErase`, hence `swapEquiv_of_stepExc`
  and `wholeStepValidREI_of_stepExc`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.SpecTec.Sim.Round7.Swap
open Silmaril.Wasm.SpecTec.Sim.Round7.EraseAll (Hyps grB gdB InAI)
open Round6.Reading (DDerivesB otherwiseB SStepB)

variable {H : Type}

section
variable {c : Config H} (hinj : StripInj c) (hnb : NamesBnd c)
  (P : Silmaril.Wasm.Numerics.Profile) (hn : H → String) (host : HostSemantics H)
include hinj hnb

/-- **`Step` at a swap-set input goes to the erased side**, given the four excluded rules. -/
theorem sStepB_QC_fwd
    (hX : ∀ nm ∈ excNames, RuleFwd (QC c) (utf8Env (Round4Int.BI P hn host)) nm) {a w : Value}
    (ha : AllIn (QC c) a) (h : SStepB (utf8Env (Round4Int.BI P hn host)) a w) :
    SStepB (utf8Env (Round4Int.BI P hn host)) (eraseV a) (eraseV w) ∧ AllIn (QC c) w := by
  have HE := EraseAll.hyps_BI hinj P hn host
  obtain ⟨K, hK⟩ := qExp_QC (Round4Int.BI P hn host) hnb
  obtain ⟨h₁, h₂⟩ := stepFwd (EraseAll.hyps_B hinj P hn host) (hyps_eImg_B hinj P hn host)
    (typFwd_gd (typFwd_utf8Env HE)) (typBwd_gd (typBwd_utf8Env HE hK)) hQA_QC hX rfl
    (inAI_of_pair ha) h
  refine ⟨by simpa [SStepB, eraseV, eraseVs_eq_map] using h₁, ?_⟩
  exact EraseAll.ai_tuple.1 h₂ _ (by simp)

/-- **`Step` on the erased side at an erased swap-set input comes back**, given the four excluded
rules. -/
theorem sStepB_QC_bwd
    (hX : ∀ nm ∈ excNames, RuleBwd (QC c) (utf8Env (Round4Int.BI P hn host)) nm) {a w' : Value}
    (ha : AllIn (QC c) a) (h : SStepB (utf8Env (Round4Int.BI P hn host)) (eraseV a) w') :
    AllIn (QC c) (unerase (QC c) w') ∧ eraseV (unerase (QC c) w') = w' ∧
      SStepB (utf8Env (Round4Int.BI P hn host)) a (unerase (QC c) w') := by
  have HE := EraseAll.hyps_BI hinj P hn host
  obtain ⟨K, hK⟩ := qExp_QC (Round4Int.BI P hn host) hnb
  have hB := EraseAll.hyps_B hinj P hn host
  obtain ⟨-, h₂, h₃⟩ := stepBwd hB (hyps_eImg_B hinj P hn host)
    (typFwd_gd (typFwd_utf8Env HE)) (typBwd_gd (typBwd_utf8Env HE hK)) hQA_QC hX rfl
    (inAI_of_pair (allIn_eImg_eraseV a ha)) h
  have hw' : AllIn (EImg (QC c)) w' := EraseAll.ai_tuple.1 h₃ _ (by simp)
  obtain ⟨hu₁, hu₂⟩ := unerase_eImg hQA_QC w' hw'
  refine ⟨hu₁, hu₂, ?_⟩
  rw [unerase_pair hB.inj ha] at h₂
  exact h₂

end

/-- **`Round7.Swap.Task.stepErase` from the four excluded rules.** -/
theorem stepErase_of_stepExc (hE : Task.stepExc) : Task.stepErase := by
  intro H hn hinj host hf hok hb hp nd r c ts hc hs hi
  have hX := hE H hn hinj host hf hok hb hp nd r c ts hc hs hi
  have hnb : NamesBnd c := hs.2
  have ha : AllIn (QC c) (configV hn c) := allIn_configV_of hn fun m hm => Or.inl ⟨m, hm, rfl⟩
  refine ⟨fun w hw => ?_, fun d _ hd => ?_⟩
  · obtain ⟨h₁, h₂⟩ := sStepB_QC_fwd hi hnb _ hn host (fun nm hnm => (hX nm hnm).1) ha hw
    rw [eraseV_configV] at h₁
    exact ⟨h₂, h₁⟩
  · rw [← eraseV_configV] at hd
    obtain ⟨h₁, h₂, h₃⟩ := sStepB_QC_bwd hi hnb _ hn host (fun nm hnm => (hX nm hnm).2) ha hd
    exact ⟨_, h₁, h₂, h₃⟩

/-- **`Round7.Task.swapEquiv` from the four excluded rules.** -/
theorem swapEquiv_of_stepExc (hE : Task.stepExc) : Round7.Task.swapEquiv :=
  swapEquiv_of_stepErase (stepErase_of_stepExc hE)

/-- **`Round7.Task.wholeStepValidREI` from the four excluded rules.** -/
theorem wholeStepValidREI_of_stepExc (hE : Task.stepExc) : Round7.Task.wholeStepValidREI :=
  wholeStepValidREI_of_stepErase (stepErase_of_stepExc hE)

end Silmaril.Wasm.SpecTec.Sim.Round7.EraseDer
