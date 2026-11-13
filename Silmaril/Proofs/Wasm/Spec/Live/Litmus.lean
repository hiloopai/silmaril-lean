module

public import Silmaril.Proofs.Wasm.Spec.Live.Sound
public import Silmaril.Wasm.Spec.Litmus.Thms
import Mathlib.Tactic.IntervalCases

@[expose] public section

/-!
# Liveness litmus tests

On the loose semantics (`Silmaril.Wasm.Spec.Litmus`):

* `okRun_terminates`: `main` calls `assert(1)` and returns `5`, so it terminates;
* `divRun_not_terminates`: a call of `main` followed by `ret main diverges` (the shape of a
  divergence trace of `wasmDivSem`) refutes termination;
* `chatterRun_not_terminates`: an infinite word calling `main` and then `log` forever (the shape
  of infinite hidden chatter) refutes termination, while `chatterRun_neverCall_assert` shows it
  is safe (`assert` is never called): liveness sees what safety cannot;
* `trapEnv_total`: the environment answering every import call with a trap is total, so the
  closed-world termination theorem applies to it.
-/

namespace Silmaril.Wasm.Spec.Live

open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Spec.Litmus

/-- `main` diverges. -/
def divRun : List (Litmus.Ev X₀) := [.call mainE [], .ret mainE .diverges]

/-- `main` is called and then calls `log` forever. -/
def chatterWord : ℕ → Litmus.Ev X₀ := fun k =>
  if k = 0 then .call mainE [] else if k % 2 = 1 then .icall logI [Val.i32 (BitVec.ofNat 32 k)]
  else .iret logI (.returns [])

/-- The finite prefixes of `chatterWord`. -/
def chatterSet : Set (List (Litmus.Ev X₀)) := {t | ∃ n, t <+: prefixList chatterWord n}

/-- The chatter program of the loose semantics. -/
def chatterRun : (Semantics.ofSets Unit (List Val) (Behaviour Val)).Prog X₀ :=
  ⟨chatterSet, ⟨⟨0, List.nil_prefix⟩, fun ⟨n, hn⟩ hs => ⟨n, hs.trans hn⟩⟩⟩

theorem okRun_terminates :
    Models (ltlMax Unit _ _) Litmus.S (progOf okRun) (responds mainE (· ≠ .diverges)) := by
  rw [models_progOf_iff, ltlMax_prefixesOf_iff, holdsFin_responds_iff]
  intro k hk hc
  have hk' : k < 4 := by simpa [okRun] using hk
  interval_cases k
  · exact ⟨3, Nat.zero_le _, by decide, .returns [Val.i32 5], by simp, rfl⟩
  all_goals
    obtain ⟨a, ha⟩ := hc
    simp [okRun, Event.call, Event.icall, Event.iret, Event.ret] at ha

theorem divRun_not_terminates :
    ¬ Models (ltlMax Unit _ _) Litmus.S (progOf divRun) (responds mainE (· ≠ .diverges)) := by
  rw [models_progOf_iff]
  refine not_sat_responds_of_witness (a := []) (bad := (· = .diverges)) (fun r hr hne => hne hr)
    (.inl ⟨divRun, maximal_prefixesOf_iff.2 rfl, by simp [divRun], fun j r hr => ?_⟩)
  simp only [divRun, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with h | h
  · cases h
  · injection h with h'
    injection h'

theorem chatterRun_not_terminates :
    ¬ Models (ltlMax Unit _ _) Litmus.S chatterRun (responds mainE (· ≠ .diverges)) := by
  rw [models_iff]
  refine not_sat_responds_of_witness (bad := (· = .diverges)) (fun r hr hne => hne hr)
    (.inr ⟨chatterWord, fun n => ⟨n, List.prefix_refl _⟩, ⟨0, rfl⟩, fun k j r => ?_⟩)
  unfold chatterWord
  split_ifs <;> simp [Event.call, Event.icall, Event.iret, Event.ret]

theorem chatterRun_neverCall_assert :
    Models (neverCall Unit _ _) Litmus.S chatterRun assertI := by
  rw [models_iff]
  rintro t ⟨n, hn⟩ a ha
  obtain ⟨k, hk, hkw⟩ := List.getElem_of_mem (hn.subset ha)
  have hw : chatterWord k = Event.icall assertI a := by
    rw [← hkw]
    simp [prefixList]
  unfold chatterWord at hw
  split_ifs at hw <;> simp [Event.icall, Event.iret, assertI, logI] at hw

/-- The trapping environment is total. -/
theorem trapEnv_total (ts : List Silmaril.Wasm.Game.FnType) : Total (trapEnv ts) :=
  fun _ => ⟨.trap, rfl⟩

end Silmaril.Wasm.Spec.Live
