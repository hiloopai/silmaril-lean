module

public import Silmaril.Raw.Wasm.SpecTec.Sim.Round8.FiresC.Fires
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.FiresC.CheckRead
public import Silmaril.Proofs.Wasm.SpecTec.Sim.Round8.FiresC.CheckStep
public import Silmaril.Wasm.SpecTec.Sim.Round8.RMCode.Thms

/-!
# Round 8, firing across code erasure: `Step_read` without `otherwise`, and `Step`

At round 6's primitives, with round 8's evaluator-level erasure (`CodeErase.EraseAll.hyps_sim`,
no hypothesis left), every rule of `Step_read` without an `otherwise` premise (`relRead`, 75
rules) and every rule of `Step` from 6 on but 7–9 (`relStep`) satisfies `RMCode.FiresEraseD`
(`firesEraseD_read`, `firesEraseD_step`). So `RMCode.RestMSHCQ` follows from `RestMSHCF`, which
asks `FiresEraseD` only for the 28 `Step_read` rules with an `otherwise` premise, and
`Round7.MemSimd.Task.wholeStepValidRM` from `OpenRMRestDPF`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round8.FiresC

open Silmaril.Wasm
open Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

variable {H : Type} (P : Profile) (hn : H → String) (host : HostSemantics H)

theorem stepRead_reach : Round7.Script.stepReach.contains (0, "Step_read") = true := by
  decide +kernel

theorem step_reach : Round7.Script.stepReach.contains (0, "Step") = true := by
  decide +kernel

/-- **The `Step_read` rules without `otherwise` keep firing when the function code is erased.** -/
theorem firesEraseD_read {i : Nat} (hi : i ∈ relRead) :
    RMCode.FiresEraseD (simEnv (Prims.builtins P hn host)) hn "Step_read" i :=
  fun _ _ _ _ h => fires_erase_rel (CodeErase.EraseAll.hyps_sim P hn host) stepRead_reach
    (rel_of_relAt relRead_ok hi) h

/-- **The `Step` rules from 6 on but 7–9 keep firing when the function code is erased.** -/
theorem firesEraseD_step {i : Nat} (hi : i ∈ relStep) :
    RMCode.FiresEraseD (simEnv (Prims.builtins P hn host)) hn "Step" i :=
  fun _ _ _ _ h => fires_erase_rel (CodeErase.EraseAll.hyps_sim P hn host) step_reach
    (rel_of_relAt relStep_ok hi) h

/-- Past the last rule, nothing fires. -/
theorem firesEraseD_step_large {i : Nat} (hi : 36 ≤ i) :
    RMCode.FiresEraseD (simEnv (Prims.builtins P hn host)) hn "Step" i := by
  rintro _ _ _ _ ⟨t, rules, r, hf, hr, -⟩
  have hl : rules.length = 36 := by rw [← rulesOf_eq hf]; exact step_length
  rw [List.getElem?_eq_none (by omega)] at hr
  cases hr

/-- Every `Step` index `RMCode.RestMSHCQ.firesStep` asks for is in `relStep` or past the end. -/
theorem step_cover {i : Nat} (h6 : 6 ≤ i) (h7 : i ≠ 7) (h8 : i ≠ 8) (h9 : i ≠ 9) :
    i ∈ relStep ∨ 36 ≤ i := by
  rcases Nat.lt_or_ge i 36 with h | h
  · left
    have : i = 6 ∨ (10 ≤ i ∧ i < 36) := by omega
    rcases this with rfl | ⟨h₁, h₂⟩
    · simp [relStep]
    · simp only [relStep, List.mem_cons, List.mem_map, List.mem_range]
      exact Or.inr ⟨i - 10, by omega, by omega⟩
  · exact Or.inr h

/-- Every `Step_read` index outside the memory SIMD rules is in `relRead`, in `elseRead`, or past
the end. -/
theorem read_cover (i : Nat) : i ∈ relRead ∨ i ∈ elseRead ∨ 103 ≤ i := by
  rcases Nat.lt_or_ge i 103 with h | h
  · have hall : ∀ j < 103, j ∈ relRead ∨ j ∈ elseRead := by decide
    exact (hall i h).elim Or.inl (fun h' => Or.inr (Or.inl h'))
  · exact Or.inr (Or.inr h)

/-- Past the last rule of `Step_read`, nothing fires. -/
theorem firesEraseD_read_large {i : Nat} (hi : 103 ≤ i) :
    RMCode.FiresEraseD (simEnv (Prims.builtins P hn host)) hn "Step_read" i := by
  rintro _ _ _ _ ⟨t, rules, r, hf, hr, -⟩
  have hl : rules.length = 103 := by rw [← rulesOf_eq hf]; exact stepRead_length
  rw [List.getElem?_eq_none (by omega)] at hr
  cases hr

variable {P hn host}

/-- **`RestMSHCF` gives `RMCode.RestMSHCQ`.** -/
theorem restMSHCQ_of_F (h : RestMSHCF hn P host) : RMCode.RestMSHCQ hn P host where
  pure := h.pure
  read := h.read
  step := h.step
  firesRead i _ := by
    rcases read_cover i with hr | he | hl
    · exact firesEraseD_read P hn host hr
    · exact h.firesRead i he
    · exact firesEraseD_read_large P hn host hl
  firesStep i h6 _ h7 h8 h9 := by
    rcases step_cover h6 h7 h8 h9 with hr | hl
    · exact firesEraseD_step P hn host hr
    · exact firesEraseD_step_large P hn host hl

/-- **`OpenRMRestDPF` gives `RMCode.OpenRMRestDPQ`.** -/
theorem openRMRestDPQ_of_F (O : OpenRMRestDPF hn P host) : RMCode.OpenRMRestDPQ hn P host :=
  ⟨O.forward, restMSHCQ_of_F O.restMSHC, O.castsFwd, O.castsBwd⟩

/-- **`Round7.MemSimd.Task.wholeStepValidRM` from `OpenRMRestDPF`.** -/
theorem wholeStepValidRM_of_restDPF
    (h : ∀ (H : Type) (hn : H → String), Function.Injective hn →
      ∀ (host : HostSemantics H), HostFinite host → HostOk host →
        ∀ (nd : Bool) (r : Silmaril.Wasm.Numerics.RelaxedChoice),
          OpenRMRestDPF hn (Profile.spec nd r) host) :
    Round7.MemSimd.Task.wholeStepValidRM :=
  RMCode.wholeStepValidRM_of_restDPQ fun H hn hinj host hf hh nd r =>
    openRMRestDPQ_of_F (h H hn hinj host hf hh nd r)

end Silmaril.Wasm.SpecTec.Sim.Round8.FiresC
