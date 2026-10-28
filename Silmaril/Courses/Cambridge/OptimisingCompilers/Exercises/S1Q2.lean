module

public import Silmaril.Courses.Cambridge.OptimisingCompilers.Liveness
public import Silmaril.Courses.Cambridge.OptimisingCompilers.Runs
public import Mathlib.Data.Fin.VecNotation

/-! # Exercise sheet 1, question 2 (syntactic and semantic liveness)

Source: `cam-optcomp-2025-exercise-sheet-1` in `references.bib`, question 2.


The flowgraph `h`: 0 `ENTRY`; 1 `y = x`; 2 `z = 0`; 3 the loop test
`CMPGT x, #0`; 4 the test `if (0)`, compiled as `CMPNE #0, #0`; 5 `z = z+y`;
6 `x = x-1`; 7 `return z`.

* (a) `lva_h`: the live-in sets.
* (b) The definitions are `Flowgraph.SynLive` and `Flowgraph.SemLive` (notes
  p. 8). `y` is syntactically live in the loop, along the path through the dead
  branch `z = z+y`, but not semantically live, since that branch never runs
  (`y_synLive_not_semLive`).
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.OptimisingCompilers.Exercises.S1Q2

/-- The function `h` of question 2. -/
def h : Flowgraph String (Fin 8) where
  entry := 0
  code := ![.entry 1,
    .alu2 .mov "y" (.var "x") 2,
    .alu2 .mov "z" (.imm 0) 3,
    .cmp .gt (.var "x") (.imm 0) 4 7,
    .cmp .ne (.imm 0) (.imm 0) 5 6,
    .alu .add "z" (.var "z") (.var "y") 6,
    .alu .sub "x" (.var "x") (.imm 1) 3,
    .exit ["z"]]

/-- (a) The live-in sets. -/
theorem lva_h :
    h.lva = ![{"x"}, {"x"}, {"x", "y"}, {"x", "y", "z"}, {"x", "y", "z"}, {"x", "y", "z"},
      {"x", "y", "z"}, {"z"}] := by
  decide +kernel

/-- `h` with the never-taken test `if (0)` replaced by a jump past it. -/
def hJump : Flowgraph String (Fin 8) where
  entry := 0
  code := fun n => if n = 4 then .nop 6 else h.code n

/-- `h` and `hJump` make the same steps from every configuration. -/
theorem h_lockstep_hJump : Flowgraph.IsLockstep h hJump Eq := by
  have hcode : ∀ n, n ≠ 4 → hJump.code n = h.code n := fun n hn => by simp [hJump, hn]
  have hstep : ∀ s : Config String (Fin 8), hJump.step s = h.step s := by
    rintro ⟨pc, env, mem⟩
    by_cases hpc : pc = 4
    · subst hpc
      rfl
    · simp only [Flowgraph.step, hcode pc hpc]
  refine ⟨?_, ?_⟩
  · rintro s t s' o rfl hs
    exact ⟨s', (hstep s).trans hs, rfl⟩
  · rintro s t rfl ⟨rs, hrs⟩
    have hpc : s.pc ≠ 4 := by
      rintro hpc
      rw [hpc] at hrs
      simp [h] at hrs
    refine ⟨⟨rs, (hcode _ hpc).trans hrs⟩, ?_, rfl⟩
    simp only [Flowgraph.resultValues, hcode _ hpc]

/-- (b) `y` is syntactically but not semantically live at the loop test. -/
theorem y_synLive_not_semLive : h.SynLive 3 "y" ∧ ¬ h.SemLive 3 "y" := by
  refine ⟨.succ (m := 4) (by show (4 : Fin 8) ∈ [4, 7]; simp) (by decide)
    (.succ (m := 5) (by show (5 : Fin 8) ∈ [5, 6]; simp) (by decide) (.ref (by decide))), ?_⟩
  rintro ⟨env, mem, v, hne⟩
  apply hne
  have hy : "y" ∉ hJump.lva 3 := by decide +kernel
  have hJ : hJump.ObsEquiv hJump ⟨3, env, mem⟩ ⟨3, Function.update env "y" v, mem⟩ := by
    by_contra hc
    exact hy (hJump.semLive_subset_of_isSafe hJump.lva_isSafe ⟨env, mem, v, hc⟩)
  have e₁ := h_lockstep_hJump.traces_outcomes (s := ⟨3, env, mem⟩) rfl
  have e₂ := h_lockstep_hJump.traces_outcomes (s := ⟨3, Function.update env "y" v, mem⟩) rfl
  exact ⟨e₁.1.trans (hJ.1.trans e₂.1.symm), e₁.2.trans (hJ.2.trans e₂.2.symm)⟩

end Silmaril.Courses.Cambridge.OptimisingCompilers.Exercises.S1Q2
