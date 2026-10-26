module

public import Silmaril.Courses.Cambridge.OptimisingCompilers.Liveness
public import Silmaril.Courses.Cambridge.OptimisingCompilers.Runs
public import Mathlib.Data.Fin.VecNotation

/-! # §4 Uses of LVA: data-flow anomalies (notes p. 10; slides p. 69)

"The above warning ['variable `x` may be used before being set'] can be issued
if `x` is live at entry to the procedure" (notes p. 10). If `x` is not live at
the entry, the procedure's behaviour does not depend on the initial value of
`x` (`behaviour_indep_of_not_live_entry`). Because LVA is a safe
over-approximation, some warnings are spurious (slides p. 69, "intentionally
ignoring p!"): `spuriousExample` warns about `x` although no run reads it
uninitialised.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.OptimisingCompilers

namespace Flowgraph

variable {V ι : Type*} [DecidableEq V] (G : Flowgraph V ι)

/-- The warning "variable `x` may be used before it is initialised". -/
def MayBeUninitialised (x : V) : Prop := x ∈ G.live G.entry

/-- Without a warning, the initial value of `x` is irrelevant. -/
theorem behaviour_indep_of_not_live_entry {x : V} (hx : ¬ G.MayBeUninitialised x)
    (env : Env V) (mem : Mem) (v : ℤ) :
    G.ObsEquiv G ⟨G.entry, env, mem⟩ ⟨G.entry, Function.update env x v, mem⟩ := by
  refine G.obsEquiv_of_agree G.liveEquations.least_isSafe ⟨rfl, rfl, fun y hy => ?_⟩
  have hyx : y ≠ x := fun h => hx (h ▸ hy)
  exact (Function.update_of_ne hyx _ _).symm

end Flowgraph

/-- The slide-69 example: `if (p) { x = 42; } … if (p) { print x; }`. -/
def spuriousExample : Flowgraph String (Fin 6) where
  entry := 0
  code := ![.cmp .ne (.var "p") (.imm 0) 1 2,
    .alu2 .mov "x" (.imm 42) 2,
    .cmp .ne (.var "p") (.imm 0) 3 4,
    .print (.var "x") 4,
    .exit [],
    .exit []]

/-- LVA warns about `x` in the slide-69 example … -/
theorem spuriousExample_warns : spuriousExample.MayBeUninitialised "x" := by
  unfold Flowgraph.MayBeUninitialised
  rw [Flowgraph.mem_live_iff_synLive]
  refine .succ (m := 2) (by show (2 : Fin 6) ∈ [1, 2]; simp) (by decide)
    (.succ (m := 3) (by show (3 : Fin 6) ∈ [3, 4]; simp) (by decide) (.ref (by decide)))

/-- … but the warning is spurious: the initial value of `x` never matters. -/
theorem spuriousExample_not_semLive : ¬ spuriousExample.SemLive 0 "x" := by
  rintro ⟨env, mem, v, h⟩
  apply h
  by_cases hp : env "p" = 0
  · refine Flowgraph.obsEquiv_of_step (o := none) (s' := ⟨2, env, mem⟩)
      (t' := ⟨2, Function.update env "x" v, mem⟩) ?_ ?_ ?_
    · simp [Flowgraph.step, Instr.exec, spuriousExample, Cond.eval, Operand.eval, hp]
    · simp [Flowgraph.step, Instr.exec, spuriousExample, Cond.eval, Operand.eval, hp]
    refine Flowgraph.obsEquiv_of_step (o := none) (s' := ⟨4, env, mem⟩)
      (t' := ⟨4, Function.update env "x" v, mem⟩) ?_ ?_ ?_
    · simp [Flowgraph.step, Instr.exec, spuriousExample, Cond.eval, Operand.eval, hp]
    · simp [Flowgraph.step, Instr.exec, spuriousExample, Cond.eval, Operand.eval, hp]
    exact Flowgraph.obsEquiv_of_halted ⟨[], rfl⟩ ⟨[], rfl⟩ rfl rfl
  · refine Flowgraph.obsEquiv_of_step (o := none) (s' := ⟨1, env, mem⟩)
      (t' := ⟨1, Function.update env "x" v, mem⟩) ?_ ?_ ?_
    · simp [Flowgraph.step, Instr.exec, spuriousExample, Cond.eval, Operand.eval, hp]
    · simp [Flowgraph.step, Instr.exec, spuriousExample, Cond.eval, Operand.eval, hp]
    refine Flowgraph.obsEquiv_of_step (o := none) (s' := ⟨2, Function.update env "x" 42, mem⟩)
      (t' := ⟨2, Function.update env "x" 42, mem⟩) ?_ ?_ ⟨rfl, rfl⟩
    · simp [Flowgraph.step, Instr.exec, spuriousExample, Operand.eval, UnOp.eval]
    · simp [Flowgraph.step, Instr.exec, spuriousExample, Operand.eval, UnOp.eval]

end Silmaril.Courses.Cambridge.OptimisingCompilers
