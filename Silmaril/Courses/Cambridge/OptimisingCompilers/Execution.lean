module

public import Silmaril.Courses.Cambridge.OptimisingCompilers.ThreeAddress

/-! # Running concrete flowgraphs

Helper lemmas for executing the course's example flowgraphs symbolically
(§1 semantics, notes pp. 4–6): one lemma per instruction form computing its
step, composition of runs, uniqueness of halting runs (the semantics is
deterministic), and the trace and outcome sets of programs without `print`.
`run_steps` executes straight-line code and branches whose condition `simp`
can decide.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.OptimisingCompilers.Flowgraph

variable {V ι : Type*} [DecidableEq V] {G : Flowgraph V ι} {s s' t : Config V ι}

theorem steps_silent (h : G.step s = some (none, s')) (h' : G.Steps s' [] t) :
    G.Steps s [] t :=
  .head h h'

theorem exists_steps_silent {P : Config V ι → Prop} (h : G.step s = some (none, s'))
    (h' : ∃ t, G.Steps s' [] t ∧ P t) : ∃ t, G.Steps s [] t ∧ P t :=
  let ⟨t, ht, hp⟩ := h'
  ⟨t, steps_silent h ht, hp⟩

theorem exists_steps_congr {P Q : Config V ι → Prop} (h : ∃ t, G.Steps s [] t ∧ P t)
    (hPQ : ∀ t, P t → Q t) : ∃ t, G.Steps s [] t ∧ Q t :=
  let ⟨t, ht, hp⟩ := h
  ⟨t, ht, hPQ t hp⟩

theorem step_alu2 {op : UnOp} {d : V} {a : Operand V} {n : ι}
    (h : G.code s.pc = .alu2 op d a n) :
    G.step s = some (none, ⟨n, Function.update s.env d (op.eval (a.eval s.env)), s.mem⟩) := by
  simp [Flowgraph.step, h, Instr.exec]

theorem step_alu {op : AluOp} {d : V} {a b : Operand V} {n : ι}
    (h : G.code s.pc = .alu op d a b n) :
    G.step s = some (none,
      ⟨n, Function.update s.env d (op.eval (a.eval s.env) (b.eval s.env)), s.mem⟩) := by
  simp [Flowgraph.step, h, Instr.exec]

theorem step_nop {n : ι} (h : G.code s.pc = .nop n) :
    G.step s = some (none, ⟨n, s.env, s.mem⟩) := by
  simp [Flowgraph.step, h, Instr.exec]

theorem step_cmp_true {c : Cond} {a b : Operand V} {tt ff : ι}
    (h : G.code s.pc = .cmp c a b tt ff) (hc : c.eval (a.eval s.env) (b.eval s.env) = true) :
    G.step s = some (none, ⟨tt, s.env, s.mem⟩) := by
  simp [Flowgraph.step, h, Instr.exec, hc]

theorem step_cmp_false {c : Cond} {a b : Operand V} {tt ff : ι}
    (h : G.code s.pc = .cmp c a b tt ff) (hc : c.eval (a.eval s.env) (b.eval s.env) = false) :
    G.step s = some (none, ⟨ff, s.env, s.mem⟩) := by
  simp [Flowgraph.step, h, Instr.exec, hc]

/-- Two halting runs from the same configuration coincide. -/
theorem steps_halted_unique {s t : Config V ι} {w : List ℤ} (h : G.Steps s w t)
    (ht : G.Halted t) :
    ∀ {w' : List ℤ} {t' : Config V ι}, G.Steps s w' t' → G.Halted t' → w = w' ∧ t = t' := by
  revert ht
  induction h with
  | refl s =>
    intro ht w' t' h' ht'
    cases h' with
    | refl => exact ⟨rfl, rfl⟩
    | head hs _ => rw [(G.step_eq_none_iff _).2 ht] at hs; cases hs
  | head hs _ ih =>
    intro ht w' t' h' ht'
    cases h' with
    | refl => rw [(G.step_eq_none_iff _).2 ht'] at hs; cases hs
    | head hs' hrest' =>
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (G.step_deterministic hs hs')
      obtain ⟨rfl, rfl⟩ := ih ht hrest' ht'
      exact ⟨rfl, rfl⟩

/-- A configuration with a halting run has exactly that run's outcome. -/
theorem outcomes_eq_singleton {s t : Config V ι} {w : List ℤ} (h : G.Steps s w t)
    (ht : G.Halted t) : G.outcomes s = {⟨w, G.resultValues t, t.mem⟩} := by
  ext ⟨o₁, o₂, o₃⟩
  simp only [outcomes, Set.mem_ofPred_eq, Set.mem_singleton_iff, Outcome.mk.injEq]
  constructor
  · rintro ⟨t', h', ht', rfl, rfl⟩
    obtain ⟨rfl, rfl⟩ := steps_halted_unique h ht h' ht'
    exact ⟨rfl, rfl, rfl⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨t, h, ht, rfl, rfl⟩

/-- A step from a node that is not a `print` is silent. -/
theorem step_output_eq_none {o : Option ℤ} (hp : ∀ a m, G.code s.pc ≠ .print a m)
    (hs : G.step s = some (o, s')) : o = none := by
  unfold step at hs
  cases hc : G.code s.pc <;>
    simp only [hc, Instr.exec, Option.map_some, Option.map_none, Option.some.injEq,
      Prod.mk.injEq, reduceCtorEq] at hs
  all_goals first | exact hs.1.symm | exact absurd hc (hp _ _)

/-- Runs of a program without `print` are silent. -/
theorem steps_output_nil (hp : ∀ n a m, G.code n ≠ .print a m) {s t : Config V ι}
    {w : List ℤ} (h : G.Steps s w t) : w = [] := by
  induction h with
  | refl => rfl
  | head hs _ ih => simp [step_output_eq_none (hp _) hs, ih]

/-- The only trace of a program without `print` is the empty one. -/
theorem traces_eq_nil (hp : ∀ n a m, G.code n ≠ .print a m) (s : Config V ι) :
    G.traces s = {[]} := by
  ext w
  simp only [traces, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  exact ⟨fun ⟨_, h⟩ => steps_output_nil hp h, fun hw => hw ▸ ⟨s, .refl s⟩⟩

end Silmaril.Courses.Cambridge.OptimisingCompilers.Flowgraph

namespace Silmaril.Courses.Cambridge.OptimisingCompilers

/-- On a goal `∃ t, G.Steps s [] t ∧ P t`, run straight-line and branch steps,
deciding branch conditions by `simp_all` from the hypotheses in context. -/
syntax "run_steps" : tactic

macro_rules
  | `(tactic| run_steps) => `(tactic| repeat (first
      | refine Flowgraph.exists_steps_silent (Flowgraph.step_alu2 rfl) ?_
      | refine Flowgraph.exists_steps_silent (Flowgraph.step_alu rfl) ?_
      | refine Flowgraph.exists_steps_silent (Flowgraph.step_nop rfl) ?_
      | (refine Flowgraph.exists_steps_silent (Flowgraph.step_cmp_true rfl ?_) ?_
         focus
           simp_all [Function.update_apply, Cond.eval, Operand.eval, UnOp.eval, AluOp.eval]
           done)
      | (refine Flowgraph.exists_steps_silent (Flowgraph.step_cmp_false rfl ?_) ?_
         focus
           simp_all [Function.update_apply, Cond.eval, Operand.eval, UnOp.eval, AluOp.eval]
           done)))

/-- Evaluate environment lookups through updates, operands and operations, using
the hypotheses in context. -/
syntax "flow_simp" : tactic

macro_rules
  | `(tactic| flow_simp) =>
    `(tactic| simp_all [Function.update_apply, Cond.eval, Operand.eval, UnOp.eval, AluOp.eval])

end Silmaril.Courses.Cambridge.OptimisingCompilers
