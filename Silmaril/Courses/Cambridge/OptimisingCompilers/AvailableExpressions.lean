module

public import Silmaril.Courses.Cambridge.OptimisingCompilers.ThreeAddress
public import Silmaril.Semantics.Dataflow.GenKill

/-! # §3 Available expressions (notes pp. 9–10; slides pp. 60–67)

"An expression `e` (typically the RHS of a 3-address instruction) is available
at node `n` if on every path leading to `n` the expression `e` has been
evaluated and not invalidated by an intervening assignment to a variable
occurring in `e`" (notes p. 9). The equations are

  `avail(n) = ⋂ p ∈ pred(n), (avail(p) \ kill(p) ∪ gen(p))`  if `pred(n) ≠ {}`,
  `avail(n) = {}`                                          if `pred(n) = {}`,

and we want their *greatest* solution. This is the must instance of the generic
gen/kill problem `Silmaril.Semantics.Dataflow.GenKill`, i.e. the framework over the order
dual `(Set (Rhs V))ᵒᵈ`, where `⨆` is `⋂` and the least solution is the
greatest one. `gen(x = x+z) = {}` (notes p. 9, footnote 2): an instruction that
overwrites one of its own operands does not make its RHS available.

Main results: `avail_isSolution` (the greatest solution solves the equations)
and `avail_sound` (an available expression is computed, and not killed since,
on every path from a node without predecessors).
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.OptimisingCompilers

open Silmaril.Semantics.Dataflow

/-- Right-hand sides of 3-address instructions: the expressions of AVAIL. -/
inductive Rhs (V : Type*) where
  | bin (op : AluOp) (a b : Operand V)
  | un (op : UnOp) (a : Operand V)
  deriving DecidableEq

namespace Rhs

variable {V : Type*} [DecidableEq V]

/-- Variables occurring in an expression. -/
def vars : Rhs V → Finset V
  | .bin _ a b => a.vars ∪ b.vars
  | .un _ a => a.vars

/-- The value of an expression. -/
def eval (env : Env V) : Rhs V → ℤ
  | .bin op a b => op.eval (a.eval env) (b.eval env)
  | .un op a => op.eval (a.eval env)

theorem _root_.Silmaril.Courses.Cambridge.OptimisingCompilers.Operand.eval_update_of_not_mem
    {x : V} {o : Operand V} (h : x ∉ o.vars) (v : ℤ) (env : Env V) :
    o.eval (Function.update env x v) = o.eval env := by
  cases o with
  | var y =>
    simp only [Operand.vars, Finset.mem_singleton] at h
    simp [Operand.eval, Function.update_of_ne (Ne.symm h)]
  | imm k => rfl

/-- Updating a variable not occurring in an expression leaves its value unchanged. -/
theorem eval_update_of_not_mem {x : V} {e : Rhs V} (h : x ∉ e.vars) (v : ℤ) (env : Env V) :
    e.eval (Function.update env x v) = e.eval env := by
  cases e with
  | bin op a b =>
    simp only [vars, Finset.mem_union, not_or] at h
    simp [eval, Operand.eval_update_of_not_mem h.1, Operand.eval_update_of_not_mem h.2]
  | un op a =>
    simp only [vars] at h
    simp [eval, Operand.eval_update_of_not_mem h]

end Rhs

namespace Instr

variable {V ι : Type*} [DecidableEq V]

/-- The defining assignment `dst := rhs` of an ALU instruction. -/
def assignment? : Instr V ι → Option (V × Rhs V)
  | .alu op d a b _ => some (d, .bin op a b)
  | .alu2 op d a _ => some (d, .un op a)
  | _ => none

/-- `gen(n)`: the expression freshly computed at `n`, unless `n` overwrites one of
its operands (notes p. 9). -/
def gen (i : Instr V ι) : Set (Rhs V) :=
  {e | ∃ d, i.assignment? = some (d, e) ∧ d ∉ e.vars}

/-- `kill(n)`: all expressions containing a variable updated at `n`. -/
def kill (i : Instr V ι) : Set (Rhs V) := {e | ∃ x ∈ i.defs, x ∈ e.vars}

theorem mem_gen {i : Instr V ι} {e : Rhs V} :
    e ∈ i.gen ↔ ∃ d, i.assignment? = some (d, e) ∧ d ∉ e.vars := Iff.rfl

theorem mem_kill {i : Instr V ι} {e : Rhs V} : e ∈ i.kill ↔ ∃ x ∈ i.defs, x ∈ e.vars :=
  Iff.rfl

/-- An instruction generating `e` defines no variable of `e`. -/
theorem not_mem_vars_of_mem_gen {i : Instr V ι} {e : Rhs V} (h : e ∈ i.gen) :
    ∀ x ∈ i.defs, x ∉ e.vars := by
  obtain ⟨d, hd, hde⟩ := mem_gen.1 h
  cases i <;> simp [assignment?] at hd <;> obtain ⟨rfl, rfl⟩ := hd <;> simpa [defs] using hde

end Instr

namespace Flowgraph

variable {V ι : Type*} [DecidableEq V] (G : Flowgraph V ι)

/-- AVAIL as a forward must gen/kill problem over `pred` (notes p. 9). -/
def availProblem : GenKill ι (Rhs V) where
  nbrs := G.pred
  gen n := (G.code n).gen
  kill n := (G.code n).kill

/-- `avail(n)`: the greatest solution of the AVAIL equations, on entry to `n`
(notes p. 10: "we wish the greatest solution"). -/
noncomputable def avail (n : ι) : Set (Rhs V) := G.availProblem.mustIn n

open Classical in
/-- The greatest solution solves the AVAIL equations of notes p. 9. -/
theorem avail_isSolution (n : ι) :
    G.avail n = if (G.pred n).Nonempty then
      ⋂ p ∈ G.pred n, (G.avail p \ (G.code p).kill ∪ (G.code p).gen) else ∅ := by
  have e : ∀ m, G.availProblem.mustOut m = G.avail m \ (G.code m).kill ∪ (G.code m).gen :=
    fun m => G.availProblem.mustOut_eq m
  show (if (G.pred n).Nonempty then ⋂ m ∈ G.pred n, G.availProblem.mustOut m else ∅) = _
  simp only [e]

open Classical in
/-- Every solution of the AVAIL equations lies below the greatest one. -/
theorem le_avail {x : ι → Set (Rhs V)}
    (hx : ∀ n, x n ⊆ if (G.pred n).Nonempty then
      ⋂ p ∈ G.pred n, (x p \ (G.code p).kill ∪ (G.code p).gen) else ∅) (n : ι) :
    x n ⊆ G.avail n := by
  have hy : ∀ m, (x m \ (G.code m).kill ∪ (G.code m).gen) ⊆
      (if (G.availProblem.nbrs m).Nonempty then
        ⋂ k ∈ G.availProblem.nbrs m, (x k \ (G.code k).kill ∪ (G.code k).gen) else ∅) \
        G.availProblem.kill m ∪ G.availProblem.gen m :=
    fun m => Set.union_subset_union_left _ (Set.sdiff_subset_sdiff_left (hx m))
  have hle := fun m => G.availProblem.le_mustOut hy m
  refine (hx n).trans ?_
  show _ ⊆ (if (G.pred n).Nonempty then ⋂ m ∈ G.pred n, G.availProblem.mustOut m else ∅)
  split_ifs
  · exact Set.iInter₂_mono fun m _ => hle m
  · exact Set.Subset.rfl

/-- Soundness of AVAIL, path form (notes p. 9): if `e` is available at `n`, then
along every path `p₀ → ⋯ → pₖ → n` from a node `p₀` without predecessors
(listed from `pₖ` back to `p₀`), some `pᵢ` generates `e` and no later node
kills it. -/
theorem avail_sound {n : ι} {e : Rhs V} (he : e ∈ G.avail n) {p : ι} (hp : p ∈ G.pred n)
    {ps : List ι} (hps : G.availProblem.IsRootedPath (p :: ps)) :
    G.availProblem.HoldsAlong e (p :: ps) := by
  have hne : (G.availProblem.nbrs n).Nonempty := ⟨p, hp⟩
  have he' := he
  unfold avail GenKill.mustIn at he'
  rw [ite_eq_left hne] at he'
  exact G.availProblem.mustOut_holdsAlong (Set.mem_iInter₂.1 he' p hp) hps

/-- Extending a run by one silent or printing step. -/
theorem steps_append_step {a b c : Config V ι} {w : List ℤ} {o : Option ℤ}
    (h : G.Steps a w b) (hs : G.step b = some (o, c)) : G.Steps a (w ++ o.toList) c := by
  revert hs
  induction h with
  | refl s => intro hs; simpa using Steps.head hs (Steps.refl c)
  | head h₁ _ ih => intro hs; simpa [List.append_assoc] using Steps.head h₁ (ih hs)

/-- Induction over the configurations reachable from `start`. -/
theorem steps_reach_induction {start : Config V ι} (P : Config V ι → Prop) (h0 : P start)
    (hstep : ∀ {w b o c}, G.Steps start w b → P b → G.step b = some (o, c) → P c)
    {w : List ℤ} {s : Config V ι} (h : G.Steps start w s) : P s := by
  suffices ∀ {a w' s}, G.Steps a w' s → ∀ w₀, G.Steps start w₀ a → P a → P s from
    this h [] (.refl _) h0
  intro a w' s h'
  induction h' with
  | refl s => exact fun _ _ hp => hp
  | head h₁ _ ih => exact fun w₀ hst hp => ih _ (G.steps_append_step hst h₁) (hstep hst hp h₁)

/-- A step moves to a successor of the current node. -/
theorem step_pc_mem_succs {b c : Config V ι} {o : Option ℤ} (hs : G.step b = some (o, c)) :
    c.pc ∈ (G.code b.pc).succs := by
  unfold step at hs
  cases hc : G.code b.pc <;>
    simp only [hc, Instr.exec, Option.map_some, Option.map_none, Option.some.injEq,
      Prod.mk.injEq, reduceCtorEq] at hs <;>
    obtain ⟨-, rfl⟩ := hs <;> simp only [Instr.succs] <;>
    first | (simp; done) | (split <;> simp)

/-- A step that defines no variable of `e` leaves the value of `e` unchanged. -/
theorem eval_step_of_disjoint {b c : Config V ι} {o : Option ℤ} (hs : G.step b = some (o, c))
    {e : Rhs V} (he : ∀ x ∈ (G.code b.pc).defs, x ∉ e.vars) : e.eval c.env = e.eval b.env := by
  unfold step at hs
  cases hc : G.code b.pc <;>
    simp only [hc, Instr.exec, Option.map_some, Option.map_none, Option.some.injEq,
      Prod.mk.injEq, reduceCtorEq] at hs <;>
    obtain ⟨-, rfl⟩ := hs <;>
    first
      | rfl
      | exact Rhs.eval_update_of_not_mem (he _ (by simp [hc, Instr.defs])) _ _

/-- Semantic soundness: at any configuration reached from an entry
configuration at a node `n`, an available expression `e` was computed earlier
on the run, by a node generating `e`, in a state where it had the value it has
now. -/
theorem avail_sound_semantic {n : ι} {e : Rhs V} (he : e ∈ G.avail n) (hentry : G.pred G.entry = ∅)
    {env : Env V} {mem : Mem} {w : List ℤ} {s : Config V ι}
    (hrun : G.Steps ⟨G.entry, env, mem⟩ w s) (hs : s.pc = n) :
    ∃ (w₁ w₂ : List ℤ) (t : Config V ι), G.Steps ⟨G.entry, env, mem⟩ w₁ t ∧ G.Steps t w₂ s ∧
      e ∈ (G.code t.pc).gen ∧ e.eval t.env = e.eval s.env := by
  subst hs
  refine G.steps_reach_induction (fun s => ∀ e ∈ G.avail s.pc, ∃ (w₁ w₂ : List ℤ)
    (t : Config V ι), G.Steps ⟨G.entry, env, mem⟩ w₁ t ∧ G.Steps t w₂ s ∧
      e ∈ (G.code t.pc).gen ∧ e.eval t.env = e.eval s.env) ?_ ?_ hrun e he
  · intro e he
    have h : ¬ (G.availProblem.nbrs G.entry).Nonempty := by
      rw [Set.not_nonempty_iff_eq_empty]; exact hentry
    unfold avail GenKill.mustIn at he
    rw [ite_eq_right h] at he
    simp at he
  · intro w b o c hb ih hs e he
    have hp : b.pc ∈ G.availProblem.nbrs c.pc := G.step_pc_mem_succs hs
    have he' := he
    unfold avail GenKill.mustIn at he'
    rw [ite_eq_left ⟨_, hp⟩] at he'
    have hout : e ∈ G.availProblem.mustOut b.pc := Set.mem_iInter₂.1 he' b.pc hp
    rw [GenKill.mustOut_eq] at hout
    rcases hout with ⟨hin, hkill⟩ | hgen
    · obtain ⟨w₁, w₂, t, h₁, h₂, h₃, h₄⟩ := ih e hin
      refine ⟨w₁, w₂ ++ o.toList, t, h₁, G.steps_append_step h₂ hs, h₃, ?_⟩
      rw [h₄, G.eval_step_of_disjoint hs (fun x hx hv => hkill (Instr.mem_kill.2 ⟨x, hx, hv⟩))]
    · exact ⟨w, o.toList, b, hb, G.steps_append_step (.refl b) hs, hgen,
        (G.eval_step_of_disjoint hs (Instr.not_mem_vars_of_mem_gen hgen)).symm⟩

end Flowgraph

end Silmaril.Courses.Cambridge.OptimisingCompilers
