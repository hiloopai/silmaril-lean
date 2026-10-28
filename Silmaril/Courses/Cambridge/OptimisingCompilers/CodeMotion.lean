module

public import Silmaril.Courses.Cambridge.OptimisingCompilers.AvailableExpressions
public import Silmaril.Courses.Cambridge.OptimisingCompilers.Execution
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Basic

/-! # §6 Code motion and partial redundancy elimination (notes pp. 14–15;
slides pp. 79–83)

"Transformations such as CSE are known collectively as code motion
transformations. Another famous one (more general than CSE) is Partial
Redundancy Elimination" (notes p. 14). An expression is *partially redundant*
at `n` if it is available along some but not all paths into `n`: it is in the
*may* version of AVAIL (`partAvail`) but not in the must version (`avail`).
PRE inserts computations so that partially redundant expressions become fully
redundant, and then CSE removes them.

* `partAvail`: the forward may gen/kill problem with AVAIL's gen and kill;
* `anticipated`: the backward must problem "`e` will be computed on every path
  from `n` before any of its operands change" (very busy expressions), which
  tells PRE where insertion is safe;
* `avail_subset_partAvail`: what is available on all paths is available on some;
* `doWhile` is the notes' example; the marked `a+b` is partially redundant
  (`doWhile_partiallyRedundant`), and hoisting one computation before the loop
  makes it fully redundant (`hoisted_fullyRedundant`).
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.OptimisingCompilers

open Silmaril.Semantics.Dataflow

namespace Flowgraph

variable {V ι : Type*} [DecidableEq V] (G : Flowgraph V ι)

/-- Partial availability: AVAIL as a may problem. -/
def partAvailProblem : GenKill ι (Rhs V) where
  nbrs := G.pred
  gen n := (G.code n).gen
  kill n := (G.code n).kill

/-- Expressions available on some path into `n`. -/
noncomputable def partAvail (n : ι) : Set (Rhs V) := G.partAvailProblem.mayIn n

/-- `e` is partially redundant at `n`: available on some but not all paths. -/
def PartiallyRedundant (n : ι) (e : Rhs V) : Prop := e ∈ G.partAvail n ∧ e ∉ G.avail n

/-- `e` is fully redundant at `n`, computed there and available. -/
def FullyRedundant (n : ι) (e : Rhs V) : Prop :=
  e ∈ G.avail n ∧ ∃ x, (G.code n).assignment? = some (x, e)

/-- Anticipated (very busy) expressions: a backward must problem over `succ`.
`n` generates the expression it computes (whether or not it overwrites an
operand, since the use precedes the definition) and kills those whose
operands it defines. -/
def anticipatedProblem : GenKill ι (Rhs V) where
  nbrs := G.succ
  gen n := {e | ∃ x, (G.code n).assignment? = some (x, e)}
  kill n := {e | ∃ x ∈ (G.code n).defs, x ∈ e.vars ∧ ¬ ∃ y, (G.code n).assignment? = some (y, e)}

/-- Expressions anticipated on entry to `n`. -/
noncomputable def anticipated (n : ι) : Set (Rhs V) := G.anticipatedProblem.mustOut n

/-- What is available on all rooted paths is available on some. -/
theorem avail_subset_partAvail {n : ι} (hn : ∃ ps, G.availProblem.IsRootedPath (n :: ps)) :
    G.avail n ⊆ G.partAvail n := by
  intro e he
  obtain ⟨ps, hps⟩ := hn
  cases ps with
  | nil =>
    have h : ¬ (G.availProblem.nbrs n).Nonempty := by
      rw [Set.not_nonempty_iff_eq_empty]; exact hps
    unfold avail GenKill.mustIn at he
    rw [ite_eq_right h] at he
    simp at he
  | cons m ps =>
    obtain ⟨hm, hps'⟩ := hps
    unfold avail GenKill.mustIn at he
    rw [ite_eq_left ⟨m, hm⟩] at he
    have h₁ : e ∈ G.availProblem.mustOut m := Set.mem_iInter₂.1 he m hm
    exact Set.mem_biUnion hm (G.availProblem.mustOut_subset_mayOut ⟨ps, hps'⟩ h₁)

/-- A may fact leaving a predecessor and not killed at `n` leaves `n`. -/
theorem _root_.Silmaril.Semantics.Dataflow.GenKill.mem_mayOut_of_nbr {α : Type*}
    (K : GenKill ι α) {n m : ι} {a : α} (hm : m ∈ K.nbrs n) (ha : a ∈ K.mayOut m)
    (hk : a ∉ K.kill n) : a ∈ K.mayOut n := by
  rw [K.mayOut_eq]
  exact Set.mem_union_left _ (Set.mem_sdiff_of_mem (Set.mem_biUnion hm ha) hk)

/-- A generated fact leaves its node. -/
theorem _root_.Silmaril.Semantics.Dataflow.GenKill.mem_mayOut_of_gen {α : Type*}
    (K : GenKill ι α) {n : ι} {a : α} (ha : a ∈ K.gen n) : a ∈ K.mayOut n := by
  rw [K.mayOut_eq]
  exact Set.mem_union_right _ ha

end Flowgraph

/-- The notes' PRE example (p. 14), with `a+b` at nodes 2 ("here") and 4.
The notes leave the loop condition `while (...)` unspecified; here it is a
counter `p`, an input that the loop decrements, and the exit returns `c` and
`d`, so that the run's outcome depends on the input and on the computed values:
```
0: a = 1          4: d = a+b
1: b = 2          5: p = p-1
2: c = a+b        6: CMPGT p, #0 → 2 / 7
3: a = 7          7: EXIT [c, d]
```
-/
-- The test depends on input `p`, and the exit exposes `c` and `d`, so the
-- equivalence covers observable terminating cases as well as silent loops.
def doWhile : Flowgraph String (Fin 8) where
  entry := 0
  code := ![.alu2 .mov "a" (.imm 1) 1,
    .alu2 .mov "b" (.imm 2) 2,
    .alu .add "c" (.var "a") (.var "b") 3,
    .alu2 .mov "a" (.imm 7) 4,
    .alu .add "d" (.var "a") (.var "b") 5,
    .alu .sub "p" (.var "p") (.imm 1) 6,
    .cmp .gt (.var "p") (.imm 0) 2 7,
    .exit ["c", "d"]]

/-- The marked `a+b` is partially redundant: computed at node 4 on the back edge,
but not on the path from the entry. -/
theorem doWhile_partiallyRedundant :
    doWhile.PartiallyRedundant 2 (.bin .add (.var "a") (.var "b")) := by
  have c1 : doWhile.code 1 = .alu2 .mov "b" (.imm 2) 2 := rfl
  have c4 : doWhile.code 4 = .alu .add "d" (.var "a") (.var "b") 5 := rfl
  have c5 : doWhile.code 5 = .alu .sub "p" (.var "p") (.imm 1) 6 := rfl
  have c6 : doWhile.code 6 = .cmp .gt (.var "p") (.imm 0) 2 7 := rfl
  constructor
  · have h4 : (.bin .add (.var "a") (.var "b") : Rhs String) ∈ doWhile.partAvailProblem.mayOut 4 :=
      GenKill.mem_mayOut_of_gen _ (Instr.mem_gen.2 ⟨"d", by rw [c4]; rfl,
        by simp [Rhs.vars, Operand.vars]⟩)
    have h5 := GenKill.mem_mayOut_of_nbr doWhile.partAvailProblem (n := 5) (m := 4) (show (5 : Fin 8) ∈ (doWhile.code 4).succs by
      rw [c4]; simp [Instr.succs]) h4 (fun hk => by
        obtain ⟨x, hx, hv⟩ := Instr.mem_kill.1 hk
        rw [c5] at hx
        simp [Instr.defs] at hx
        subst hx
        simp [Rhs.vars, Operand.vars] at hv)
    have h6 := GenKill.mem_mayOut_of_nbr doWhile.partAvailProblem (n := 6) (m := 5) (show (6 : Fin 8) ∈ (doWhile.code 5).succs by
      rw [c5]; simp [Instr.succs]) h5 (fun hk => by
        obtain ⟨x, hx, -⟩ := Instr.mem_kill.1 hk
        rw [c6] at hx
        simp [Instr.defs] at hx)
    exact Set.mem_biUnion (show (6 : Fin 8) ∈ doWhile.pred 2 from
      show (2 : Fin 8) ∈ (doWhile.code 6).succs by rw [c6]; simp [Instr.succs]) h6
  · intro he
    have h12 : (1 : Fin 8) ∈ doWhile.availProblem.nbrs 2 :=
      show (2 : Fin 8) ∈ (doWhile.code 1).succs by rw [c1]; simp [Instr.succs]
    unfold Flowgraph.avail GenKill.mustIn at he
    rw [ite_eq_left ⟨_, h12⟩] at he
    have h1 := Set.mem_iInter₂.1 he 1 h12
    rw [GenKill.mustOut_eq] at h1
    rcases h1 with ⟨-, hk⟩ | hg
    · exact hk (Instr.mem_kill.2 ⟨"b", by rw [c1]; simp [Instr.defs],
        by simp [Rhs.vars, Operand.vars]⟩)
    · obtain ⟨d, hd, -⟩ := Instr.mem_gen.1 hg
      rw [c1] at hd
      simp [Instr.assignment?] at hd

/-- The transformed program (notes p. 15), with `e = a+b` hoisted before the
loop as node 2 and the loop body starting at node 3. -/
def doWhileHoisted : Flowgraph String (Fin 9) where
  entry := 0
  code := ![.alu2 .mov "a" (.imm 1) 1,
    .alu2 .mov "b" (.imm 2) 2,
    .alu .add "e" (.var "a") (.var "b") 3,
    .alu .add "c" (.var "a") (.var "b") 4,
    .alu2 .mov "a" (.imm 7) 5,
    .alu .add "d" (.var "a") (.var "b") 6,
    .alu .sub "p" (.var "p") (.imm 1) 7,
    .cmp .gt (.var "p") (.imm 0) 3 8,
    .exit ["c", "d"]]

/-- After hoisting, the marked `a+b` (now node 3) is fully redundant, so CSE
can remove it. -/
theorem hoisted_fullyRedundant :
    doWhileHoisted.FullyRedundant 3 (.bin .add (.var "a") (.var "b")) := by
  refine ⟨?_, "c", rfl⟩
  classical
  let x : Fin 9 → Set (Rhs String) := fun n =>
    if n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 7 ∨ n = 8 then {.bin .add (.var "a") (.var "b")} else ∅
  have hgen : ∀ p : Fin 9, (p = 2 ∨ p = 3 ∨ p = 5) →
      (.bin .add (.var "a") (.var "b") : Rhs String) ∈ (doWhileHoisted.code p).gen := by
    rintro p (rfl | rfl | rfl)
    · exact Instr.mem_gen.2 ⟨"e", rfl, by simp [Rhs.vars, Operand.vars]⟩
    · exact Instr.mem_gen.2 ⟨"c", rfl, by simp [Rhs.vars, Operand.vars]⟩
    · exact Instr.mem_gen.2 ⟨"d", rfl, by simp [Rhs.vars, Operand.vars]⟩
  have hpred : ∀ n p : Fin 9, (n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 7 ∨ n = 8) →
      n ∈ (doWhileHoisted.code p).succs → (p = 2 ∨ p = 3 ∨ p = 5) ∨ p = 6 ∨ p = 7 := by
    decide
  have hne : ∀ n : Fin 9, (n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 7 ∨ n = 8) →
      ∃ p, n ∈ (doWhileHoisted.code p).succs := by
    decide
  have c6 : doWhileHoisted.code 6 = .alu .sub "p" (.var "p") (.imm 1) 7 := rfl
  have c7 : doWhileHoisted.code 7 = .cmp .gt (.var "p") (.imm 0) 3 8 := rfl
  refine doWhileHoisted.le_avail (x := x) (fun n => ?_) 3 (by simp [x])
  by_cases hS : n = 3 ∨ n = 4 ∨ n = 6 ∨ n = 7 ∨ n = 8
  · obtain ⟨p₀, hp₀⟩ := hne n hS
    have hne' : (doWhileHoisted.pred n).Nonempty := ⟨p₀, hp₀⟩
    rw [ite_eq_left hne']
    simp only [x, ite_eq_left hS]
    rw [Set.singleton_subset_iff, Set.mem_iInter₂]
    intro p hp
    rcases hpred n p hS hp with hg | rfl | rfl
    · exact Set.mem_union_right _ (hgen p hg)
    · refine Set.mem_union_left _ (Set.mem_sdiff_of_mem (by simp) fun hk => ?_)
      obtain ⟨y, hy, hv⟩ := Instr.mem_kill.1 hk
      rw [c6] at hy
      simp [Instr.defs] at hy
      subst hy
      simp [Rhs.vars, Operand.vars] at hv
    · refine Set.mem_union_left _ (Set.mem_sdiff_of_mem (by simp) fun hk => ?_)
      obtain ⟨y, hy, -⟩ := Instr.mem_kill.1 hk
      rw [c7] at hy
      simp [Instr.defs] at hy
  · simp only [x, ite_eq_right hS]
    exact Set.empty_subset _

/-- The loop of `doWhile` from its head: it exits with `c = 9` if it iterates
more than once and `c = a + 2` otherwise, and `d = 9`. -/
theorem doWhile_loop (mem : Mem) : ∀ (k : ℕ) (env : Env String), env "b" = 2 →
    env "p" ≤ (k : ℤ) + 1 →
    ∃ t, doWhile.Steps ⟨2, env, mem⟩ [] t ∧ (t.pc = 7 ∧
      t.env "c" = (if 1 < env "p" then 9 else env "a" + 2) ∧ t.env "d" = 9 ∧ t.mem = mem) := by
  intro k
  induction k with
  | zero =>
    intro env hb hk
    have hp : ¬ 1 < env "p" := by omega
    refine Flowgraph.exists_steps_silent (Flowgraph.step_alu rfl) ?_
    refine Flowgraph.exists_steps_silent (Flowgraph.step_alu2 rfl) ?_
    refine Flowgraph.exists_steps_silent (Flowgraph.step_alu rfl) ?_
    refine Flowgraph.exists_steps_silent (Flowgraph.step_alu rfl) ?_
    refine Flowgraph.exists_steps_silent (Flowgraph.step_cmp_false rfl (by flow_simp)) ?_
    exact ⟨_, .refl _, rfl, by flow_simp, by flow_simp, rfl⟩
  | succ k ih =>
    intro env hb hk
    by_cases hp : 1 < env "p"
    · refine Flowgraph.exists_steps_silent (Flowgraph.step_alu rfl) ?_
      refine Flowgraph.exists_steps_silent (Flowgraph.step_alu2 rfl) ?_
      refine Flowgraph.exists_steps_silent (Flowgraph.step_alu rfl) ?_
      refine Flowgraph.exists_steps_silent (Flowgraph.step_alu rfl) ?_
      refine Flowgraph.exists_steps_silent (Flowgraph.step_cmp_true rfl (by flow_simp)) ?_
      refine Flowgraph.exists_steps_congr (ih _ ?_ ?_) ?_
      · flow_simp
      · simp only [Function.update_apply, String.reduceEq, ↓reduceIte, Operand.eval,
          AluOp.eval]
        omega
      · rintro t ⟨hpc, hc, hd, hm⟩
        refine ⟨hpc, ?_, hd, hm⟩
        rw [hc]
        flow_simp
    · refine Flowgraph.exists_steps_silent (Flowgraph.step_alu rfl) ?_
      refine Flowgraph.exists_steps_silent (Flowgraph.step_alu2 rfl) ?_
      refine Flowgraph.exists_steps_silent (Flowgraph.step_alu rfl) ?_
      refine Flowgraph.exists_steps_silent (Flowgraph.step_alu rfl) ?_
      refine Flowgraph.exists_steps_silent (Flowgraph.step_cmp_false rfl (by flow_simp)) ?_
      exact ⟨_, .refl _, rfl, by flow_simp, by flow_simp, rfl⟩

/-- The loop of `doWhileHoisted` from its head: it exits with `c = 9` if it iterates
more than once and `c = a + 2` otherwise, and `d = 9`. -/
theorem doWhileHoisted_loop (mem : Mem) : ∀ (k : ℕ) (env : Env String), env "b" = 2 →
    env "p" ≤ (k : ℤ) + 1 →
    ∃ t, doWhileHoisted.Steps ⟨3, env, mem⟩ [] t ∧ (t.pc = 8 ∧
      t.env "c" = (if 1 < env "p" then 9 else env "a" + 2) ∧ t.env "d" = 9 ∧ t.mem = mem) := by
  intro k
  induction k with
  | zero =>
    intro env hb hk
    have hp : ¬ 1 < env "p" := by omega
    refine Flowgraph.exists_steps_silent (Flowgraph.step_alu rfl) ?_
    refine Flowgraph.exists_steps_silent (Flowgraph.step_alu2 rfl) ?_
    refine Flowgraph.exists_steps_silent (Flowgraph.step_alu rfl) ?_
    refine Flowgraph.exists_steps_silent (Flowgraph.step_alu rfl) ?_
    refine Flowgraph.exists_steps_silent (Flowgraph.step_cmp_false rfl (by flow_simp)) ?_
    exact ⟨_, .refl _, rfl, by flow_simp, by flow_simp, rfl⟩
  | succ k ih =>
    intro env hb hk
    by_cases hp : 1 < env "p"
    · refine Flowgraph.exists_steps_silent (Flowgraph.step_alu rfl) ?_
      refine Flowgraph.exists_steps_silent (Flowgraph.step_alu2 rfl) ?_
      refine Flowgraph.exists_steps_silent (Flowgraph.step_alu rfl) ?_
      refine Flowgraph.exists_steps_silent (Flowgraph.step_alu rfl) ?_
      refine Flowgraph.exists_steps_silent (Flowgraph.step_cmp_true rfl (by flow_simp)) ?_
      refine Flowgraph.exists_steps_congr (ih _ ?_ ?_) ?_
      · flow_simp
      · simp only [Function.update_apply, String.reduceEq, ↓reduceIte, Operand.eval,
          AluOp.eval]
        omega
      · rintro t ⟨hpc, hc, hd, hm⟩
        refine ⟨hpc, ?_, hd, hm⟩
        rw [hc]
        flow_simp
    · refine Flowgraph.exists_steps_silent (Flowgraph.step_alu rfl) ?_
      refine Flowgraph.exists_steps_silent (Flowgraph.step_alu2 rfl) ?_
      refine Flowgraph.exists_steps_silent (Flowgraph.step_alu rfl) ?_
      refine Flowgraph.exists_steps_silent (Flowgraph.step_alu rfl) ?_
      refine Flowgraph.exists_steps_silent (Flowgraph.step_cmp_false rfl (by flow_simp)) ?_
      exact ⟨_, .refl _, rfl, by flow_simp, by flow_simp, rfl⟩

/-- Hoisting preserves behaviour: for every input both programs halt with the
same results (`c = 3` if `p ≤ 1` initially, else `c = 9`; always `d = 9`), the
hoisted `e` being invisible at the exit. -/
theorem doWhileHoisted_equiv (env : Env String) (mem : Mem) :
    doWhile.traces ⟨0, env, mem⟩ = doWhileHoisted.traces ⟨0, env, mem⟩ ∧
      doWhile.outcomes ⟨0, env, mem⟩ = doWhileHoisted.outcomes ⟨0, env, mem⟩ := by
  have hp₁ : ∀ n a m, doWhile.code n ≠ .print a m := by
    have key : ∀ n : Fin 8,
        (match doWhile.code n with | .print _ _ => true | _ => false) = false := by decide
    intro n a m h
    have := key n
    rw [h] at this
    cases this
  have hp₂ : ∀ n a m, doWhileHoisted.code n ≠ .print a m := by
    have key : ∀ n : Fin 9,
        (match doWhileHoisted.code n with | .print _ _ => true | _ => false) = false := by decide
    intro n a m h
    have := key n
    rw [h] at this
    cases this
  refine ⟨by rw [Flowgraph.traces_eq_nil hp₁, Flowgraph.traces_eq_nil hp₂], ?_⟩
  have htn := Int.self_le_toNat (env "p")
  obtain ⟨t₁, h₁, hpc₁, hc₁, hd₁, hm₁⟩ : ∃ t, doWhile.Steps ⟨0, env, mem⟩ [] t ∧ (t.pc = 7 ∧
      t.env "c" = (if 1 < env "p" then 9 else 3) ∧ t.env "d" = 9 ∧ t.mem = mem) := by
    refine Flowgraph.exists_steps_silent (Flowgraph.step_alu2 rfl) ?_
    refine Flowgraph.exists_steps_silent (Flowgraph.step_alu2 rfl) ?_
    refine Flowgraph.exists_steps_congr (doWhile_loop mem (env "p").toNat _ ?_ ?_) ?_
    · flow_simp
    · simp only [Function.update_apply, String.reduceEq, ↓reduceIte]
      omega
    · rintro t ⟨hpc, hc, hd, hm⟩
      refine ⟨hpc, ?_, hd, hm⟩
      rw [hc]
      flow_simp
  obtain ⟨t₂, h₂, hpc₂, hc₂, hd₂, hm₂⟩ : ∃ t, doWhileHoisted.Steps ⟨0, env, mem⟩ [] t ∧
      (t.pc = 8 ∧ t.env "c" = (if 1 < env "p" then 9 else 3) ∧ t.env "d" = 9 ∧
        t.mem = mem) := by
    refine Flowgraph.exists_steps_silent (Flowgraph.step_alu2 rfl) ?_
    refine Flowgraph.exists_steps_silent (Flowgraph.step_alu2 rfl) ?_
    refine Flowgraph.exists_steps_silent (Flowgraph.step_alu rfl) ?_
    refine Flowgraph.exists_steps_congr (doWhileHoisted_loop mem (env "p").toNat _ ?_ ?_) ?_
    · flow_simp
    · simp only [Function.update_apply, String.reduceEq, ↓reduceIte]
      omega
    · rintro t ⟨hpc, hc, hd, hm⟩
      refine ⟨hpc, ?_, hd, hm⟩
      rw [hc]
      flow_simp
  have c₁ : doWhile.code 7 = .exit ["c", "d"] := rfl
  have c₂ : doWhileHoisted.code 8 = .exit ["c", "d"] := rfl
  rw [Flowgraph.outcomes_eq_singleton h₁ ⟨["c", "d"], by rw [hpc₁]; rfl⟩,
    Flowgraph.outcomes_eq_singleton h₂ ⟨["c", "d"], by rw [hpc₂]; rfl⟩]
  simp [Flowgraph.resultValues, hpc₁, hpc₂, c₁, c₂, hc₁, hc₂, hd₁, hd₂, hm₁, hm₂]

end Silmaril.Courses.Cambridge.OptimisingCompilers
