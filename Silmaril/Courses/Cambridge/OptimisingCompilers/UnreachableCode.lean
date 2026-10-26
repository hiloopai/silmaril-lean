module

public import Silmaril.Courses.Cambridge.OptimisingCompilers.Runs
public import Silmaril.Semantics.Dataflow.Framework
public import Mathlib.Logic.Relation
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Fin

/-! # §1.2–1.3 Unreachable-code and unreachable-procedure elimination
(notes p. 7; slides pp. 47–53)

*Unreachable-code elimination* (notes §1.2): "mark entry node of each procedure
as reachable; mark every successor of a marked node as reachable and repeat
until no further marks are required". This is the least solution of a forward
dataflow problem over the two-point lattice `Prop`, an instance of
`Silmaril.Semantics.Dataflow.Equations`. The analysis is safe (`reachable_of_steps`):
every node that execution reaches is marked. The converse fails
(`if tautology(x) then C₁ else C₂`, `exists_marked_not_executed`).

The transformation replaces unmarked nodes by `EXIT`; since they are never
executed, behaviour from the entry is unchanged (`eraseUnreachable_obsEquiv`).

*Unreachable-procedure elimination* (notes §1.3) is the same analysis on the
call graph, starting from `main`.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.OptimisingCompilers

open Silmaril.Semantics.Dataflow

namespace Flowgraph

variable {V ι : Type*} (G : Flowgraph V ι)

/-- The reachability equations: `reach(n) = (n = entry) ∨ ∃ p ∈ pred(n), reach(p)`. -/
def reachEquations : Equations ι Prop where
  nbrs := G.pred
  transfer n :=
    { toFun := fun P => n = G.entry ∨ P
      monotone' := fun _ _ h hp => hp.imp_right h }

/-- The marked (reachable) nodes: the least solution. -/
noncomputable def reachable : ι → Prop := G.reachEquations.least

/-- The marked nodes are those reachable along flowgraph edges from the entry. -/
theorem reachable_iff (n : ι) :
    G.reachable n ↔ Relation.ReflTransGen (fun a b => b ∈ G.succ a) G.entry n := by
  have hsol := (Equations.isSolution_iff _ _).1 G.reachEquations.least_isSolution
  constructor
  · intro h
    have hle : G.reachable ≤ fun n => Relation.ReflTransGen (fun a b => b ∈ G.succ a) G.entry n := by
      refine G.reachEquations.least_le_of_isSafe fun m hm => ?_
      simp only [Equations.step_apply, Equations.join, reachEquations,
        iSup_Prop_eq, exists_prop] at hm
      rcases hm with rfl | ⟨p, hp, hr⟩
      · exact .refl
      · exact hr.tail hp
    exact hle n h
  · intro h
    induction h with
    | refl =>
      show G.reachEquations.least G.entry
      rw [hsol]
      exact Or.inl rfl
    | @tail a b _ hab ih =>
      show G.reachEquations.least b
      rw [hsol]
      simp only [Equations.join, reachEquations, iSup_Prop_eq, exists_prop]
      exact Or.inr ⟨a, hab, ih⟩

theorem reachable_of_reachable_succ {a b : ι} (ha : G.reachable a) (hab : b ∈ G.succ a) :
    G.reachable b :=
  (G.reachable_iff b).2 (((G.reachable_iff a).1 ha).tail hab)

variable [DecidableEq V]

/-- Safety (notes p. 7): "every node to which execution may flow at execution
will be marked by the algorithm". -/
theorem reachable_of_steps {env : Env V} {mem : Mem} {w : List ℤ} {s : Config V ι}
    (h : G.Steps ⟨G.entry, env, mem⟩ w s) : G.reachable s.pc := by
  refine (G.reachable_iff _).2 ?_
  have key : ∀ {s t : Config V ι} {w : List ℤ}, G.Steps s w t →
      Relation.ReflTransGen (fun a b => b ∈ G.succ a) s.pc t.pc := by
    intro s t w h
    induction h with
    | refl => exact .refl
    | head h₁ _ ih => exact .head (G.step_pc_mem_succ h₁) ih
  exact key h

/-- Unreachable-code elimination: replace unmarked nodes by `EXIT`. -/
noncomputable def eraseUnreachable : Flowgraph V ι where
  entry := G.entry
  code n := by
    classical
    exact if G.reachable n then G.code n else .exit []

/-- The transformation preserves behaviour from the entry. -/
theorem eraseUnreachable_obsEquiv (env : Env V) (mem : Mem) :
    G.ObsEquiv G.eraseUnreachable ⟨G.entry, env, mem⟩ ⟨G.entry, env, mem⟩ := by
  have hcode : ∀ n, G.reachable n → G.eraseUnreachable.code n = G.code n := by
    intro n hn
    simp [eraseUnreachable, hn]
  have hstep : ∀ s : Config V ι, G.reachable s.pc → G.eraseUnreachable.step s = G.step s := by
    intro s hs
    simp only [step, hcode _ hs]
  have hR : IsLockstep G G.eraseUnreachable fun s t => s = t ∧ G.reachable s.pc := by
    refine ⟨?_, ?_⟩
    · rintro s t s' o ⟨rfl, hs⟩ h
      exact ⟨s', by rw [hstep s hs, h], rfl, G.reachable_of_reachable_succ hs (G.step_pc_mem_succ h)⟩
    · rintro s t ⟨rfl, hs⟩ hh
      refine ⟨?_, ?_, rfl⟩
      · unfold Halted; rw [hcode _ hs]; exact hh
      · unfold resultValues; rw [hcode _ hs]
  exact hR.traces_outcomes ⟨rfl, (G.reachable_iff _).2 .refl⟩

end Flowgraph

/-- The converse of safety fails (notes p. 7, `if tautology(x) then C₁ else C₂`):
a node can be marked but never executed. Here `CMPEQ #0, #0` always branches to
node 1, but node 2 is marked. -/
theorem exists_marked_not_executed :
    ∃ G : Flowgraph Unit (Fin 3), G.reachable 2 ∧
      ∀ env mem w (s : Config Unit (Fin 3)), G.Steps ⟨G.entry, env, mem⟩ w s → s.pc ≠ 2 := by
  let G : Flowgraph Unit (Fin 3) := ⟨0, ![.cmp .eq (.imm 0) (.imm 0) 1 2, .exit [], .exit []]⟩
  refine ⟨G, (G.reachable_iff 2).2 (.single ?_), ?_⟩
  · show (2 : Fin 3) ∈ [(1 : Fin 3), 2]
    simp
  · have key : ∀ {s t : Config Unit (Fin 3)} {w : List ℤ}, G.Steps s w t → s.pc ≠ 2 → t.pc ≠ 2 := by
      intro s t w h
      induction h with
      | refl => exact id
      | @head s s' _ o _ h₁ _ ih =>
        intro hs
        apply ih
        rcases s with ⟨pc, env, mem⟩
        fin_cases pc
        · have h0 : G.step ⟨0, env, mem⟩ = some (none, ⟨1, env, mem⟩) := rfl
          change G.step ⟨0, env, mem⟩ = some (o, s') at h₁
          rw [h0] at h₁
          simp only [Option.some.injEq, Prod.mk.injEq] at h₁
          obtain ⟨-, rfl⟩ := h₁
          show (1 : Fin 3) ≠ 2
          decide
        · have h1 : G.step ⟨1, env, mem⟩ = none := rfl
          change G.step ⟨1, env, mem⟩ = some (o, s') at h₁
          simp [h1] at h₁
        · exact absurd rfl hs
    intro env mem w s h
    exact key h (by show (0 : Fin 3) ≠ 2; decide)

/-! ## §1.3 Unreachable-procedure elimination -/

/-- A call graph (notes p. 7): an edge `(f, g)` whenever `f` contains `CALL g`, or
`CALLI a` where `a` may be `g`. -/
structure CallGraph (P : Type*) where
  main : P
  calls : P → Set P

namespace CallGraph

variable {P : Type*} (C : CallGraph P)

/-- The callability equations, as a forward framework over callers. -/
def callableEquations : Equations P Prop where
  nbrs g := {f | g ∈ C.calls f}
  transfer g :=
    { toFun := fun Q => g = C.main ∨ Q
      monotone' := fun _ _ h hq => hq.imp_right h }

/-- The procedures marked callable. -/
noncomputable def callable : P → Prop := C.callableEquations.least

/-- A call graph is *safe* for a run-time invocation relation if every
invocation is an edge (the notes' over-estimate of `CALLI`). -/
def IsSafeFor (invokes : P → P → Prop) : Prop := ∀ f g, invokes f g → g ∈ C.calls f

/-- Safety (notes p. 7): every procedure invoked during execution, transitively
from `main`, is marked callable. -/
theorem callable_of_invoked {invokes : P → P → Prop} (hC : C.IsSafeFor invokes) {g : P}
    (h : Relation.ReflTransGen invokes C.main g) : C.callable g := by
  have hsol := (Equations.isSolution_iff _ _).1 C.callableEquations.least_isSolution
  induction h with
  | refl =>
    show C.callableEquations.least C.main
    rw [hsol]
    exact Or.inl rfl
  | @tail a b _ hab ih =>
    show C.callableEquations.least b
    rw [hsol]
    simp only [Equations.join, callableEquations, iSup_Prop_eq, exists_prop]
    exact Or.inr ⟨a, hC a b hab, ih⟩

end CallGraph

end Silmaril.Courses.Cambridge.OptimisingCompilers
