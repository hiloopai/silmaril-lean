module

public import Silmaril.Machine.CBackend.Behaviour.Equivalence.Defs
public import Silmaril.Machine.CBackend.Behaviour.Compose.Defs
/-!
# Examples of the failure modes and the exhaustion relaxation

Toy semantics on `Nat` and `Unit`, one per case of the behaviour layer:

* `stackLimit_divergeToTrap`, `stackLimit_not_strict`: a stack-limit check
  turns unbounded recursion (divergent in the source) into a trap. This
  refines in `divergeToTrap` and not in `strict`.
* `selfLoop_trapOrDiverge`, `selfLoop_not_divergeToTrap`: a trap implemented
  as a self-loop refines in `trapOrDiverge` only.
* `exhaustion_allowed`, `exhaustion_forbidden`: a target that may stop
  exhausted implements a returning source only under `Exhaustion.allowed`,
  whatever the failure mode.
* `mutual_refines`, `mutual_not_equiv`: without determinism, mutual
  `divergeToTrap` refinement is not `strict` equivalence.
* `succ_implements`, `succ_nonvacuous`: an `Implements` instance obtained from
  a forward simulation and target determinism, with a represented target state
  for every call and a target that never gets stuck.
* `stuck_implements`, `stuck_represented`, `stuck_not_live`: a target with no
  transitions and no final outcomes implements every source, with every call
  represented. Only the liveness half of `Implements.Nonvacuous` rules it out.
-/

@[expose] public section

namespace Silmaril.Machine.Behaviour.Examples

open Relation Semantics

/-! ## A stack-limit check: `divergeToTrap` but not `strict` -/

/-- Unbounded recursion: every depth calls one level deeper. -/
def recursion : Semantics Nat Unit Unit Empty where
  step n n' := n' = n + 1
  final _ _ := False

/-- The same recursion with a stack limit `k`: at depth `k` or more it traps. -/
def guarded (k : Nat) : Semantics Nat Unit Unit Empty where
  step n n' := n < k ∧ n' = n + 1
  final n o := k ≤ n ∧ o = .trapped ()

theorem recursion_diverges (n : Nat) : recursion.Beh n .diverges :=
  ⟨fun i => n + i, rfl, fun i => by show n + (i + 1) = n + i + 1; omega⟩

theorem recursion_not_final {n : Nat} {o : Outcome Unit Unit Empty} (ho : o ≠ .diverges) :
    ¬ recursion.Beh n o := by
  rw [beh_of_ne ho]
  rintro ⟨_, -, h⟩
  exact h

theorem recursion_safe (n : Nat) : recursion.Safe n :=
  recursion_not_final (by simp)

theorem guarded_reach (k : Nat) : ∀ i, i ≤ k → ReflTransGen (guarded k).step 0 i
  | 0, _ => .refl
  | i + 1, h => (guarded_reach k i (by omega)).tail ⟨by omega, rfl⟩

theorem guarded_traps (k : Nat) : (guarded k).Beh 0 (.trapped ()) :=
  (beh_of_ne (by simp)).mpr ⟨k, guarded_reach k k le_rfl, le_rfl, rfl⟩

theorem guarded_beh {k n : Nat} {o : Outcome Unit Unit Empty} (h : (guarded k).Beh n o) :
    o = .trapped () ∨ o = .diverges := by
  by_cases ho : o = .diverges
  · exact .inr ho
  · obtain ⟨_, -, -, rfl⟩ := (beh_of_ne ho).mp h
    exact .inl rfl

theorem stackLimit_divergeToTrap (k : Nat) :
    Refines ⟨.divergeToTrap, .forbidden⟩ (guarded k) recursion Eq (fun _ _ => Obs.id) := by
  intro t s _ _ o ho
  refine ⟨.diverges, recursion_diverges s, ?_⟩
  rcases guarded_beh ho with rfl | rfl
  · show FailureMode.divergeToTrap ≠ .strict
    decide
  · trivial

theorem stackLimit_not_strict (k : Nat) :
    ¬ Refines Mode.strict (guarded k) recursion Eq (fun _ _ => Obs.id) := fun h => by
  obtain ⟨_, hb, -⟩ := h.trapped rfl rfl (recursion_safe 0) (guarded_traps k)
  exact recursion_not_final (by simp) hb

/-! ## A trap as a self-loop: `trapOrDiverge` only -/

/-- A program that traps immediately. -/
def trapNow : Semantics Unit Unit Unit Empty where
  step _ _ := False
  final _ o := o = .trapped ()

/-- A program that loops forever (`jmp .`). -/
def spin : Semantics Unit Unit Unit Empty where
  step _ _ := True
  final _ _ := False

theorem spin_beh {o : Outcome Unit Unit Empty} : spin.Beh () o ↔ o = .diverges := by
  by_cases ho : o = .diverges
  · subst ho
    exact ⟨fun _ => rfl, fun _ => ⟨(fun _ => ()), rfl, (fun _ => trivial)⟩⟩
  · rw [beh_of_ne ho]
    exact ⟨fun ⟨_, _, h⟩ => h.elim, fun h => absurd h ho⟩

theorem trapNow_beh {o : Outcome Unit Unit Empty} : trapNow.Beh () o ↔ o = .trapped () := by
  rw [beh_of_stop (fun _ h => h)]
  exact ⟨fun h => h.1, fun h => ⟨h, by rw [h]; simp⟩⟩

theorem trapNow_safe : trapNow.Safe () := fun h => by
  cases trapNow_beh.mp h

theorem selfLoop_trapOrDiverge :
    Refines ⟨.trapOrDiverge, .forbidden⟩ spin trapNow Eq (fun _ _ => Obs.id) := by
  rintro ⟨⟩ ⟨⟩ _ _ o ho
  rw [spin_beh.mp ho]
  exact ⟨.trapped (), trapNow_beh.mpr rfl, rfl⟩

/-- Not even with the exhaustion relaxation. -/
theorem selfLoop_not_divergeToTrap (x : Exhaustion) :
    ¬ Refines ⟨.divergeToTrap, x⟩ spin trapNow Eq (fun _ _ => Obs.id) := fun h => by
  have := h.diverges le_rfl rfl trapNow_safe (spin_beh.mpr rfl)
  cases trapNow_beh.mp this

/-! ## Resource exhaustion: only under `Exhaustion.allowed` -/

/-- A program that returns. -/
def returnsNow : Semantics Unit Unit Empty Empty where
  step _ _ := False
  final _ o := o = .returned ()

/-- A program that returns, or runs out of stack first. -/
def mayExhaust : Semantics Unit Unit Empty Empty where
  step _ _ := False
  final _ o := o = .returned () ∨ o = .exhausted

theorem returnsNow_beh {o : Outcome Unit Empty Empty} :
    returnsNow.Beh () o ↔ o = .returned () := by
  rw [beh_of_stop (fun _ h => h)]
  exact ⟨fun h => h.1, fun h => ⟨h, by rw [h]; simp⟩⟩

theorem mayExhaust_beh {o : Outcome Unit Empty Empty} :
    mayExhaust.Beh () o ↔ o = .returned () ∨ o = .exhausted := by
  rw [beh_of_stop (fun _ h => h)]
  exact ⟨fun h => h.1, fun h => ⟨h, by rcases h with rfl | rfl <;> simp⟩⟩

theorem returnsNow_safe : returnsNow.Safe () := fun h => by
  cases returnsNow_beh.mp h

theorem exhaustion_allowed :
    Refines ⟨.strict, .allowed⟩ mayExhaust returnsNow Eq (fun _ _ => Obs.id) := by
  rintro ⟨⟩ ⟨⟩ _ _ o ho
  refine ⟨.returned (), returnsNow_beh.mpr rfl, ?_⟩
  rcases mayExhaust_beh.mp ho with rfl | rfl
  · exact rfl
  · exact rfl

/-- In every failure mode, exhaustion forbidden. -/
theorem exhaustion_forbidden (f : FailureMode) :
    ¬ Refines ⟨f, .forbidden⟩ mayExhaust returnsNow Eq (fun _ _ => Obs.id) := fun h => by
  obtain ⟨o', ho', hr⟩ := h () () rfl returnsNow_safe .exhausted (mayExhaust_beh.mpr (.inr rfl))
  rw [hr.exhausted_left rfl] at ho'
  cases returnsNow_beh.mp ho'

/-! ## Mutual `divergeToTrap` refinement without determinism -/

/-- A nondeterministic program: it may trap, or loop forever. -/
def trapOrLoop : Semantics Unit Unit Unit Empty where
  step _ _ := True
  final _ o := o = .trapped ()

theorem trapOrLoop_beh {o : Outcome Unit Unit Empty} :
    trapOrLoop.Beh () o ↔ o = .trapped () ∨ o = .diverges := by
  by_cases ho : o = .diverges
  · subst ho
    exact ⟨fun _ => .inr rfl, fun _ => ⟨(fun _ => ()), rfl, (fun _ => trivial)⟩⟩
  · rw [beh_of_ne ho]
    exact ⟨fun ⟨_, _, h⟩ => .inl h, fun h => ⟨(), .refl, h.resolve_right ho⟩⟩

theorem trapOrLoop_not_deterministic : ¬ trapOrLoop.Deterministic := fun h =>
  h.final_stop () (.trapped ()) rfl () trivial

/-- Every pair of `Unit` states, observed by equality. -/
def unitContract : Contract Unit Unit Unit Empty := Contract.diag (fun _ => True) (fun _ => Obs.id)

theorem mutual_refines :
    Refinement .divergeToTrap unitContract trapOrLoop spin ∧
      Refinement .divergeToTrap unitContract.flip spin trapOrLoop := by
  constructor
  · rintro ⟨⟩ ⟨⟩ _ _ o ho
    refine ⟨.diverges, spin_beh.mpr rfl, ?_⟩
    rcases trapOrLoop_beh.mp ho with rfl | rfl
    · show FailureMode.divergeToTrap ≠ .strict
      decide
    · trivial
  · rintro ⟨⟩ ⟨⟩ _ _ o ho
    rw [spin_beh.mp ho]
    exact ⟨.diverges, trapOrLoop_beh.mpr (.inr rfl), trivial⟩

theorem mutual_not_equiv : ¬ Equiv .strict unitContract trapOrLoop spin := fun h => by
  obtain ⟨o', ho', hr⟩ := h.1 () () ⟨rfl, trivial⟩ (fun hu => by cases spin_beh.mp hu)
    (.trapped ()) (trapOrLoop_beh.mpr (.inl rfl))
  rw [spin_beh.mp ho'] at hr
  exact hr rfl

/-! ## A nonvacuous `Implements` instance -/

/-- Source: the call `n` returns `n + 1`. -/
def succSpec : Semantics Nat Nat Empty Empty where
  step _ _ := False
  final n o := o = .returned (n + 1)

/-- Target: a register and a done bit. One step increments the register;
the done state returns it. -/
def succImpl : Semantics (Nat × Bool) Nat Empty Empty where
  step s s' := s.2 = false ∧ s' = (s.1 + 1, true)
  final s o := s.2 = true ∧ o = .returned s.1

/-- The target state for the call `n`: the argument in the register, not done. -/
def succRep (n : Nat) (t : Nat × Bool) : Prop := t = (n, false)

theorem succImpl_deterministic : succImpl.Deterministic where
  step_unique _ _ _ h h' := h.2.trans h'.2.symm
  final_unique _ _ _ h h' := h.2.trans h'.2.symm
  final_stop _ _ h _ h' := absurd (h.1.symm.trans h'.1) (by decide)

theorem succSpec_beh {n : Nat} {o : Outcome Nat Empty Empty} :
    succSpec.Beh n o ↔ o = .returned (n + 1) := by
  rw [beh_of_stop (fun _ h => h)]
  exact ⟨fun h => h.1, fun h => ⟨h, by rw [h]; simp⟩⟩

theorem succ_implements :
    Implements Mode.strict succSpec succImpl id succRep (fun _ _ => Obs.id) := by
  refine Implements.of_forward succImpl_deterministic
    (fun n _ _ _ => ⟨_, succSpec_beh.mpr rfl⟩) ?_
  rintro n t rfl - o' ho'
  rw [succSpec_beh.mp ho']
  refine ⟨.returned (n + 1), Beh.of_step ⟨rfl, rfl⟩ (Beh.of_final ⟨rfl, rfl⟩ (by simp)), rfl⟩

theorem succImpl_progress : succImpl.Progress := by
  rintro ⟨n, _ | _⟩
  · exact .inl ⟨_, rfl, rfl⟩
  · exact .inr ⟨.returned n, ⟨rfl, rfl⟩, by simp⟩

theorem succ_nonvacuous : Implements.Nonvacuous succImpl (fun _ : Nat => True) succRep :=
  .of_progress succImpl_progress fun n _ => ⟨(n, false), rfl⟩

/-! ## A stuck target implements anything -/

/-- A target with no transitions and no final outcomes. -/
def stuck : Semantics Unit Nat Empty Empty where
  step _ _ := False
  final _ _ := False

/-- Every call is represented by the one stuck state. -/
def stuckRep (_ : Nat) (_ : Unit) : Prop := True

/-- The stuck target implements `succSpec` (and any other source): it has no
behaviour to check. -/
theorem stuck_implements :
    Implements Mode.strict succSpec stuck id stuckRep (fun _ _ => Obs.id) :=
  fun _ _ _ _ _ ho => ((beh_of_stop (fun _ h => h)).mp ho).1.elim

theorem stuck_represented : Implements.Represented (fun _ : Nat => True) stuckRep :=
  fun _ _ => ⟨(), trivial⟩

theorem stuck_not_live : ¬ Implements.Live stuck stuckRep := fun h => by
  rcases h 0 () trivial () .refl with ⟨_, h⟩ | ⟨_, h, _⟩ <;> exact h

end Silmaril.Machine.Behaviour.Examples
