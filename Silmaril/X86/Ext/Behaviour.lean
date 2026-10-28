module

public import Silmaril.X86.Ext.Machine
public import Silmaril.Machine.Behaviour.Semantics

/-!
# The `X86.Ext` machine as a `Behaviour.Semantics`

`Ext.sem Exhausted` presents the fetch/decode/execute machine `Ext.step` in the
shared vocabulary of `Silmaril.Machine.Behaviour` (#452). It does not depend on
any compiler.

A state is a pair `(exit, t)` of the designated return address and a machine
state; `exit` never changes. A step is a retirement, `Ext.step exit t =
.retired t'`. Where the machine stops, the outcome is:

* `returned final` for a RET that pops `exit` (`Ext.Outcome.returned final`);
* for a UD2 (`Ext.Outcome.trapped`): `exhausted` when `Exhausted t` holds, and
  otherwise `trapped t`, the machine state at the UD2;
* `faulted φ` for every other outcome, with `φ : Fault` naming it: an undefined
  condition, a divide fault, a data fault, a fetch fault or undecodable bytes.

`Exhausted` is a parameter: it says which UD2 stops are resource exhaustion
rather than traps. `StackCheck.Exhausted stackLo sites` is the instance used
for code with stack-limit checks: a UD2 counts as exhaustion only at a declared
stack-check site `(a, n)`, RIP `= a`, with less than `n` bytes of stack left
above `stackLo`. Every other UD2 is a trap.

The semantics is deterministic (`sem_deterministic`), because `Ext.step` is a
function, and every state steps or stops (`sem_progress`).
-/

@[expose] public section

namespace Silmaril.X86.Ext

open Silmaril.X86 (MState Word)
open Silmaril.Machine
open Relation

/-- The non-retiring, non-returning, non-trapping outcomes of `Ext.step`. -/
inductive Fault where
  | undefinedCondition (c : Cond)
  | divideFault
  | dataFault (instr : Instr)
  | fetchFault
  | undecodable

/-- The fault of an outcome, if it is one. -/
def Outcome.fault? : Outcome → Option Fault
  | .undefinedCondition c => some (.undefinedCondition c)
  | .divideFault => some .divideFault
  | .dataFault instr => some (.dataFault instr)
  | .fetchFault => some .fetchFault
  | .undecodable => some .undecodable
  | .retired _ | .returned _ | .trapped => none

/-- The outcome shown by a state where the machine stops. -/
inductive FinalOutcome (Exhausted : MState → Prop) :
    Word × MState → Behaviour.Outcome MState MState Fault → Prop where
  | returned {exit : Word} {t final : MState} (h : step exit t = .returned final) :
      FinalOutcome Exhausted (exit, t) (.returned final)
  | exhausted {exit : Word} {t : MState} (h : step exit t = .trapped) (hx : Exhausted t) :
      FinalOutcome Exhausted (exit, t) .exhausted
  | trapped {exit : Word} {t : MState} (h : step exit t = .trapped) (hx : ¬ Exhausted t) :
      FinalOutcome Exhausted (exit, t) (.trapped t)
  | faulted {exit : Word} {t : MState} {φ : Fault} (h : (step exit t).fault? = some φ) :
      FinalOutcome Exhausted (exit, t) (.faulted φ)

/-- One retirement at a fixed return address. -/
def Step (a b : Word × MState) : Prop := b.1 = a.1 ∧ step a.1 a.2 = .retired b.2

/-- The machine with return address `exit` as a semantics; `Exhausted` selects
the UD2 stops that are resource exhaustion. -/
def sem (Exhausted : MState → Prop) : Behaviour.Semantics (Word × MState) MState MState Fault where
  step := Step
  final := FinalOutcome Exhausted

section Sem

variable {Exhausted : MState → Prop}

@[simp] theorem sem_step : (sem Exhausted).step = Step := rfl

@[simp] theorem sem_final : (sem Exhausted).final = FinalOutcome Exhausted := rfl

theorem step_rightUnique : Relator.RightUnique Step := by
  have h := RightUnique.of_injective (fun a : Word × MState => (a.1, step a.1 a.2))
    (fun b : Word × MState => (b.1, Outcome.retired b.2))
    (fun a b h => by
      simp only [Prod.mk.injEq, Outcome.retired.injEq] at h
      exact Prod.ext h.1 h.2)
  intro a b c hb hc
  exact h (Prod.ext hb.1.symm hb.2) (Prod.ext hc.1.symm hc.2)

theorem finalOutcome_not_retired {s : Word × MState} {o : Behaviour.Outcome MState MState Fault}
    (h : FinalOutcome Exhausted s o) {t' : MState} : step s.1 s.2 ≠ .retired t' := by
  cases h with
  | returned h | exhausted h | trapped h => rw [h]; nofun
  | faulted h =>
    intro e
    rw [e] at h
    cases h

theorem sem_deterministic : (sem Exhausted).Deterministic where
  step_unique := step_rightUnique
  final_unique s o o' h h' := by
    cases h with
    | returned h =>
      cases h' with
      | returned h' => rw [h] at h'; cases h'; rfl
      | exhausted h' | trapped h' => rw [h] at h'; cases h'
      | faulted h' => rw [h] at h'; cases h'
    | exhausted h hx =>
      cases h' with
      | returned h' => rw [h] at h'; cases h'
      | exhausted => rfl
      | trapped _ hx' => exact absurd hx hx'
      | faulted h' => rw [h] at h'; cases h'
    | trapped h hx =>
      cases h' with
      | returned h' => rw [h] at h'; cases h'
      | exhausted _ hx' => exact absurd hx' hx
      | trapped => rfl
      | faulted h' => rw [h] at h'; cases h'
    | faulted h =>
      cases h' with
      | returned h' | exhausted h' | trapped h' => rw [h'] at h; cases h
      | faulted h' => rw [h] at h'; cases h'; rfl
  final_stop s o h t hs := finalOutcome_not_retired h hs.2

theorem sem_progress : (sem Exhausted).Progress := by
  classical
  rintro ⟨exit, t⟩
  cases h : step exit t with
  | retired t' => exact .inl ⟨(exit, t'), rfl, h⟩
  | returned final => exact .inr ⟨_, .returned h, nofun⟩
  | trapped =>
    by_cases hx : Exhausted t
    · exact .inr ⟨_, .exhausted h hx, nofun⟩
    · exact .inr ⟨_, .trapped h hx, nofun⟩
  | undefinedCondition c => exact .inr ⟨_, .faulted (φ := .undefinedCondition c) (by rw [h]; rfl), nofun⟩
  | divideFault => exact .inr ⟨_, .faulted (φ := .divideFault) (by rw [h]; rfl), nofun⟩
  | dataFault i => exact .inr ⟨_, .faulted (φ := .dataFault i) (by rw [h]; rfl), nofun⟩
  | fetchFault => exact .inr ⟨_, .faulted (φ := .fetchFault) (by rw [h]; rfl), nofun⟩
  | undecodable => exact .inr ⟨_, .faulted (φ := .undecodable) (by rw [h]; rfl), nofun⟩

/-! ## Runs at a fixed return address -/

/-- A run of retirements at return address `exit` is a run of `sem`. -/
theorem reach_of {exit : Word} {t u : MState}
    (h : ReflTransGen (fun a b => step exit a = .retired b) t u) :
    ReflTransGen (sem Exhausted).step (exit, t) (exit, u) := by
  induction h with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail ⟨rfl, hs⟩

/-- An infinite run of retirements at return address `exit` is an infinite run
of `sem`. -/
theorem infinite_of {exit : Word} {t : MState}
    (h : InfiniteTrace (fun a b => step exit a = .retired b) t) :
    InfiniteTrace (sem Exhausted).step (exit, t) :=
  InfiniteTrace.map (fun u => (exit, u)) (fun _ _ hs => ⟨rfl, hs⟩) h

theorem beh_returned {exit : Word} {t u final : MState}
    (h : ReflTransGen (fun a b => step exit a = .retired b) t u)
    (hs : step exit u = .returned final) : (sem Exhausted).Beh (exit, t) (.returned final) :=
  Behaviour.Semantics.Beh.of_reach (reach_of h) (.of_final (.returned hs) nofun)

theorem beh_exhausted {exit : Word} {t u : MState}
    (h : ReflTransGen (fun a b => step exit a = .retired b) t u) (hs : step exit u = .trapped)
    (hx : Exhausted u) : (sem Exhausted).Beh (exit, t) .exhausted :=
  Behaviour.Semantics.Beh.of_reach (reach_of h) (.of_final (.exhausted hs hx) nofun)

theorem beh_trapped {exit : Word} {t u : MState}
    (h : ReflTransGen (fun a b => step exit a = .retired b) t u) (hs : step exit u = .trapped)
    (hx : ¬ Exhausted u) : (sem Exhausted).Beh (exit, t) (.trapped u) :=
  Behaviour.Semantics.Beh.of_reach (reach_of h) (.of_final (.trapped hs hx) nofun)

theorem beh_diverges {exit : Word} {t : MState}
    (h : InfiniteTrace (fun a b => step exit a = .retired b) t) :
    (sem Exhausted).Beh (exit, t) .diverges :=
  infinite_of h

end Sem

/-! ## Stack-limit checks -/

namespace StackCheck

/-- A UD2 at state `t` is stack exhaustion when RIP is a declared stack-check
site `(a, n)` and less than `n` bytes of stack are left above `stackLo`. -/
def Exhausted (stackLo : Nat) (sites : List (Nat × Nat)) (t : MState) : Prop :=
  ∃ a n, (a, n) ∈ sites ∧ t.core.rip.toNat = a ∧ (t.core.read .rsp).toNat - stackLo < n

end StackCheck

end Silmaril.X86.Ext
