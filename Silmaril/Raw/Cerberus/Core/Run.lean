module

public import Silmaril.Cerberus.Core.Dynamics.Defs

/-! Certified bounded execution of the Core LTS. Fuel exhaustion
leaves a resumable state and has no terminal label. -/

@[expose] public section
namespace Silmaril.Cerberus.Core.Dynamics


structure Response (mem : Mem.Concrete.State) (r : Request) where
  action : Label
  after : State
  valid : Respond mem r action after

/-- Every genuine branch is retained. The default runner selects the first. -/
def responses (mem : Mem.Concrete.State) : (r : Request) → List (Response mem r)
  | .memory name m c k => [⟨.memory name, ⟨c, k, m⟩, .memory⟩]
  | .update m c k => [⟨.tau, ⟨c, k, m⟩, .update⟩]
  | .pull _ _ _ => [⟨.terminal (.error "negative action without bound"),
      ⟨.halt (.error "negative action without bound"), [], mem⟩, .pull⟩]
  | .next c k => [⟨.tau, ⟨c, k, mem⟩, .next⟩]
  | .end_ o => [⟨.terminal o, ⟨.halt o, [], mem⟩, .end_⟩]
  | .choose [] => [⟨.terminal (.error "empty choice"), ⟨.halt (.error "empty choice"), [], mem⟩, .empty⟩]
  | .choose (x :: xs) =>
      (x :: xs).attach.map fun p => ⟨.tau, ⟨p.val.1, p.val.2, mem⟩, .choose p.property⟩

  | .scheduled [] => [⟨.terminal (.error "empty choice"), ⟨.halt (.error "empty choice"), [], mem⟩, .scheduledEmpty⟩]
  | .scheduled (x :: xs) =>
      (x :: xs).attach.map fun p => ⟨.tau, ⟨p.val.1, p.val.2, mem⟩, .scheduled p.property⟩

structure Transition (file : Program) (labels : Labels) (start : State) where
  action : Label
  after : State
  valid : (lts file labels).Tr start action after

inductive StepResult (file : Program) (labels : Labels) (start : State) where
  | step : Transition file labels start → StepResult file labels start
  | ended : (o : Outcome) → start.control = .halt o → StepResult file labels start

/-- A response list is nonempty, including explicit failures. -/
theorem responses_nonempty (mem : Mem.Concrete.State) (r : Request) : responses mem r ≠ [] := by
  cases r with
  | memory => simp [responses]
  | next => simp [responses]
  | update => simp [responses]
  | pull => simp [responses]
  | end_ => simp [responses]
  | choose choices => cases choices <;> simp [responses]
  | scheduled choices => cases choices <;> simp [responses]

/-- No fuel is spent inside the stepper. The certificate uses the relation's
response rule, independently of which branch the policy selects. -/
def stepWith (choice : Nat) (file : Program) (labels : Labels) (start : State) : StepResult file labels start :=
  match h : start.control with
  | .halt o => .ended o h
  | .globals _ _ _ | .enterMain _ _ | .mainArgs _ _ _ _ | .startup _ | .commitMemory _ _ _ | .commitUpdate _ _ | .setLocation _ _ | .pureExpr _ _ | .effectExpr _ _ | .value _ | .apply _ _ | .interleave _ _ | .pulling _ _ _ | .resuming _ | .rmwFinish _ _ _ | .rmwMarker _ _ | .jumping _ _ _ | .raise _ =>
      let rs := responses start.memory (request file labels start)
      let response := rs[choice]?.getD (rs.head (responses_nonempty _ _))
      .step ⟨response.action, response.after, .respond (by
        intro o equal
        rw [h] at equal
        cases equal) response.valid⟩

def step (file : Program) (labels : Labels) (start : State) : StepResult file labels start :=
  stepWith 0 file labels start

structure Run (file : Program) (labels : Labels) (start : State) where
  finalState : State
  actions : List Label
  trace : (lts file labels).MTr start actions finalState
  ending : Option Outcome

/-- Python/Interpreter/Run.lean's bounded recursion and trace construction. -/
def runWith (choice : Nat) (file : Program) (labels : Labels) : (fuel : Nat) → (start : State) → Run file labels start
  | 0, start => ⟨start, [], .refl, none⟩
  | fuel + 1, start => match stepWith choice file labels start with
      | .step transition =>
          let rest := runWith choice file labels fuel transition.after
          ⟨rest.finalState, transition.action :: rest.actions,
            .stepL transition.valid rest.trace, rest.ending⟩
      | .ended o _ => ⟨start, [], .refl, some o⟩

def run (file : Program) (labels : Labels) (fuel : Nat) (start : State) : Run file labels start :=
  runWith 0 file labels fuel start

theorem run_sound (file : Program) (labels : Labels) (fuel : Nat) (start : State) :
    (lts file labels).MTr start (run file labels fuel start).actions
      (run file labels fuel start).finalState := (run file labels fuel start).trace

theorem run_execution (file : Program) (labels : Labels) (fuel : Nat) (start : State) :
    ∃ states, (lts file labels).Execution start (run file labels fuel start).actions
      (run file labels fuel start).finalState states :=
  Cslib.LTS.Execution.of_mTr (run_sound file labels fuel start)

theorem terminal_no_step (file : Program) (labels : Labels) (o : Outcome)
    (k : List Frame) (mem : Mem.Concrete.State) (a : Label) (after : State) :
    ¬ (lts file labels).Tr ⟨.halt o, k, mem⟩ a after := by
  intro h
  cases h with
  | respond live _ => exact live o rfl

/-- Every live state has a transition, including a labelled unsupported ending. -/
theorem live_progress (file : Program) (labels : Labels) (start : State)
    (live : ∀ o, start.control ≠ .halt o) :
    ∃ action after, (lts file labels).Tr start action after := by
  cases step file labels start with
  | step transition => exact ⟨transition.action, transition.after, transition.valid⟩
  | ended o equal => exact False.elim (live o equal)

end Silmaril.Cerberus.Core.Dynamics
