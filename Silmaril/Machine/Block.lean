module

/-!
# Straight-line machine blocks

These definitions describe a total, deterministic instruction fragment. Control
flow, faults, memory events, instruction fetching, and termination require richer
semantics; none are implicit in a list of instructions here.

The compiler theorem isolates the reusable part of a straight-line backend:
instruction selection supplies a state relation and one proof per instruction.
-/

@[expose] public section

namespace Silmaril.Machine.Block

universe u v w x

variable {Instr : Type u} {State : Type v}

/-- Execute instructions from left to right, threading the machine state. -/
def run (step : Instr → State → State) : List Instr → State → State
  | [], state => state
  | instr :: rest, state => run step rest (step instr state)

@[simp] theorem run_nil (step : Instr → State → State) (state : State) :
    run step [] state = state := rfl

@[simp] theorem run_cons (step : Instr → State → State) (instr : Instr)
    (rest : List Instr) (state : State) :
    run step (instr :: rest) state = run step rest (step instr state) := rfl

@[simp] theorem run_singleton (step : Instr → State → State) (instr : Instr)
    (state : State) : run step [instr] state = step instr state := rfl

/-- Concatenating code composes its state transformations in execution order. -/
theorem run_append (step : Instr → State → State) (first second : List Instr)
    (state : State) :
    run step (first ++ second) state = run step second (run step first state) := by
  induction first generalizing state with
  | nil => rfl
  | cons instr rest ih => exact ih (step instr state)

/-- An instruction invariant holds after any straight-line block. -/
theorem run_preserves (step : Instr → State → State) (invariant : State → Prop)
    (preserves : ∀ instr state, invariant state → invariant (step instr state))
    (code : List Instr) (state : State) (h : invariant state) :
    invariant (run step code state) := by
  induction code generalizing state with
  | nil => exact h
  | cons instr rest ih => exact ih _ (preserves instr state h)

variable {Source : Type u} {Target : Type v}

/-- Replace each source instruction with its selected target block. -/
def compile (emit : Source → List Target) : List Source → List Target
  | [] => []
  | instr :: rest => emit instr ++ compile emit rest

@[simp] theorem compile_nil (emit : Source → List Target) :
    compile emit [] = [] := rfl

@[simp] theorem compile_cons (emit : Source → List Target) (instr : Source)
    (rest : List Source) :
    compile emit (instr :: rest) = emit instr ++ compile emit rest := rfl

theorem compile_append (emit : Source → List Target) (first second : List Source) :
    compile emit (first ++ second) = compile emit first ++ compile emit second := by
  induction first with
  | nil => rfl
  | cons instr rest ih => simp only [List.cons_append, compile_cons, ih, List.append_assoc]

/--
Instruction selection is correct for every block when each source instruction is
simulated by its emitted block. The relation may hide target scratch registers,
record a representation invariant, or relate states of different architectures.
-/
theorem compile_correct {SourceState : Type w} {TargetState : Type x}
    (sourceStep : Source → SourceState → SourceState)
    (targetStep : Target → TargetState → TargetState)
    (emit : Source → List Target) (relation : SourceState → TargetState → Prop)
    (correct : ∀ instr source target, relation source target →
      relation (sourceStep instr source) (run targetStep (emit instr) target))
    (code : List Source) {source : SourceState} {target : TargetState}
    (h : relation source target) :
    relation (run sourceStep code source) (run targetStep (compile emit code) target) := by
  induction code generalizing source target with
  | nil => exact h
  | cons instr rest ih =>
    simp only [run_cons, compile_cons, run_append]
    exact ih (correct instr source target h)

/-- Successive straight-line lowering passes can be fused instruction by instruction. -/
theorem compile_comp {Final : Type w} (first : Source → List Target)
    (second : Target → List Final) (code : List Source) :
    compile second (compile first code) = compile (fun instr => compile second (first instr)) code := by
  induction code with
  | nil => rfl
  | cons instr rest ih => simp only [compile_cons, compile_append, ih]

end Silmaril.Machine.Block
