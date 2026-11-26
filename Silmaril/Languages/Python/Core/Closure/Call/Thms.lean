module

public import Silmaril.Languages.Python.Core.Closure.Call.Defs
public import Silmaril.Languages.Python.Core.Closure.Call.PositionalDefaults.Completion
public import Silmaril.Languages.Python.Core.Closure.Thms
import Silmaril.Proofs.Languages.Python.Core.Closure.Call.Correspondence

public section

namespace Silmaril.Languages.Python.Core.Closure.Call

variable {layout : Layout} {before after : Environment layout}

theorem bind_iff {parameters : Parameters layout} {arguments : List Value} :
    bindPositional parameters arguments before = .ok after ↔
      arguments.length = parameters.slots.length ∧ Writes (parameters.slots.zip arguments) before after :=
  Proofs.Languages.Python.Core.Closure.Call.bind_iff

theorem bind_preserves_ids {parameters : Parameters layout} {arguments : List Value}
    (bound : bindPositional parameters arguments before = .ok after) :
    after.2.owned = before.2.owned ∧ after.2.captures = before.2.captures :=
  Proofs.Languages.Python.Core.Closure.Call.writes_preserve_ids (bind_iff.mp bound).2

/-- Each argument can be read at its declared parameter slot after binding.
Distinct owned slots must use distinct cells. -/
theorem bind_read {parameters : Parameters layout} {arguments : List Value}
    (bound : bindPositional parameters arguments before = .ok after)
    (unique : Function.Injective before.2.owned)
    {slot : ParameterSlot layout} {value : Value} (member : (slot, value) ∈ parameters.slots.zip arguments) :
    after.2.read after.1 slot.slot = .ok value :=
  Proofs.Languages.Python.Core.Closure.Call.bind_read bound unique member

theorem bind_arity_error (parameters : Parameters layout) (arguments : List Value)
    (before : Environment layout) (wrong : arguments.length ≠ parameters.slots.length) :
    bindPositional parameters arguments before =
      .error (.defined (.positionalArity parameters.slots.length arguments.length)) := by
  simp [bindPositional, wrong]

variable {Continuation : Layout → Type} {fn : Function} {parameters : Parameters fn.code.layout}
  {arguments : List Value} {heap : Heap} {caller : Saved Continuation} {stack : List (Saved Continuation)}
  {callee : Entered Continuation fn.code.layout}

theorem enter_spec (entered : enter fn parameters arguments heap caller stack = .ok callee) :
    (∃ completed, completeArguments parameters fn.positionalDefaults arguments = .ok completed ∧
      bindPositional parameters completed (fn.freshFrame heap) = .ok callee.environment) ∧
      callee.stack = caller :: stack :=
  Proofs.Languages.Python.Core.Closure.Call.enter_spec entered

theorem enter_captures_live (entered : enter fn parameters arguments heap caller stack = .ok callee)
    {identity : CellId} (captured : identity ∈ fn.captures.toList) : identity.address < heap.next :=
  Proofs.Languages.Python.Core.Closure.Call.enter_captures_live entered captured

/-- Entry succeeds after argument completion when all incoming cells are allocated. -/
theorem enter_complete {completed : List Value}
    (completion : completeArguments parameters fn.positionalDefaults arguments = .ok completed)
    (live : ∀ identity ∈ fn.captures.toList, identity.address < heap.next) :
    ∃ callee, enter fn parameters arguments heap caller stack = .ok callee :=
  Proofs.Languages.Python.Core.Closure.Call.enter_complete completion live

theorem enter_capture (entered : enter fn parameters arguments heap caller stack = .ok callee)
    (index : Fin fn.code.layout.captures) : callee.environment.2.captures index = fn.captures.get index :=
  by
    obtain ⟨_, _, bound⟩ := (enter_spec entered).1
    exact congrFun (bind_preserves_ids bound).2 index

/-- Successful entry reads each completed argument at its compiler-assigned slot. -/
theorem enter_read (entered : enter fn parameters arguments heap caller stack = .ok callee)
    {completed : List Value}
    (completion : completeArguments parameters fn.positionalDefaults arguments = .ok completed)
    {slot : ParameterSlot fn.code.layout} {value : Value}
    (member : (slot, value) ∈ parameters.slots.zip completed) :
    callee.environment.2.read callee.environment.1 slot.slot = .ok value := by
  obtain ⟨actual, checked, bound⟩ := (enter_spec entered).1
  have same := Except.ok.inj (checked.symm.trans completion)
  subst actual
  exact bind_read bound (Frame.fresh_owned_injective heap fn.captures.get) member

/-- Allocation and positional binding leave every pre-existing cell unchanged. -/
theorem enter_preserves_cell (entered : enter fn parameters arguments heap caller stack = .ok callee)
    {identity : CellId} (live : identity.address < heap.next) :
    callee.environment.1.lookup identity = heap.lookup identity :=
  Proofs.Languages.Python.Core.Closure.Call.enter_preserves_cell entered live

/-- The entire caller frame and continuation are restored for a return or a
defined error. Both deliveries carry the residual heap supplied by the callee. -/
theorem finish_after_enter (entered : enter fn parameters arguments heap caller stack = .ok callee)
    (residual : Heap) (result : Result) :
    finish residual callee.stack result = ⟨residual, stack, .resume caller result⟩ := by
  rw [(enter_spec entered).2]
  rfl

end Silmaril.Languages.Python.Core.Closure.Call
