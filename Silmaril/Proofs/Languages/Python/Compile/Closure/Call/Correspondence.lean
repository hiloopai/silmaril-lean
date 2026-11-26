module

public import Silmaril.Languages.Python.Compile.Closure.Call.Defs
public import Silmaril.Languages.Python.Compile.Closure.Thms
public import Silmaril.Languages.Python.Core.Closure.Call.Thms

public section
namespace Silmaril.Proofs.Languages.Python.Compile.Closure.Call

open Silmaril.Languages.Python
open Compile.Closure (frameLayout parameters parameterName)
open Compile.Closure.Call (enter)
open Source (Scope)
open Source.Closure (Layout)
open Source.Closure.Frame (ParameterLayout)
open Core.Closure (Frame Heap Value)
open Core.Closure.Call (Entered Saved)

variable {parent child : Scope} {Continuation : Core.Closure.Layout → Type}
  {key : Nat} {captureLayout : Layout parent child.captures}
  {parameterLayout : ParameterLayout child} {arguments : List Value} {heap : Heap}
  {frame : Frame (frameLayout parent)} {continuation : Continuation (frameLayout parent)}
  {stack : List (Saved Continuation)} {callee : Entered Continuation (frameLayout child)}

theorem source_enter_complete
    (arity : arguments.length = child.context.parameters.length)
    (live : ∀ index : Fin child.captures.length,
      ((captureLayout.entriesVector.get index).slot.cell frame.owned frame.captures).address < heap.next) :
    ∃ callee, enter key captureLayout parameterLayout arguments heap frame continuation stack = .ok callee := by
  let fn := frame.closure (Compile.Closure.codeRef child key) (Compile.Closure.captureOperands captureLayout)
  have count : (parameters parameterLayout).slots.length = child.context.parameters.length := by
    simpa using congrArg List.length (Compile.Closure.parameters_order parameterLayout)
  have completed : Core.Closure.Call.completeArguments (parameters parameterLayout)
      fn.positionalDefaults arguments = .ok arguments :=
    Core.Closure.Call.completeArguments_empty.mpr ⟨arity.trans count.symm, rfl⟩
  apply Core.Closure.Call.enter_complete (fn := fn) completed
  intro identity member
  obtain ⟨i, bound, atIndex⟩ := List.mem_iff_getElem.mp member
  have runtimeBound : i < fn.code.layout.captures := by simpa using bound
  let index : Fin child.captures.length := ⟨i, runtimeBound⟩
  have isCell := Compile.Closure.capture_at key captureLayout frame index
  have isIdentity : fn.captures[index] = identity := by simpa [index] using atIndex
  exact (isIdentity.symm.trans isCell) ▸ live index

theorem source_parameter_read
    (entered : enter key captureLayout parameterLayout arguments heap frame continuation stack = .ok callee)
    (index : Nat) (declared : index < child.context.parameters.length) :
    ∃ (slot : Core.Closure.ParameterSlot (frameLayout child)) (arg : Value),
      (parameters parameterLayout).slots[index]? = some slot ∧
      arguments[index]? = some arg ∧
      child.context.parameters[index] = parameterName child slot ∧
      callee.environment.2.read callee.environment.1 slot.slot = .ok arg := by
  have order := Compile.Closure.parameters_order parameterLayout
  have count : (parameters parameterLayout).slots.length = child.context.parameters.length := by
    simpa using congrArg List.length order
  have spec := Core.Closure.Call.enter_spec
    (fn := frame.closure (Compile.Closure.codeRef child key) (Compile.Closure.captureOperands captureLayout))
    entered
  obtain ⟨completed, completion, _⟩ := spec.1
  change Core.Closure.Call.completeArguments _ [] _ = .ok completed at completion
  obtain ⟨arity, same⟩ := Core.Closure.Call.completeArguments_empty.mp completion
  subst completed
  have atSlot : index < (parameters parameterLayout).slots.length := count ▸ declared
  have atArg : index < arguments.length := arity ▸ atSlot
  let slot := (parameters parameterLayout).slots[index]
  let arg := arguments[index]
  have zipped : index < ((parameters parameterLayout).slots.zip arguments).length := by
    simpa [Nat.lt_min] using And.intro atSlot atArg
  have pair : (slot, arg) ∈ (parameters parameterLayout).slots.zip arguments := by
    rw [← List.getElem_zip (h := zipped)]
    exact List.getElem_mem zipped
  have named := congrArg (·[index]?) order
  refine ⟨slot, arg, List.getElem?_eq_getElem atSlot, List.getElem?_eq_getElem atArg, ?_, ?_⟩
  · simpa [List.getElem?_eq_getElem atSlot, List.getElem?_eq_getElem declared, slot] using named.symm
  · exact Core.Closure.Call.enter_read entered completion pair

theorem source_capture_at
    (entered : enter key captureLayout parameterLayout arguments heap frame continuation stack = .ok callee)
    (index : Fin child.captures.length) :
    callee.environment.2.captures index = (captureLayout.entriesVector.get index).slot.cell frame.owned frame.captures := by
  exact (Core.Closure.Call.enter_capture
    (fn := frame.closure (Compile.Closure.codeRef child key) (Compile.Closure.captureOperands captureLayout))
    entered index).trans (Compile.Closure.capture_at key captureLayout frame index)

theorem source_capture_contents
    (entered : enter key captureLayout parameterLayout arguments heap frame continuation stack = .ok callee)
    (index : Fin child.captures.length) :
    callee.environment.1.lookup (callee.environment.2.captures index) =
      heap.lookup ((captureLayout.entriesVector.get index).slot.cell frame.owned frame.captures) := by
  let fn := frame.closure (Compile.Closure.codeRef child key) (Compile.Closure.captureOperands captureLayout)
  have member : fn.captures[index] ∈ fn.captures.toList := by
    exact Vector.mem_toList_iff.mpr (Vector.getElem_mem index.isLt)
  have live := Core.Closure.Call.enter_captures_live (fn := fn) entered member
  rw [source_capture_at entered index, ← Compile.Closure.capture_at key captureLayout frame index]
  exact Core.Closure.Call.enter_preserves_cell (fn := fn) entered live

end Silmaril.Proofs.Languages.Python.Compile.Closure.Call
