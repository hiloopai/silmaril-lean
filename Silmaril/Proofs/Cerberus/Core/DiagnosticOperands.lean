module

public import Silmaril.Cerberus.Core.DiagnosticOperands.Defs

@[expose] public section
namespace Silmaril.Cerberus.Core.DiagnosticOperands
open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics
open Silmaril.Cerberus.Elaboration
open Silmaril.Cerberus.Core.PureOperands

attribute [local cbv_eval] String.toUTF8_eq_toByteArray

/-- Focusing changes no observable output. -/
theorem focused_stdout (memory : Mem.Concrete.State) : (focused memory).stdout = memory.stdout := by
  unfold focused
  split <;> rfl

/-- The same diagnostic annotation is stable after its first actual update. -/
theorem focused_idempotent (memory : Mem.Concrete.State) : focused (focused memory) = focused memory := by
  cases library : libraryLocation .unknown <;> simp [focused, library]

/-- Both actual unsequenced constant operands are forced in the real machine.
The scheduler's actual administrative priority computes the right operand
first; tuple order still follows the original operand positions. All possible
transitions at these states are retained through Forced.Reaches uniqueness. -/
theorem unseq_pair_forced (file : Program) (labels : Labels) (left right : Int)
    (environment : Env) (frames : List Frame) (memory : Mem.Concrete.State) :
    Forced.Reaches file labels
      ⟨.effectExpr (.mk [] (.unseq [constant left, constant right])) environment, frames, memory⟩
      ⟨.value (.tuple [.loaded (.specified (.integer left)), .loaded (.specified (.integer right))]),
        .annotations [] :: frames, focused memory⟩ := by
  let leftValue : Val := .loaded (.specified (.integer left))
  let rightValue : Val := .loaded (.specified (.integer right))
  let leftPure : PE := Constants.loadedInteger left
  let rightPure : PE := Constants.loadedInteger right
  let c1 : Control := Control.interleave [] [(0, .effectExpr (constant left) environment, []),
    (1, .effectExpr (constant right) environment, [])]
  let c2 : Control := Control.interleave [] [(0, .effectExpr (constant left) environment, []),
    (1, .pureExpr rightPure environment, [.diagnosticLocation memory.currentLocation])]
  let c3 : Control := Control.interleave [] [(0, .effectExpr (constant left) environment, []),
    (1, .value rightValue, [.diagnosticLocation memory.currentLocation])]
  let c4 : Control := Control.interleave [] [(0, .effectExpr (constant left) environment, []),
    (1, .value rightValue, [])]
  let c5 : Control := Control.interleave [(1, rightValue, [])] [(0, .effectExpr (constant left) environment, [])]
  let c6 : Control := Control.interleave [(1, rightValue, [])] [(0, .pureExpr leftPure environment, [.diagnosticLocation (focused memory).currentLocation])]
  let c7 : Control := Control.interleave [(1, rightValue, [])] [(0, .value leftValue, [.diagnosticLocation (focused memory).currentLocation])]
  let c8 : Control := Control.interleave [(1, rightValue, [])] [(0, .value leftValue, [])]
  let c9 : Control := Control.interleave [(0, leftValue, []), (1, rightValue, [])] []
  have start : Forced.Reaches file labels
      ⟨.effectExpr (.mk [] (.unseq [constant left, constant right])) environment, frames, memory⟩
      ⟨c1, frames, memory⟩ := by
    apply Forced.next (by intro outcome impossible; cases impossible)
    simp [request, requestAux, awaitsScheduling, c1]
  have rightStart : Forced.Reaches file labels ⟨c1, frames, memory⟩ ⟨c2, frames, focused memory⟩ := by
    cases library : libraryLocation .unknown
    · show Forced.Reaches file labels ⟨c1, frames, memory⟩ ⟨c2, frames, focused memory⟩
      by_cases located : memory.currentLocation = .unknown
      · have unchanged : focused memory = memory := by simp [focused, ← located]
        rw [unchanged]
        apply Forced.choose (by intro outcome impossible; cases impossible)
        simp [c1, c2, rightPure, constant, request, requestAux, awaitsScheduling, located, library,
          activeCall, controlHasCCall, hasCCall]
      · show Forced.Reaches file labels ⟨c1, frames, memory⟩ ⟨c2, frames, focused memory⟩
        have notUnknown : Loc.unknown ≠ memory.currentLocation := Ne.symm located
        let setter : Control := .interleave [] [(0, .effectExpr (constant left) environment, []),
          (1, .setLocation .unknown (.pureExpr rightPure environment), [.diagnosticLocation memory.currentLocation])]
        have select : Forced.Reaches file labels ⟨c1, frames, memory⟩ ⟨setter, frames, memory⟩ := by
          apply Forced.choose (by intro outcome impossible; cases impossible)
          simp [c1, setter, rightPure, constant, request, requestAux, awaitsScheduling, notUnknown, library,
            activeCall, controlHasCCall, hasCCall]
        have lift : Forced.Reaches file labels ⟨setter, frames, memory⟩
            ⟨.commitUpdate (focused memory) c2, frames, memory⟩ := by
          apply Forced.choose (by intro outcome impossible; cases impossible)
          simp [setter, c2, focused, request, requestAux, awaitsScheduling, library,
            activeCall, controlHasCCall]
        have commit : Forced.Reaches file labels ⟨.commitUpdate (focused memory) c2, frames, memory⟩
            ⟨c2, frames, focused memory⟩ := by
          apply Forced.update (by intro outcome impossible; cases impossible)
          simp [request, requestAux, awaitsScheduling]
        exact select.trans (lift.trans commit)
    · have unchanged : focused memory = memory := by simp [focused, library]
      rw [unchanged]
      apply Forced.choose (by intro outcome impossible; cases impossible)
      simp [c1, c2, rightPure, constant, request, requestAux, awaitsScheduling, library,
        activeCall, controlHasCCall, hasCCall]
  have rightRead : Forced.Reaches file labels ⟨c2, frames, focused memory⟩ ⟨c3, frames, focused memory⟩ := by
    apply Forced.choose (by intro outcome impossible; cases impossible)
    simp [c2, c3, rightPure, rightValue, Constants.loadedInteger, Construction.valuePure,
      request, requestAux, awaitsScheduling, runtimeValue, runtimeLoaded, runtimeObject, activeCall, controlHasCCall]
  have rightPop : Forced.Reaches file labels ⟨c3, frames, focused memory⟩ ⟨c4, frames, focused memory⟩ := by
    apply Forced.choose (by intro outcome impossible; cases impossible)
    simp [c3, c4, request, requestAux, awaitsScheduling, activeCall, controlHasCCall, annotationsOnly]
  have rightDone : Forced.Reaches file labels ⟨c4, frames, focused memory⟩ ⟨c5, frames, focused memory⟩ := by
    apply Forced.choose (by intro outcome impossible; cases impossible)
    simp [c4, c5, request, requestAux, awaitsScheduling, activeCall, controlHasCCall, annotationsOnly, List.filter]
  have leftStart : Forced.Reaches file labels ⟨c5, frames, focused memory⟩ ⟨c6, frames, focused memory⟩ := by
    apply Forced.choose (by intro outcome impossible; cases impossible)
    cases library : libraryLocation .unknown <;>
      simp [c5, c6, leftPure, constant, request, requestAux, awaitsScheduling, focused, library,
        activeCall, controlHasCCall, hasCCall]
  have leftRead : Forced.Reaches file labels ⟨c6, frames, focused memory⟩ ⟨c7, frames, focused memory⟩ := by
    apply Forced.choose (by intro outcome impossible; cases impossible)
    simp [c6, c7, leftPure, leftValue, Constants.loadedInteger, Construction.valuePure,
      request, requestAux, awaitsScheduling, runtimeValue, runtimeLoaded, runtimeObject, activeCall, controlHasCCall]
  have leftPop : Forced.Reaches file labels ⟨c7, frames, focused memory⟩ ⟨c8, frames, focused memory⟩ := by
    apply Forced.choose (by intro outcome impossible; cases impossible)
    simp [c7, c8, request, requestAux, awaitsScheduling, activeCall, controlHasCCall, annotationsOnly]
  have leftDone : Forced.Reaches file labels ⟨c8, frames, focused memory⟩ ⟨c9, frames, focused memory⟩ := by
    apply Forced.choose (by intro outcome impossible; cases impossible)
    simp [c8, c9, request, requestAux, awaitsScheduling, activeCall, controlHasCCall, annotationsOnly]
  have finish : Forced.Reaches file labels ⟨c9, frames, focused memory⟩
      ⟨.value (.tuple [leftValue, rightValue]), .annotations [] :: frames, focused memory⟩ := by
    dsimp only [c9]
    apply Forced.next (by intro outcome impossible; cases impossible)
    simp [request, requestAux, awaitsScheduling]
  exact start.trans (rightStart.trans (rightRead.trans (rightPop.trans (rightDone.trans
    (leftStart.trans (leftRead.trans (leftPop.trans (leftDone.trans finish))))))))

end Silmaril.Cerberus.Core.DiagnosticOperands
