module

public import Silmaril.Cerberus.Core.Administrative.Continuation.Defs

@[expose] public section
namespace Silmaril.Cerberus.Core.Administrative
open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics

theorem callfree_append (control : Control) (first second : List Frame) :
    controlHasCCall control (first ++ second) =
      (controlHasCCall control first || controlHasCCall (.value .unit) second) := by
  conv_lhs => rw [controlHasCCall.eq_def]
  conv_rhs =>
    arg 1
    rw [controlHasCCall.eq_def]
  conv_rhs =>
    arg 2
    rw [controlHasCCall.eq_def]
  simp only [List.any_append, Bool.false_or, Bool.or_assoc]

private theorem or_swap (first second third : Bool) :
    ((first || second) || third) = ((first || third) || (second || false)) := by
  cases first <;> cases second <;> cases third <;> rfl

theorem inactive_append (control : Control) (first second : List Frame) :
    activeCall control (first ++ second) = (activeCall control first || activeCall (.value .unit) second) := by
  conv_lhs => rw [activeCall.eq_def]
  conv_rhs =>
    arg 1
    rw [activeCall.eq_def]
  conv_rhs =>
    arg 2
    rw [activeCall.eq_def]
  rw [List.any_append]
  exact or_swap _ _ _

theorem Plain.extended {state : Dynamics.State} (plain : Plain state) (outer : List Frame)
    (framesPlain : PlainFrames outer) : Plain (extend state outer) := by
  constructor
  · exact plain.unwrapped
  · change controlHasCCall state.control (state.stack ++ outer) = false
    rw [callfree_append, plain.callfree, framesPlain.1]
    rfl
  · change activeCall state.control (state.stack ++ outer) = false
    rw [inactive_append, plain.inactive, framesPlain.2]
    rfl

theorem annotationsOnly_append (first second : List Frame) :
    annotationsOnly (first ++ second) =
      (annotationsOnly first).bind (fun accesses => (annotationsOnly second).map (accesses ++ ·)) := by
  induction first with
  | nil => simp [annotationsOnly]
  | cons frame rest ih =>
    cases frame <;> simp only [List.cons_append, annotationsOnly, Option.bind_none]
    cases found : annotationsOnly rest <;>
      simp [ih, found, Option.map_map, Function.comp_def, List.append_assoc]

theorem NotDone.extended {state : Dynamics.State} (running : NotDone state) (outer : List Frame) :
    NotDone (extend state outer) := by
  intro value accesses controlEq annotationsEq
  have empty : annotationsOnly state.stack = none := by
    cases found : annotationsOnly state.stack with
    | none => rfl
    | some inner => exact (running value inner controlEq found).elim
  have absent : annotationsOnly (state.stack ++ outer) = none := by
    rw [annotationsOnly_append, empty]
    rfl
  have impossible : (none : Option (List Access)) = some accesses := absent.symm.trans annotationsEq
  cases impossible

/-- Reuse a uniform actual edge in a structurally call-free internal
continuation. Later external continuations remain universally quantified. -/
theorem Edge.extended {file : Program} {labels : Labels} {source target : Dynamics.State}
    (edge : Edge file labels source target) (outer : List Frame) (framesPlain : PlainFrames outer) :
    Edge file labels (extend source outer) (extend target outer) := by
  cases edge with
  | next sourcePlain running targetPlain requested =>
    apply Edge.next (sourcePlain.extended outer framesPlain) (running.extended outer)
      (targetPlain.extended outer framesPlain)
    intro suffix
    simpa only [extend, List.append_assoc] using requested (outer ++ suffix)
  | choose sourcePlain running targetPlain requested =>
    apply Edge.choose (sourcePlain.extended outer framesPlain) (running.extended outer)
      (targetPlain.extended outer framesPlain)
    intro suffix
    simpa only [extend, List.append_assoc] using requested (outer ++ suffix)
  | update sourcePlain running targetPlain requested =>
    apply Edge.update (sourcePlain.extended outer framesPlain) (running.extended outer)
      (targetPlain.extended outer framesPlain)
    intro suffix
    simpa only [extend, List.append_assoc] using requested (outer ++ suffix)

theorem Path.extended {file : Program} {labels : Labels} {source target : Dynamics.State}
    (path : Path file labels source target) (outer : List Frame) (framesPlain : PlainFrames outer) :
    Path file labels (extend source outer) (extend target outer) := by
  induction path with
  | refl plain => exact .refl (plain.extended outer framesPlain)
  | cons edge _ ih => exact .cons (edge.extended outer framesPlain) ih

end Silmaril.Cerberus.Core.Administrative
