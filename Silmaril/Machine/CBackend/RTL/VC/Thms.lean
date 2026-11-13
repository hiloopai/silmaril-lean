module

public import Silmaril.Raw.Machine.CBackend.RTL.VC
public import Silmaril.Machine.CBackend.RTL.Construct.Defs
@[expose] public section
namespace Silmaril.Machine.CBackend.RTL.VC

open Silmaril.Machine.RTL
open Silmaril.Machine.Lir (Word Memory)
open ProgramVC.RTL

/-- Reading distinct parameters after entry recovers the supplied argument list.
Distinctness matters: repeated parameters receive the last value written. -/
theorem writeAll_values : ∀ {registers : List Nat} {arguments : List Word}
    {before after : Frame Nat}, registers.Nodup →
    before.writeAll registers arguments = some after →
    registers.map (fun r => (after.get r).getD 0) = arguments
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, _, h => by simp [Frame.writeAll] at h
  | _ :: _, [], _, _, _, h => by simp [Frame.writeAll] at h
  | r :: rs, v :: vs, before, after, distinct, written => by
    have tail : (before.set r v).writeAll rs vs = some after := written
    have head := writeAll_get_of_not_mem tail (List.nodup_cons.mp distinct).1
    simp only [Frame.get_set, ↓reduceIte] at head
    simp only [List.map_cons, head, Option.getD_some]
    exact congrArg (v :: ·) (writeAll_values (List.nodup_cons.mp distinct).2 tail)

/-- The singleton program's actual initialization, including argument-count failure. -/
theorem start_frame (fn : Func Nat) (arguments : List Word) (memory : Memory) :
    (ProgramVC.RTL.prog fn).start 0 arguments memory =
      (Frame.empty.writeAll fn.params arguments).map
        (fun frame => ⟨⟨0, fn.entry⟩, frame, [], memory⟩) := by
  simp [Prog.start, Prog.enter, Prog.func?, ProgramVC.RTL.prog, Option.map_map]
  rfl

/-- Total correctness from the semantic `start` operation. The parameter
distinctness obligation prevents silently replacing supplied arguments by the
last writes to duplicate parameter registers. -/
theorem sound_start {fn : Func Nat} {cuts : List (Node × ProgramVC.RTL.Cut)}
    {post pre : List Word → Memory → Prop} {budget : Nat}
    (verified : ProgramVC.RTL.vc fn cuts post pre budget) (distinct : fn.params.Nodup)
    {arguments : List Word} {memory : Memory} {initial : State Nat}
    (started : (ProgramVC.RTL.prog fn).start 0 arguments memory = some initial)
    (admitted : pre arguments memory) :
    ∃ values finalMemory,
      Behaves (ProgramVC.RTL.prog fn) initial (.returned values finalMemory) ∧ post values finalMemory := by
  rw [start_frame] at started
  cases written : Frame.empty.writeAll fn.params arguments with
  | none => simp [written] at started
  | some frame =>
    simp only [written, Option.map_some, Option.some.injEq] at started
    subst initial
    apply ProgramVC.RTL.sound verified frame memory
    · intro r member
      exact writeAll_isSome_of_mem written member
    · have values : fn.params.map (ProgramVC.RTL.valsOn fn.params frame) = arguments := by
        rw [← writeAll_values distinct written]
        apply List.map_congr_left
        intro r member
        simp only [ProgramVC.RTL.valsOn, ite_eq_left member]
      rwa [values]

/-- A proved VC discharges the non-stuck hypothesis of checked abstraction. -/
theorem not_stuck_start {fn : Func Nat} {cuts : List (Node × ProgramVC.RTL.Cut)}
    {post pre : List Word → Memory → Prop} {budget : Nat}
    (verified : ProgramVC.RTL.vc fn cuts post pre budget) (distinct : fn.params.Nodup)
    {arguments : List Word} {memory : Memory} {initial : State Nat}
    (started : (ProgramVC.RTL.prog fn).start 0 arguments memory = some initial)
    (admitted : pre arguments memory) : ¬ Behaves (ProgramVC.RTL.prog fn) initial .stuck := by
  obtain ⟨values, finalMemory, returned, _⟩ := sound_start verified distinct started admitted
  intro stuck
  have impossible := Behaves.unique returned stuck
  cases impossible

/-- Every RTL behavior of a VC-certified entry returns into the specified
postcondition; determinism excludes traps, stuckness and divergence. -/
theorem behavior_post {fn : Func Nat} {cuts : List (Node × ProgramVC.RTL.Cut)}
    {post pre : List Word → Memory → Prop} {budget : Nat}
    (verified : ProgramVC.RTL.vc fn cuts post pre budget) (distinct : fn.params.Nodup)
    {arguments : List Word} {memory : Memory} {initial : State Nat}
    (started : (ProgramVC.RTL.prog fn).start 0 arguments memory = some initial)
    (admitted : pre arguments memory) {behavior : Behavior}
    (run : Behaves (ProgramVC.RTL.prog fn) initial behavior) :
    ∃ values finalMemory, behavior = .returned values finalMemory ∧ post values finalMemory := by
  obtain ⟨values, finalMemory, returned, specified⟩ :=
    sound_start verified distinct started admitted
  exact ⟨values, finalMemory, Behaves.unique run returned, specified⟩

end Silmaril.Machine.CBackend.RTL.VC
