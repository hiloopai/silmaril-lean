module

public import Silmaril.Project.CompilesTo.Defs
public import Silmaril.Cerberus.Core.Forced.Thms
public import Silmaril.Cerberus.Core.Explore.Defs
public import Silmaril.Proofs.Project.CompilesTo.Params
public import Silmaril.Compiler.Core.Verified.Globals.Defs

/-!
# Non-vacuity: safe Core entries

`Source.Safe` quantifies over every Core run. For a concrete entry it follows from one
**forced** run (each visited state has exactly one successor) to a normal end
(`safe_of_forced`, using `Forced.terminal_unique`); `forcedRun` finds such a run by stepping
`Dynamics.successors` and is sound for it (`forcedRun_sound`), so the run itself can be checked by
evaluation. `argAlloc` and `argsMem_alloc` build the argument objects of a call the way the
verified Core library's callers do (`Params.ArgsMem`), for `Params.inv_params`.
-/

@[expose] public section

namespace Silmaril.Project.CompilesTo

open Silmaril.Compiler.CompilesTo

open Silmaril.Cerberus Silmaril.Cerberus.Core Silmaril.Cerberus.Core.Dynamics
open Silmaril.Compile.Core.Verified

/-! ## Forced runs -/

/-- Step the unique successor of each state (`Dynamics.successors`), up to `fuel` states, until
a halted state; `none` if some state has no successor or several. -/
def forcedRun (file : Program) (labels : Labels) : Nat → State → Option State
  | 0, _ => none
  | n + 1, s =>
    match s.control with
    | .halt _ => some s
    | _ =>
      match successors file labels s with
      | [(_, t)] => forcedRun file labels n t
      | _ => none

theorem forcedRun_sound {file : Program} {labels : Labels} :
    ∀ (n : Nat) (s h : State), forcedRun file labels n s = some h →
      Silmaril.Cerberus.Core.Forced.Reaches file labels s h ∧ ∃ o, h.control = .halt o
  | 0, _, _, hr => by simp [forcedRun] at hr
  | n + 1, s, h, hr => by
    unfold forcedRun at hr
    split at hr
    · rename_i o hc
      cases hr
      exact ⟨.refl, o, hc⟩
    · split at hr
      · rename_i a t hsucc
        obtain ⟨hreach, hh⟩ := forcedRun_sound n t h hr
        have hstep : Step file labels s a t :=
          (successors_correct file labels s a t).mp (by rw [hsucc]; simp)
        refine ⟨.cons hstep (fun a' t' hs' => ?_) hreach, hh⟩
        have hm := (successors_correct file labels s a' t').mpr hs'
        rw [hsucc] at hm
        simp only [List.mem_singleton, Prod.mk.injEq] at hm
        exact hm
      · cases hr

/-- **A forced run to a normal end makes the source safe**: every run follows it (so none goes
wrong, the only halted state reachable being its end) and every run is finite. -/
theorem safe_of_forced {F : FnData} {k0 : List Frame} {s h : State} {v : Val}
    (hp : Silmaril.Cerberus.Core.Forced.Reaches F.file F.labels s h)
    (hh : h.control = .halt (.defined v)) : (F.source k0).Safe s := by
  refine ⟨fun t ht hw => ?_, ?_⟩
  · obtain ⟨o, hto, hnd⟩ := hw
    have := Silmaril.Cerberus.Core.Forced.terminal_unique hp hh ht hto
    subst this
    rw [hh] at hto
    injection hto with ho
    exact hnd v ho.symm
  · induction hp with
    | refl =>
      constructor
      intro u ⟨a, hstep⟩
      cases hstep with
      | respond live _ => exact absurd hh (live _)
    | cons edge unique _ ih =>
      constructor
      intro u ⟨a, hstep⟩
      obtain ⟨-, rfl⟩ := unique a u hstep
      exact ih hh

/-! ## Argument objects -/

theorem stored_nextId (m : Mem.Concrete.State) (id addr n : Int) :
    (Locals.stored m id addr n).nextId = m.nextId := by
  obtain ⟨b, pb, hw⟩ := Mem.Concrete.writeRepresentation_shape addr
    (Mem.Concrete.plainBytes (Mem.Concrete.encodeInteger 4 n)) m
  unfold Locals.stored; rw [hw]

theorem stored_lastAddress (m : Mem.Concrete.State) (id addr n : Int) :
    (Locals.stored m id addr n).lastAddress = m.lastAddress := by
  obtain ⟨b, pb, hw⟩ := Mem.Concrete.writeRepresentation_shape addr
    (Mem.Concrete.plainBytes (Mem.Concrete.encodeInteger 4 n)) m
  unfold Locals.stored; rw [hw]

theorem stored_dead (m : Mem.Concrete.State) (id addr n : Int) :
    (Locals.stored m id addr n).dead = m.dead := by
  obtain ⟨b, pb, hw⟩ := Mem.Concrete.writeRepresentation_shape addr
    (Mem.Concrete.plainBytes (Mem.Concrete.encodeInteger 4 n)) m
  unfold Locals.stored; rw [hw]

/-- One more argument object. -/
theorem argsMem_alloc {m : Mem.Concrete.State} {objs : List (Int × Int)} {ns : List Int}
    (h : Params.ArgsMem m objs ns) (aligned : m.lastAddress % 4 = 0)
    (fresh : m.nextId ∉ m.dead) (n : Int) :
    Params.ArgsMem (argAlloc m n) (objs ++ [(m.nextId, Mem.Concrete.nextIntAddress m)])
      (ns ++ [n]) := by
  refine h.snoc aligned (fun id addr v hs hne hap => ?_) ?_ ?_ ?_
  · exact Slots.slot_stored (Slots.slot_created hs .malloc [] hne hap) _ _ _ hap
  · exact Locals.stored_slot (Locals.created_live .malloc [] m fresh) n
  · rw [argAlloc, stored_nextId, Globals.created_nextId]
  · rw [argAlloc, stored_lastAddress, Locals.created_lastAddress]

theorem argAlloc_dead (m : Mem.Concrete.State) (n : Int) : (argAlloc m n).dead = m.dead := by
  rw [argAlloc, stored_dead, Locals.created_dead]

theorem argAlloc_nextId (m : Mem.Concrete.State) (n : Int) :
    (argAlloc m n).nextId = m.nextId + 1 := by
  rw [argAlloc, stored_nextId, Globals.created_nextId]

theorem argAlloc_lastAddress (m : Mem.Concrete.State) (n : Int) :
    (argAlloc m n).lastAddress = Mem.Concrete.nextIntAddress m := by
  rw [argAlloc, stored_lastAddress, Locals.created_lastAddress]

/-- `Silmaril.Project.Shapes.C.CFn.paramDefs` is the verified Core library's `Params.paramDefs`. -/
theorem paramDefs_eq (params : List (Sym × Ctype)) (ns : List Int) :
    Silmaril.Project.Shapes.C.CFn.paramDefs params ns = Params.paramDefs (params.map (·.1)) ns := by
  funext q
  unfold Silmaril.Project.Shapes.C.CFn.paramDefs Params.paramDefs
  rw [List.zip_map_left, List.find?_map]
  simp only [Function.comp_def, Option.map_map]
  congr 2

end Silmaril.Project.CompilesTo

end
