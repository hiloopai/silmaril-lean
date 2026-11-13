module

public import Silmaril.Wasm.Component.Reference.Engine.Core3.Agreement.Defs
public import Silmaril.Raw.Wasm.Component.Engine.Core3.Extends
public import Silmaril.Wasm.SingleThreaded.Exec.InterpTyped

/-!
# The concrete Core 3.0 engine agrees with the single-threaded machine on typed threads

The internal step of `core3 o` is the graph of the interpreter step,
`internalC (stepI o) c = some c'`; the single-threaded machine's internal step
`SingleThreaded.Internal o` is the relational host-free Core step in the deterministic profile
with grow oracle `o` (`SingleThreaded.profile o`). On typed threads
(`SingleThreaded.ThreadOk s t ts`, i.e. `ConfigOk` of the thread's configuration):

* `core3_internal_sound`: every engine step is a machine step (`stepI_sound_typed`);
* `core3_internal_complete`: every machine step `y` is matched by the engine step `y'`, up to
  one more machine step from `y` to `y'` (`Relation.ReflGen`): the relational step may stop
  half-way through the bubbling of a `trap` or an exception that the interpreter does in one
  step (`stepI_maximal`); the machine is deterministic only up to this bubbling
  (`Internal.deterministic`, SingleThreaded/Determinism.lean);
* `core3_steps_sound`: engine runs are machine runs (typing is preserved along the run,
  `Internal.preserves`);
* `statusE_eq`: the engine status is the flat view (`flatStatus`) of the machine status
  `SingleThreaded.status o` (`statusI_eq_typed`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Engine.Core3

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation

variable {H : Type}

/-- On a typed thread, every internal step of the single-threaded machine is matched by the
internal step of the concrete engine, up to one more machine step. -/
theorem core3_internal_complete {o : SingleThreaded.GrowOracle} {s : Store H}
    {t : SingleThreaded.Thread} {ts : List CValType} {y : Store H × SingleThreaded.Thread}
    (ht : SingleThreaded.ThreadOk s t ts) (h : SingleThreaded.Internal o (s, t) y) :
    ∃ y', SingleThreaded.internalC (SingleThreaded.Exec.stepI o) (s, t) = some y' ∧
      Relation.ReflGen (SingleThreaded.Internal o) y y' := by
  obtain ⟨s', t'⟩ := y
  obtain ⟨f', code', rfl, hst⟩ := h
  obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp (SingleThreaded.Exec.stepI_complete_typed ht hst)
  have hm := SingleThreaded.Exec.stepI_maximal (SingleThreaded.ConfigOk.storeOk ht)
    (SingleThreaded.Exec.ConfigOk.deepAll_iHeadInv ht) hst hd
  refine ⟨(d.store, .active d.frame d.code), ?_, ?_⟩
  · show Option.map _ (SingleThreaded.Exec.stepI o (t.config s)) = _
    rw [hd]
    rfl
  · rcases hm with _ | hm
    · exact .refl
    · exact .single ⟨d.frame, d.code, rfl, hm⟩

/-- On a typed thread, runs of the concrete engine are runs of the single-threaded machine. -/
theorem core3_steps_sound {o : SingleThreaded.GrowOracle} {s : Store H}
    {t : SingleThreaded.Thread} {ts : List CValType} {y : Store H × SingleThreaded.Thread}
    (ht : SingleThreaded.ThreadOk s t ts) (h : (core3 o).Steps (s, t) y) :
    Relation.ReflTransGen (SingleThreaded.Internal o) (s, t) y := by
  suffices ∀ y, (core3 o).Steps (s, t) y →
      Relation.ReflTransGen (SingleThreaded.Internal o) (s, t) y ∧
        SingleThreaded.ThreadOk y.1 y.2 ts from (this y h).1
  intro y hy
  induction hy with
  | refl => exact ⟨.refl, ht⟩
  | @tail b c _ step ih =>
    obtain ⟨hr, hb⟩ := ih
    have hi := core3_internal_sound (s := b.1) (t := b.2) hb step
    have hs : StoreOk b.1 := by
      have := SingleThreaded.ConfigOk.storeOk hb
      have e := SingleThreaded.Thread.config_store (H := H) b.1 b.2
      rwa [e] at this
    obtain ⟨-, hc, -⟩ := SingleThreaded.Internal.preserves (s' := c.1) (t' := c.2) hs hb hi
    exact ⟨hr.tail hi, hc⟩

end Silmaril.Wasm.Component.Engine.Core3
