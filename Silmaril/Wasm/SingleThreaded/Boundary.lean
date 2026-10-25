module

public import Silmaril.Wasm.SingleThreaded.Agreement

@[expose] public section

/-! # Exceptions at the boundary are traps (U27)

The component model's `call_and_trap_on_throw`: an exception that escapes the
outermost activation of a thread is reported as `.returned .trap`, never as
`stuck` or `running`.
-/

namespace Silmaril.Wasm.SingleThreaded

open Silmaril.Wasm.Execution.Core

variable {H : Type}

theorem status_throw {o : GrowOracle} {s : Store H} {f : Frame} {a : Nat} :
    status o s (.active f (throwing a)) = .returned .trap := by
  have h1 : ¬ ∃ vs, throwing a = vals vs := by
    rintro ⟨vs, h⟩
    have := congrArg splitVals h
    rw [splitVals_vals] at this
    simp [splitVals, Admin.val?] at this
  have h2 : throwing a ≠ [.trap] := by simp [throwing]
  unfold status
  dsimp only
  split
  · rename_i ha; exact absurd ha h1
  · split
    · rename_i hb; exact absurd hb h2
    · split
      · rfl
      · rename_i hc; exact absurd ⟨a, rfl⟩ hc

theorem status_trap {o : GrowOracle} {s : Store H} {f : Frame} :
    status o s (.active f [.trap]) = .returned .trap := by
  have h1 : ¬ ∃ vs, [Admin.trap] = vals vs := by
    rintro ⟨vs, h⟩
    have := congrArg splitVals h
    rw [splitVals_vals] at this
    simp [splitVals, Admin.val?] at this
  unfold status
  dsimp only
  split
  · rename_i ha; exact absurd ha h1
  · split
    · rfl
    · rename_i hb; exact absurd rfl hb

theorem status_values {o : GrowOracle} {s : Store H} {f : Frame} {vs : List Val} :
    status o s (.active f (vals vs)) = .returned (.values vs) := by
  unfold status
  dsimp only
  split
  · rename_i ha; rw [← vals_injective ha.choose_spec]
  · rename_i ha; exact absurd ⟨vs, rfl⟩ ha

/-- **Milestone.** If an invocation runs to an uncaught exception, its status is
a trap. -/
theorem invoke_throw_trap {o : GrowOracle} {s s' : Store H} {a : Nat} {args : List Val}
    {f : Frame} {e : Nat}
    (_h : Relation.ReflTransGen (Internal o) (s, Thread.invoke a args) (s', .active f (throwing e))) :
    status o s' (.active f (throwing e)) = .returned .trap :=
  status_throw

/-- An uncaught exception is never reported as `stuck` or `running`. -/
theorem throw_not_stuck {o : GrowOracle} {s : Store H} {f : Frame} {a : Nat} :
    status o s (.active f (throwing a)) ≠ .stuck ∧ status o s (.active f (throwing a)) ≠ .running := by
  rw [status_throw]
  constructor <;> intro h <;> cases h

end Silmaril.Wasm.SingleThreaded
