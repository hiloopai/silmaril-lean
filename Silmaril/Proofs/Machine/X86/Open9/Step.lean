module

public import Silmaril.Proofs.Machine.X86.Open9.Law

/-!
# `Ext9` runs are `Open9` runs

A retirement of `Ext9.stepOpt exit` and the return to `exit` are `Open9` steps, so a callee
proved under `Ext9.Returns R` (or `Ext8.Returns`, `Ext.Returns`) is an `Open9` run ending at
`rip = R` (`returns_open9`).
-/

@[expose] public section

namespace Silmaril.Proofs.Machine.X86.Open9

open Silmaril.X86 (State MState Word Byte)
open Silmaril.Machine.Execution (run Reaches)
open Silmaril.Machine.X86
open Silmaril.Machine.X86.Open9

theorem fetch8_of_step_undecodable {exit : Word} {m : MState}
    (h : Silmaril.X86.Ext8.step exit m = .ext .undecodable) :
    Silmaril.X86.Ext8.fetch m.memory m.core.rip.toNat = .inl .undecodable := by
  unfold Silmaril.X86.Ext8.step at h
  split at h
  · rename_i e; exact e
  · cases h
  · rename_i i n e
    exfalso
    have hf : Silmaril.X86.Ext.fetch m.memory m.core.rip.toNat = .decoded i n := by
      unfold Silmaril.X86.Ext8.fetch at e
      generalize hg : Silmaril.X86.Ext.fetch m.memory m.core.rip.toNat = g at e
      cases g with
      | decoded i' n' => simp only [Sum.inl.injEq, Silmaril.X86.Ext.Fetch.decoded.injEq] at e; rw [e.1, e.2]
      | truncated => simp at e
      | undecodable =>
        simp only at e
        split at e
        · split at e <;> cases e
        · cases e
    simp only [Silmaril.X86.Ext8.Outcome.ext.injEq] at h
    unfold Silmaril.X86.Ext.step at h
    rw [hf] at h
    simp only at h
    split at h
    · split at h <;> cases h
    all_goals cases h
  · rename_i i n e
    split at h <;> cases h

theorem step_of_ext9_stepOpt {exit : Word} {m n : MState}
    (h : Ext9.stepOpt exit m = some n) : step m = some n := by
  unfold Ext9.stepOpt at h
  split at h
  · rename_i k e
    simp only [Option.some.injEq] at h; subst h
    unfold Ext9.step at e
    split at e
    · split at e
      · split at e <;> cases e
      · cases e
      · cases e
    · exact step_of_open (Open.step_of_ext8_stepOpt (exit := exit)
        (by simp [Silmaril.X86.Ext8.stepOpt, Ext9.Outcome.ext8.inj e]))
  · rename_i k e
    simp only [Option.some.injEq] at h; subst h
    unfold Ext9.step at e
    split at e
    · split at e
      · split at e <;> cases e
      · cases e
      · cases e
    · exact step_of_open (Open.step_of_ext8_stepOpt (exit := exit)
        (by simp [Silmaril.X86.Ext8.stepOpt, Ext9.Outcome.ext8.inj e]))
  · rename_i k e
    simp only [Option.some.injEq] at h; subst h
    unfold Ext9.step at e
    split at e
    · rename_i hu
      split at e
      · rename_i i l hf
        split at e
        · rename_i c mem hx
          simp only [Ext9.Outcome.retired.injEq] at e
          subst e
          simp [step, fetch8_of_step_undecodable hu, hf, hx, Open.ofResult]
        · cases e
      · cases e
      · cases e
    · cases e
  · cases h

theorem step_of_ext9_returned {exit : Word} {m n : MState}
    (h : Ext9.step exit m = .ext8 (.ext (.returned n))) : step m = some n := by
  unfold Ext9.step at h
  split at h
  · split at h
    · split at h <;> cases h
    · cases h
    · cases h
  · exact step_of_open (Open.step_of_ext8_returned (Ext9.Outcome.ext8.inj h))

theorem reaches_of_ext9 {exit : Word} : ∀ (k : Nat) {a b : MState},
    run (Ext9.stepOpt exit) k a = some b → Reaches step a b
  | 0, a, b, h => by
    simp only [run, Option.some.injEq] at h; subst h; exact ⟨0, rfl⟩
  | k + 1, a, b, h => by
    simp only [run] at h
    cases e : Ext9.stepOpt exit a with
    | none => simp [e] at h
    | some c =>
      rw [e] at h
      simp only [Option.bind_some] at h
      obtain ⟨j, hj⟩ := reaches_of_ext9 k h
      exact ⟨j + 1, by simp [run, step_of_ext9_stepOpt e, hj]⟩

theorem returns_open9 {R : Word} {m m' : MState} (h : Ext9.Returns R m m') :
    Reaches step m m' ∧ m'.core.rip = R := by
  obtain ⟨k, mid, hrun, hstep⟩ := h
  have hr := reaches_of_ext9 k hrun
  have hs := step_of_ext9_returned hstep
  refine ⟨hr.trans ⟨1, by simp [run, hs]⟩, ?_⟩
  -- the return popped `R`
  unfold Ext9.step at hstep
  split at hstep
  · split at hstep
    · split at hstep <;> cases hstep
    · cases hstep
    · cases hstep
  · exact (Open.returns_open ⟨0, mid, rfl, Ext9.Outcome.ext8.inj hstep⟩).2

end Silmaril.Proofs.Machine.X86.Open9
