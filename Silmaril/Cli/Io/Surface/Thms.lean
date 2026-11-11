module

public import Silmaril.Cli.Io.Surface.Defs

/-!
# The front-end checks of pinned tools are sound

* **`Tool.check_sound`**: `Tool.check t body` is sound for `Tool.spec t S` when each
  `body inv` is sound for `S inv`; **`Tool.frontCheck_sound`**: the front-end check
  `Tool.frontCheck` is sound for `Tool.frontSpec`.
* `Tool.spec_mono`: refining the runs refines the tool.

A Silmaril addition.
-/

@[expose] public section

namespace Silmaril.Cli.Surface

open Silmaril.Cli Silmaril.Cli.Io

/-- A snapshot with no changed file shows `snapObs`. -/
theorem snapObs_agrees {s : Snap} (i : Input) (h : s.files = []) : s.Agrees i (snapObs s i) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  funext q
  simp [Snap.fs, snapObs, h]

/-- A non-run outcome whose front-end test passes is allowed. -/
theorem Tool.front_sound (t : Tool) (body : Invocation → Spec) {i : Input} {s : Snap}
    {res : Outcome} (hres : t.root.parse i.args = res) (hr : ∀ inv, res ≠ .run inv)
    (h : (decide (t.FrontOut res (snapObs s i)) && s.files.isEmpty) = true) :
    ∃ o, s.Agrees i o ∧ t.spec body i o := by
  have hc : t.FrontOut res (snapObs s i) ∧ s.files = [] := by simpa using h
  refine ⟨snapObs s i, snapObs_agrees i hc.2, ?_⟩
  unfold Tool.spec
  rw [hres]
  cases res with
  | run inv => exact absurd rfl (hr inv)
  | _ => exact ⟨hc.1, rfl⟩

/-- **`Tool.check` is sound for `Tool.spec`.** -/
theorem Tool.check_sound (t : Tool) {body : Invocation → Check} {S : Invocation → Spec}
    (h : ∀ inv, (body inv).Sound (S inv)) : (t.check body).Sound (t.spec S) := by
  intro i s hs
  unfold Tool.check at hs
  rcases hres : t.root.parse i.args with inv | p | p | p | m <;> rw [hres] at hs
  · obtain ⟨o, hag, ho⟩ := h inv i s hs
    exact ⟨o, hag, by unfold Tool.spec; rw [hres]; exact ho⟩
  · exact t.front_sound S hres (fun _ => Outcome.noConfusion) hs
  · exact t.front_sound S hres (fun _ => Outcome.noConfusion) hs
  · exact t.front_sound S hres (fun _ => Outcome.noConfusion) hs
  · exact t.front_sound S hres (fun _ => Outcome.noConfusion) hs

/-- **The front-end check is sound for the front-end spec.** -/
theorem Tool.frontCheck_sound (t : Tool) : t.frontCheck.Sound t.frontSpec :=
  t.check_sound fun _ i s _ =>
    ⟨{ stdout := s.stdout, stderr := s.stderr, exit := s.exit, fs := s.fs i },
      ⟨rfl, rfl, rfl, rfl⟩, trivial⟩

/-- Refining the runs refines the tool. -/
theorem Tool.spec_mono (t : Tool) {S T : Invocation → Spec} (h : ∀ inv, S inv ≤ T inv) :
    t.spec S ≤ t.spec T := by
  intro i o hs
  unfold Tool.spec at hs ⊢
  split
  · next inv hinv => rw [hinv] at hs; exact h inv i o hs
  · next res hnot =>
    split at hs
    · next inv hinv => exact absurd hinv (hnot inv)
    · exact hs

end Silmaril.Cli.Surface

end
