module

public import Silmaril.Machine.X86.RelIsa.Defs

/-!
# Proofs: demonic reachability (`Must`) and same-state refinement (`Le`)

Names are in `Silmaril.Machine.X86.RelIsa`, so that the header `RelIsa/Thms.lean` exports them.

* `Must.step_iff_outcomes`, `Must.ofOutcomes`, `Must.mono`, `Must.bind`, `Must.of_le`,
  `Must.exists_run`;
* `Le.refl`, `Le.trans`, `Le.live_iff`;
* the deterministic case: `progress_ofIsa`, `must_ofIsa_of_runsIn`, `runsIn_of_must_ofIsa`,
  `must_ofIsa_iff`.
-/

@[expose] public section

namespace Silmaril.Machine.X86.RelIsa

open Silmaril.X86.SegVC (Isa)
open Silmaril.Machine.X86.FnContract (RunsIn)

variable {σ : Type} {A C B : RelIsa σ} {R R' Q Q' Q₁ Q₂ : σ → Prop} {s : σ}

/-! ## `Must` -/

/-- The step case of `Must`, as in the design note: every outcome is an `ok` whose state
satisfies `Must`. -/
theorem Must.step_iff_outcomes :
    (¬ A.step s .stop ∧ ∀ t, A.step s (.ok t) → Must A R Q t) ↔
      ∀ r, A.step s r → ∃ t, r = .ok t ∧ Must A R Q t := by
  constructor
  · rintro ⟨hs, h⟩ r hr
    cases r with
    | ok t => exact ⟨t, rfl, h t hr⟩
    | stop => exact absurd hr hs
  · intro h
    refine ⟨fun hr => ?_, fun t hr => ?_⟩
    · obtain ⟨_, e, _⟩ := h _ hr; cases e
    · obtain ⟨_, e, ht⟩ := h _ hr; cases e; exact ht

/-- Build a step of `Must` from the outcome form. -/
theorem Must.ofOutcomes (hR : R s) (h : ∀ r, A.step s r → ∃ t, r = .ok t ∧ Must A R Q t) :
    Must A R Q s :=
  let h' := Must.step_iff_outcomes.2 h
  .step hR h'.1 h'.2

/-- Weaken the step condition and the target. -/
theorem Must.mono (hR : ∀ s, R s → R' s) (hQ : ∀ s, Q s → Q' s) (h : Must A R Q s) :
    Must A R' Q' s := by
  induction h with
  | done hq => exact .done (hQ _ hq)
  | step hr hs _ ih => exact .step (hR _ hr) hs ih

/-- **Sequential composition.** -/
theorem Must.bind (h : Must A R Q₁ s) (k : ∀ t, Q₁ t → Must A R Q₂ t) : Must A R Q₂ s := by
  induction h with
  | done hq => exact k _ hq
  | step hr hs _ ih => exact .step hr hs ih

/-- **Transfer along refinement**: a `Must` property of `A` holds for every live `C` with
fewer behaviours. -/
theorem Must.of_le (h : Le C A) (hl : C.live s) (hm : Must A R Q s) : Must C R Q s := by
  induction hm with
  | done hq => exact .done hq
  | step hr hs _ ih =>
    exact .step hr (fun hc => hs (h.step hl hc))
      (fun t ht => ih t (h.step hl ht) (C.live_step hl ht))

/-- **Extract a run** from a `Must` property of a machine that always has an outcome. -/
theorem Must.exists_run (hp : Progress C) (hl : C.live s) (hm : Must C R Q s) :
    ∃ t, RunsInR C R s t ∧ Q t := by
  induction hm with
  | done hq => exact ⟨_, .refl _, hq⟩
  | @step s hr hs _ ih =>
    obtain ⟨r, hr'⟩ := hp s hl
    cases r with
    | stop => exact absurd hr' hs
    | ok t =>
      obtain ⟨u, hu, hq⟩ := ih t hr' (C.live_step hl hr')
      exact ⟨u, .step hr hr' hu, hq⟩

/-! ## `Le` -/

theorem Le.refl (A : RelIsa σ) : Le A A := ⟨rfl, fun _ h => h⟩

theorem Le.live_iff (h : Le C A) : C.live = A.live := by
  rw [show C.live = C.toViews.live from rfl, h.views]

theorem Le.trans (h₁ : Le C B) (h₂ : Le B A) : Le C A :=
  ⟨h₁.views.trans h₂.views, fun hl hs =>
    h₂.step (by rw [← h₁.live_iff]; exact hl) (h₁.step hl hs)⟩

/-! ## Deterministic machines -/

variable {I : Isa σ}

theorem ofIsa_step_iff {r : Res σ} :
    (ofIsa I).step s r ↔ (match I.step s with | some t => r = .ok t | none => r = .stop) :=
  Iff.rfl

theorem ofIsa_step_ok {t : σ} : (ofIsa I).step s (.ok t) ↔ I.step s = some t := by
  show (match I.step s with | some t' => Res.ok t = .ok t' | none => Res.ok t = .stop) ↔ _
  cases I.step s with
  | some t' => simp [eq_comm]
  | none => simp

theorem ofIsa_step_stop : (ofIsa I).step s .stop ↔ I.step s = none := by
  show (match I.step s with | some t' => Res.stop = .ok t' | none => Res.stop = .stop) ↔ _
  cases I.step s with
  | some t' => simp
  | none => simp

/-- A deterministic machine always has an outcome. -/
theorem progress_ofIsa : Progress (ofIsa I) := by
  intro s _
  cases e : I.step s with
  | some t => exact ⟨.ok t, ofIsa_step_ok.2 e⟩
  | none => exact ⟨.stop, ofIsa_step_stop.2 e⟩

/-- A terminating run of a deterministic machine is a `Must` run (the machine has exactly
the step the run took). -/
theorem must_ofIsa_of_runsIn {t : σ} (h : RunsIn I R s t) (hq : Q t) : Must (ofIsa I) R Q s := by
  induction h with
  | refl => exact .done hq
  | step hr he _ ih =>
    refine .step hr (fun hs => ?_) (fun u hu => ?_)
    · rw [ofIsa_step_stop] at hs; simp [hs] at he
    · rw [ofIsa_step_ok, he] at hu; cases hu; exact ih hq

/-- A `Must` run of a deterministic machine is a run of it. -/
theorem runsIn_of_must_ofIsa (h : Must (ofIsa I) R Q s) : ∃ t, RunsIn I R s t ∧ Q t := by
  induction h with
  | done hq => exact ⟨_, .refl _, hq⟩
  | @step s hr hs _ ih =>
    cases e : I.step s with
    | none => exact absurd (ofIsa_step_stop.2 e) hs
    | some u =>
      obtain ⟨v, hv, hq⟩ := ih u (ofIsa_step_ok.2 e)
      exact ⟨v, .step hr e hv, hq⟩

/-- On a deterministic machine, `Must` is exactly a run. -/
theorem must_ofIsa_iff : Must (ofIsa I) R Q s ↔ ∃ t, RunsIn I R s t ∧ Q t :=
  ⟨runsIn_of_must_ofIsa, fun ⟨_, h, hq⟩ => must_ofIsa_of_runsIn h hq⟩

end Silmaril.Machine.X86.RelIsa
