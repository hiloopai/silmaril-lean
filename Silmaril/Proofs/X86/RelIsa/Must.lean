module

public import Silmaril.X86.RelIsa.Defs

/-!
# Proofs: demonic reachability, refinement and simulation of relational machines

The header is `Silmaril/X86/RelIsa/Thms.lean`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.RelIsa

open Silmaril.X86 (RelIsa)
open Silmaril.X86.RelIsa
open Silmaril.X86.SegVC (Isa)
open Silmaril.X86.FnContract (RunsIn AbiEntry Spec)

variable {σ τ υ : Type} {A C B : RelIsa σ} {R R' Q Q' Q₁ Q₂ : σ → Prop} {s : σ}

/-! ## `Must` -/

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

theorem Must.mono (hR : ∀ s, R s → R' s) (hQ : ∀ s, Q s → Q' s) (h : Must A R Q s) :
    Must A R' Q' s := by
  induction h with
  | done hq => exact .done (hQ _ hq)
  | step hr hs _ ih => exact .step (hR _ hr) hs ih

theorem Must.bind (h : Must A R Q₁ s) (k : ∀ t, Q₁ t → Must A R Q₂ t) : Must A R Q₂ s := by
  induction h with
  | done hq => exact k _ hq
  | step hr hs _ ih => exact .step hr hs ih

theorem Must.of_le (h : Le C A) (hl : C.live s) (hm : Must A R Q s) : Must C R Q s := by
  induction hm with
  | done hq => exact .done hq
  | step hr hs _ ih =>
    exact .step hr (fun hc => hs (h.step hl hc))
      (fun t ht => ih t (h.step hl ht) (C.live_step hl ht))

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

theorem not_must_of_stop (hQ : ¬ Q s) (hs : A.step s .stop) : ¬ Must A R Q s := by
  intro h
  cases h with
  | done h => exact hQ h
  | step _ hns _ => exact hns hs

/-! ## `Le` -/

theorem Le.live_iff (h : Le C A) : C.live = A.live := by
  rw [show C.live = C.toViews.live from rfl, h.views]

theorem Le.trans (h₁ : Le C B) (h₂ : Le B A) : Le C A :=
  ⟨h₁.views.trans h₂.views, fun hl hs =>
    h₂.step (by rw [← Le.live_iff h₁]; exact hl) (h₁.step hl hs)⟩

/-! ## Deterministic machines -/

variable {I : Isa σ}

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

theorem progress_ofIsa : Progress (ofIsa I) := by
  intro s _
  cases e : I.step s with
  | some t => exact ⟨.ok t, ofIsa_step_ok.2 e⟩
  | none => exact ⟨.stop, ofIsa_step_stop.2 e⟩

theorem must_ofIsa_of_runsIn {t : σ} (h : RunsIn I R s t) (hq : Q t) :
    Must (ofIsa I) R Q s := by
  induction h with
  | refl => exact .done hq
  | step hr he _ ih =>
    refine .step hr (fun hs => ?_) (fun u hu => ?_)
    · rw [ofIsa_step_stop] at hs; simp [hs] at he
    · rw [ofIsa_step_ok, he] at hu; cases hu; exact ih hq

theorem runsIn_of_must_ofIsa (h : Must (ofIsa I) R Q s) : ∃ t, RunsIn I R s t ∧ Q t := by
  induction h with
  | done hq => exact ⟨_, .refl _, hq⟩
  | @step s hr hs _ ih =>
    cases e : I.step s with
    | none => exact absurd (ofIsa_step_stop.2 e) hs
    | some u =>
      obtain ⟨v, hv, hq⟩ := ih u (ofIsa_step_ok.2 e)
      exact ⟨v, .step hr e hv, hq⟩

/-! ## Simulations -/

theorem ResRel.refl_eq (r : Res σ) : ResRel Eq r r := by
  cases r <;> simp [ResRel]

theorem ResRel.comp {R₁ : υ → τ → Prop} {R₂ : τ → σ → Prop} {r : Res υ} {r' : Res τ}
    {r'' : Res σ} (h₁ : ResRel R₁ r r') (h₂ : ResRel R₂ r' r'') :
    ResRel (fun c a => ∃ b, R₁ c b ∧ R₂ b a) r r'' := by
  cases r <;> cases r' <;> cases r'' <;> simp_all [ResRel]
  exact ⟨_, h₁, h₂⟩

theorem Sim.of_le (h : Le C A) : Sim C A Eq where
  live := by
    rintro c a rfl hl
    rw [← Le.live_iff h]; exact hl
  step := by
    rintro c a r rfl hl hs
    exact ⟨r, h.step hl hs, ResRel.refl_eq r⟩

theorem Sim.comp {C : RelIsa υ} {B : RelIsa τ} {A : RelIsa σ} {R₁ : υ → τ → Prop}
    {R₂ : τ → σ → Prop} (h₁ : Sim C B R₁) (h₂ : Sim B A R₂) :
    Sim C A (fun c a => ∃ b, R₁ c b ∧ R₂ b a) where
  live := by
    rintro c a ⟨b, hcb, hba⟩ hl
    exact h₂.live hba (h₁.live hcb hl)
  step := by
    rintro c a r ⟨b, hcb, hba⟩ hl hs
    obtain ⟨r', hb, hr'⟩ := h₁.step hcb hl hs
    obtain ⟨r'', ha, hr''⟩ := h₂.step hba (h₁.live hcb hl) hb
    exact ⟨r'', ha, ResRel.comp hr' hr''⟩

theorem Must.of_sim {C : RelIsa τ} {A : RelIsa σ} {Rel : τ → σ → Prop} {R : σ → Prop}
    {R' : τ → Prop} {Q : σ → Prop} (h : Sim C A Rel) (hR : ∀ c a, Rel c a → R a → R' c)
    {c : τ} {a : σ} (hr : Rel c a) (hl : C.live c) (hm : Must A R Q a) :
    Must C R' (fun c' => ∃ a', Rel c' a' ∧ Q a') c := by
  induction hm generalizing c with
  | done hq => exact .done ⟨_, hr, hq⟩
  | @step a hRa hns _ ih =>
    refine .step (hR c a hr hRa) (fun hc => ?_) (fun c' hc' => ?_)
    · obtain ⟨r', ha, hrel⟩ := h.step hr hl hc
      cases r' with
      | ok _ => exact hrel.elim
      | stop => exact hns ha
    · obtain ⟨r', ha, hrel⟩ := h.step hr hl hc'
      cases r' with
      | ok t => exact ih t ha hrel (C.live_step hl hc')
      | stop => exact hrel.elim

/-! ## Demonic total correctness -/

theorem mustTotalIn_of_le {S : Spec σ} {P : σ → σ → Prop} (hle : Le C A)
    (h : S.MustTotalIn A P) : S.MustTotalIn C P := by
  intro s hl ha he
  have hv := hle.views
  have hlA : A.live s := by rw [← Le.live_iff hle]; exact hl
  have ha' : AbiEntry (A.core s) (A.mem s) := by
    rw [show A.core = C.core from congrArg Views.core hv.symm,
      show A.mem = C.mem from congrArg Views.mem hv.symm]
    exact ha
  have hm := h s hlA ha' he
  rw [← hv] at hm
  exact Must.of_le hle hl hm

end Silmaril.Proofs.X86.RelIsa
