module

public import Silmaril.Proofs.Machine.X86.RelIsa.Must

/-!
# Proofs: forward simulations (`Sim`) and the transfer of `Must` along them

Names are in `Silmaril.Machine.X86.RelIsa`, so that the header `RelIsa/Thms.lean` exports them.

* `ResRel.refl_eq`, `ResRel.comp`;
* `Sim.of_le`, `Sim.refl`, `Sim.comp`;
* `Must.of_sim`: a `Must` property of the abstract machine holds for every concrete live
  state related to the abstract one, with the target transported along the relation.
-/

@[expose] public section

namespace Silmaril.Machine.X86.RelIsa

variable {σ τ υ : Type}

theorem ResRel.refl_eq (r : Res σ) : ResRel Eq r r := by
  cases r <;> simp [ResRel]

theorem ResRel.comp {R₁ : υ → τ → Prop} {R₂ : τ → σ → Prop} {r : Res υ} {r' : Res τ}
    {r'' : Res σ} (h₁ : ResRel R₁ r r') (h₂ : ResRel R₂ r' r'') :
    ResRel (fun c a => ∃ b, R₁ c b ∧ R₂ b a) r r'' := by
  cases r <;> cases r' <;> cases r'' <;> simp_all [ResRel]
  exact ⟨_, h₁, h₂⟩

/-- Same-state refinement is a simulation along equality. -/
theorem Sim.of_le {C A : RelIsa σ} (h : Le C A) : Sim C A Eq where
  live := by
    rintro c a rfl hl
    rw [← h.live_iff]; exact hl
  step := by
    rintro c a r rfl hl hs
    exact ⟨r, h.step hl hs, ResRel.refl_eq r⟩

theorem Sim.refl (A : RelIsa σ) : Sim A A Eq := Sim.of_le (Le.refl A)

/-- Simulations compose. -/
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

/-- **Transfer along a simulation.** If the abstract machine `A` must reach `Q` from `a`,
every live concrete state `c` related to `a` must reach a state related to a `Q`-state, and
its steps are taken from `R'`-states as long as `R'` follows from `R` along the relation. -/
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

end Silmaril.Machine.X86.RelIsa
