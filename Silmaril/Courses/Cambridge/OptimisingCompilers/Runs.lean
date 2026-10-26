module

public import Silmaril.Courses.Cambridge.OptimisingCompilers.ThreeAddress

/-! # Runs of 3-address flowgraphs: unfolding and simulation lemmas

Helper lemmas about the small-step semantics of `ThreeAddress`:

* `step_pc_mem_succ`: a step moves along a flowgraph edge;
* `traces_of_step`, `outcomes_of_step`, `traces_of_halted`,
  `outcomes_of_halted`: one-step unfolding of the observations of a run;
* `obsEquiv_of_step`, `obsEquiv_silent_left`, `obsEquiv_silent_right`,
  `obsEquiv_of_halted`: building observational equivalences step by step,
  used for the worked examples;
* `sim_traces_outcomes`: a lock-step simulation between two flowgraphs (over
  possibly different variables and nodes) preserves traces and outcomes.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.OptimisingCompilers

namespace Flowgraph

variable {V ι : Type*} [DecidableEq V] (G : Flowgraph V ι)

/-- A step moves to a successor of the current node. -/
theorem step_pc_mem_succ {s s' : Config V ι} {o : Option ℤ} (h : G.step s = some (o, s')) :
    s'.pc ∈ G.succ s.pc := by
  unfold step at h
  show s'.pc ∈ (G.code s.pc).succs
  cases hc : G.code s.pc with
  | exit rs => simp [hc, Instr.exec] at h
  | cmp c a b t f =>
    simp only [hc, Instr.exec, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp only [Instr.succs, List.mem_cons, List.not_mem_nil, or_false]
    split <;> simp
  | _ =>
    simp only [hc, Instr.exec, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨-, rfl⟩ := h
    simp [Instr.succs]

theorem not_halted_of_step {s s' : Config V ι} {o : Option ℤ} (h : G.step s = some (o, s')) :
    ¬ G.Halted s := by
  rw [← step_eq_none_iff, h]
  simp

theorem exists_step_of_not_halted {s : Config V ι} (h : ¬ G.Halted s) :
    ∃ o s', G.step s = some (o, s') := by
  rw [← step_eq_none_iff] at h
  obtain ⟨⟨o, s'⟩, hs⟩ := Option.ne_none_iff_exists'.1 h
  exact ⟨o, s', hs⟩

/-- One-step unfolding of the traces. -/
theorem traces_of_step {s s' : Config V ι} {o : Option ℤ} (h : G.step s = some (o, s')) :
    G.traces s = insert [] ((o.toList ++ ·) '' G.traces s') := by
  ext w
  constructor
  · rintro ⟨t, ht⟩
    cases ht with
    | refl => exact Or.inl rfl
    | head h₁ h₂ =>
      rw [h] at h₁
      simp only [Option.some.injEq, Prod.mk.injEq] at h₁
      obtain ⟨rfl, rfl⟩ := h₁
      exact Or.inr ⟨_, ⟨_, h₂⟩, rfl⟩
  · rintro (rfl | ⟨w', ⟨t, ht⟩, rfl⟩)
    · exact ⟨s, .refl s⟩
    · exact ⟨t, .head h ht⟩

/-- The traces of a halted configuration. -/
theorem traces_of_halted {s : Config V ι} (h : G.Halted s) : G.traces s = {[]} := by
  ext w
  constructor
  · rintro ⟨t, ht⟩
    cases ht with
    | refl => rfl
    | head h₁ _ => exact absurd h (G.not_halted_of_step h₁)
  · rintro rfl
    exact ⟨s, .refl s⟩

/-- One-step unfolding of the outcomes. -/
theorem outcomes_of_step {s s' : Config V ι} {o : Option ℤ} (h : G.step s = some (o, s')) :
    G.outcomes s =
      (fun r : Outcome => ({ r with output := o.toList ++ r.output } : Outcome)) ''
        G.outcomes s' := by
  ext ⟨w, res, m⟩
  constructor
  · rintro ⟨t, ht, hh, hres, hm⟩
    cases ht with
    | refl => exact absurd hh (G.not_halted_of_step h)
    | head h₁ h₂ =>
      rw [h] at h₁
      simp only [Option.some.injEq, Prod.mk.injEq] at h₁
      obtain ⟨rfl, rfl⟩ := h₁
      exact ⟨⟨_, res, m⟩, ⟨t, h₂, hh, hres, hm⟩, rfl⟩
  · rintro ⟨⟨w', res', m'⟩, ⟨t, ht, hh, hres, hm⟩, he⟩
    simp only [Outcome.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact ⟨t, .head h ht, hh, hres, hm⟩

/-- The outcomes of a halted configuration. -/
theorem outcomes_of_halted {s : Config V ι} (h : G.Halted s) :
    G.outcomes s = {⟨[], G.resultValues s, s.mem⟩} := by
  ext ⟨w, res, m⟩
  constructor
  · rintro ⟨t, ht, hh, hres, hm⟩
    cases ht with
    | refl =>
      subst hres hm
      rfl
    | head h₁ _ => exact absurd h (G.not_halted_of_step h₁)
  · intro he
    simp only [Set.mem_singleton_iff, Outcome.mk.injEq] at he
    obtain ⟨rfl, rfl, rfl⟩ := he
    exact ⟨s, .refl s, h, rfl, rfl⟩

/-- A silent step does not change the traces. -/
theorem traces_of_silent {s s' : Config V ι} (h : G.step s = some (none, s')) :
    G.traces s = G.traces s' := by
  rw [G.traces_of_step h]
  have hid : (fun w : List ℤ => (none : Option ℤ).toList ++ w) = id := rfl
  rw [hid, Set.image_id]
  exact Set.insert_eq_of_mem ⟨s', .refl s'⟩

/-- A silent step does not change the outcomes. -/
theorem outcomes_of_silent {s s' : Config V ι} (h : G.step s = some (none, s')) :
    G.outcomes s = G.outcomes s' := by
  rw [G.outcomes_of_step h]
  have hid : (fun r : Outcome => ({ r with output := (none : Option ℤ).toList ++ r.output } :
      Outcome)) = id := by
    funext r
    rfl
  rw [hid, Set.image_id]

variable {G} {V' ι' : Type*} [DecidableEq V'] {G' : Flowgraph V' ι'}

/-! The following lemmas build `traces`/`outcomes` equalities between configurations
of two flowgraphs, possibly over different variables and nodes; for one pair of
types this is `ObsEquiv`. -/

/-- Equal observations are preserved backwards along matching steps. -/
theorem obsEquiv_of_step {s s' : Config V ι} {t t' : Config V' ι'} {o : Option ℤ}
    (hs : G.step s = some (o, s')) (ht : G'.step t = some (o, t'))
    (h : G.traces s' = G'.traces t' ∧ G.outcomes s' = G'.outcomes t') :
    G.traces s = G'.traces t ∧ G.outcomes s = G'.outcomes t := by
  refine ⟨?_, ?_⟩
  · rw [G.traces_of_step hs, G'.traces_of_step ht, h.1]
  · rw [G.outcomes_of_step hs, G'.outcomes_of_step ht, h.2]

/-- A silent step on the left. -/
theorem obsEquiv_silent_left {s s' : Config V ι} {t : Config V' ι'}
    (hs : G.step s = some (none, s'))
    (h : G.traces s' = G'.traces t ∧ G.outcomes s' = G'.outcomes t) :
    G.traces s = G'.traces t ∧ G.outcomes s = G'.outcomes t :=
  ⟨(G.traces_of_silent hs).trans h.1, (G.outcomes_of_silent hs).trans h.2⟩

/-- A silent step on the right. -/
theorem obsEquiv_silent_right {s : Config V ι} {t t' : Config V' ι'}
    (ht : G'.step t = some (none, t'))
    (h : G.traces s = G'.traces t' ∧ G.outcomes s = G'.outcomes t') :
    G.traces s = G'.traces t ∧ G.outcomes s = G'.outcomes t :=
  ⟨h.1.trans (G'.traces_of_silent ht).symm, h.2.trans (G'.outcomes_of_silent ht).symm⟩

/-- Halted configurations with the same results and memory have equal observations. -/
theorem obsEquiv_of_halted {s : Config V ι} {t : Config V' ι'} (hs : G.Halted s)
    (ht : G'.Halted t) (hres : G.resultValues s = G'.resultValues t) (hm : s.mem = t.mem) :
    G.traces s = G'.traces t ∧ G.outcomes s = G'.outcomes t := by
  refine ⟨?_, ?_⟩
  · rw [G.traces_of_halted hs, G'.traces_of_halted ht]
  · rw [G.outcomes_of_halted hs, G'.outcomes_of_halted ht, hres, hm]

/-! ## Lock-step simulation -/

section Simulation

variable {R : Config V ι → Config V' ι' → Prop}

/-- Hypotheses of a lock-step simulation: related configurations make the same
step, and halt together with the same observations. -/
structure IsLockstep (G : Flowgraph V ι) (G' : Flowgraph V' ι')
    (R : Config V ι → Config V' ι' → Prop) : Prop where
  step : ∀ {s t s' o}, R s t → G.step s = some (o, s') → ∃ t', G'.step t = some (o, t') ∧ R s' t'
  halt : ∀ {s t}, R s t → G.Halted s →
    G'.Halted t ∧ G.resultValues s = G'.resultValues t ∧ s.mem = t.mem

theorem IsLockstep.steps_fwd (hR : IsLockstep G G' R) {s s'' : Config V ι} {t : Config V' ι'}
    {w : List ℤ} (hst : G.Steps s w s'') (h : R s t) :
    ∃ t'', G'.Steps t w t'' ∧ R s'' t'' := by
  induction hst generalizing t with
  | refl => exact ⟨t, .refl t, h⟩
  | head h₁ _ ih =>
    obtain ⟨t₁, ht₁, hR₁⟩ := hR.step h h₁
    obtain ⟨t'', ht'', hR''⟩ := ih hR₁
    exact ⟨t'', .head ht₁ ht'', hR''⟩

theorem IsLockstep.steps_bwd (hR : IsLockstep G G' R) {s : Config V ι} {t t'' : Config V' ι'}
    {w : List ℤ} (hst : G'.Steps t w t'') (h : R s t) :
    ∃ s'', G.Steps s w s'' ∧ R s'' t'' := by
  induction hst generalizing s with
  | refl => exact ⟨s, .refl s, h⟩
  | head h₁ _ ih =>
    by_cases hs : G.Halted s
    · exact absurd (hR.halt h hs).1 (G'.not_halted_of_step h₁)
    obtain ⟨o', s₁, hs₁⟩ := G.exists_step_of_not_halted hs
    obtain ⟨t₁, ht₁, hR₁⟩ := hR.step h hs₁
    rw [h₁] at ht₁
    simp only [Option.some.injEq, Prod.mk.injEq] at ht₁
    obtain ⟨rfl, rfl⟩ := ht₁
    obtain ⟨s'', hs'', hR''⟩ := ih hR₁
    exact ⟨s'', .head hs₁ hs'', hR''⟩

/-- A lock-step simulation preserves traces and outcomes. -/
theorem IsLockstep.traces_outcomes (hR : IsLockstep G G' R) {s : Config V ι}
    {t : Config V' ι'} (h : R s t) :
    G.traces s = G'.traces t ∧ G.outcomes s = G'.outcomes t := by
  refine ⟨Set.ext fun w => ⟨?_, ?_⟩, Set.ext fun r => ⟨?_, ?_⟩⟩
  · rintro ⟨s'', hs''⟩
    obtain ⟨t'', ht'', -⟩ := hR.steps_fwd hs'' h
    exact ⟨t'', ht''⟩
  · rintro ⟨t'', ht''⟩
    obtain ⟨s'', hs'', -⟩ := hR.steps_bwd ht'' h
    exact ⟨s'', hs''⟩
  · rintro ⟨s'', hs'', hh, hres, hm⟩
    obtain ⟨t'', ht'', hR''⟩ := hR.steps_fwd hs'' h
    obtain ⟨hh', hres', hm'⟩ := hR.halt hR'' hh
    exact ⟨t'', ht'', hh', hres.trans hres', hm.trans hm'⟩
  · rintro ⟨t'', ht'', hh, hres, hm⟩
    obtain ⟨s'', hs'', hR''⟩ := hR.steps_bwd ht'' h
    have hs : G.Halted s'' := by
      by_contra hs
      obtain ⟨o, s₁, hs₁⟩ := G.exists_step_of_not_halted hs
      obtain ⟨t₁, ht₁, -⟩ := hR.step hR'' hs₁
      exact G'.not_halted_of_step ht₁ hh
    obtain ⟨-, hres', hm'⟩ := hR.halt hR'' hs
    exact ⟨s'', hs'', hs, hres.trans hres'.symm, hm.trans hm'.symm⟩

end Simulation

end Flowgraph

end Silmaril.Courses.Cambridge.OptimisingCompilers
