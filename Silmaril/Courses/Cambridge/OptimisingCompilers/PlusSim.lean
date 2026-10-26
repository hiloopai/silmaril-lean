module

public import Silmaril.Courses.Cambridge.OptimisingCompilers.ThreeAddress

/-! # Simulations matching a source step by one or two target steps

A generalisation of `Flowgraph.obsEquiv_of_sim` (§1 semantics, notes pp. 4–6)
for transformations that split one instruction into two, such as CSE
(notes p. 13: "replace `n′` with two instructions `n′ : t := a ⊕ b;
n″ : y := t`"). Each source step is matched either by one target step with the
same output, or by a *silent* target step followed by a step with the same
output. The source and target flowgraphs may have different node labels.

The forward direction transports runs of the source. The reverse direction uses
determinism: a target run that stops between the two steps of a matched pair
has produced the same output as the source run stopped before the source step,
because the first target step is silent.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.OptimisingCompilers.Flowgraph

variable {V ι κ : Type*} [DecidableEq V] (G : Flowgraph V ι) (G' : Flowgraph V κ)
  (R : Config V ι → Config V κ → Prop)

/-- A step-matching simulation with one or two target steps per source step
transports runs of the source. -/
theorem steps_of_plusSim
    (hfwd : ∀ {s t s' o}, R s t → G.step s = some (o, s') →
      (∃ t', G'.step t = some (o, t') ∧ R s' t') ∨
        ∃ u t', G'.step t = some (none, u) ∧ G'.step u = some (o, t') ∧ R s' t')
    {s s' : Config V ι} {t : Config V κ} {w : List ℤ} (h : G.Steps s w s') (hst : R s t) :
    ∃ t', G'.Steps t w t' ∧ R s' t' := by
  induction h generalizing t with
  | refl => exact ⟨t, .refl t, hst⟩
  | head hs _ ih =>
    rcases hfwd hst hs with ⟨t₁, ht, hR⟩ | ⟨u, t₁, hu, ht, hR⟩
    · obtain ⟨t', ht', hR'⟩ := ih hR
      exact ⟨t', .head ht ht', hR'⟩
    · obtain ⟨t', ht', hR'⟩ := ih hR
      exact ⟨t', by simpa using Steps.head hu (Steps.head ht ht'), hR'⟩

/-- The reverse direction: a run of the target is matched by a run of the
source ending either in a related configuration or one step before it, with the
target configuration between the two steps of a matched pair. -/
theorem steps_of_plusSim_rev
    (hfwd : ∀ {s t s' o}, R s t → G.step s = some (o, s') →
      (∃ t', G'.step t = some (o, t') ∧ R s' t') ∨
        ∃ u t', G'.step t = some (none, u) ∧ G'.step u = some (o, t') ∧ R s' t')
    (hnone : ∀ {s t}, R s t → G.step s = none → G'.step t = none)
    {t t' : Config V κ} {w : List ℤ} (h : G'.Steps t w t') {s : Config V ι}
    (hst : R s t ∨ ∃ o s₁ t₁, G.step s = some (o, s₁) ∧ G'.step t = some (o, t₁) ∧ R s₁ t₁) :
    ∃ s', G.Steps s w s' ∧
      (R s' t' ∨ ∃ o s₁ t₁, G.step s' = some (o, s₁) ∧ G'.step t' = some (o, t₁) ∧ R s₁ t₁) := by
  induction h generalizing s with
  | refl => exact ⟨s, .refl s, hst⟩
  | head ht _ ih =>
    rcases hst with hst | ⟨o', s₁, t₁, hs, ht₁, hR⟩
    · cases hs : G.step s with
      | none => rw [hnone hst hs] at ht; cases ht
      | some p =>
        obtain ⟨o', s₁⟩ := p
        rcases hfwd hst hs with ⟨t₁, ht₁, hR⟩ | ⟨u, t₁, hu, ht₁, hR⟩
        · rw [ht] at ht₁
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj ht₁)
          obtain ⟨s', hs', hR'⟩ := ih (Or.inl hR)
          exact ⟨s', .head hs hs', hR'⟩
        · rw [ht] at hu
          obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hu)
          obtain ⟨s', hs', hR'⟩ := ih (Or.inr ⟨o', s₁, t₁, hs, ht₁, hR⟩)
          exact ⟨s', by simpa using hs', hR'⟩
    · rw [ht] at ht₁
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj ht₁)
      obtain ⟨s', hs', hR'⟩ := ih (Or.inl hR)
      exact ⟨s', .head hs hs', hR'⟩

/-- A one-or-two-step simulation that preserves halting and the halting
observations (result values and memory) preserves traces and outcomes. -/
theorem traces_outcomes_eq_of_plusSim
    (hfwd : ∀ {s t s' o}, R s t → G.step s = some (o, s') →
      (∃ t', G'.step t = some (o, t') ∧ R s' t') ∨
        ∃ u t', G'.step t = some (none, u) ∧ G'.step u = some (o, t') ∧ R s' t')
    (hnone : ∀ {s t}, R s t → G.step s = none → G'.step t = none)
    (hres : ∀ {s t}, R s t → G.Halted s →
      G.resultValues s = G'.resultValues t ∧ s.mem = t.mem)
    {s : Config V ι} {t : Config V κ} (hst : R s t) :
    G.traces s = G'.traces t ∧ G.outcomes s = G'.outcomes t := by
  refine ⟨Set.ext fun w => ⟨?_, ?_⟩, Set.ext fun o => ⟨?_, ?_⟩⟩
  · rintro ⟨s', hs'⟩
    obtain ⟨t', ht', -⟩ := G.steps_of_plusSim G' R hfwd hs' hst
    exact ⟨t', ht'⟩
  · rintro ⟨t', ht'⟩
    obtain ⟨s', hs', -⟩ := G.steps_of_plusSim_rev G' R hfwd hnone ht' (Or.inl hst)
    exact ⟨s', hs'⟩
  · rintro ⟨s', hs', hh, hr, hm⟩
    obtain ⟨t', ht', hR⟩ := G.steps_of_plusSim G' R hfwd hs' hst
    have hht : G'.Halted t' :=
      (G'.step_eq_none_iff t').1 (hnone hR ((G.step_eq_none_iff s').2 hh))
    obtain ⟨e1, e2⟩ := hres hR hh
    exact ⟨t', ht', hht, hr.trans e1, hm.trans e2⟩
  · rintro ⟨t', ht', hh, hr, hm⟩
    obtain ⟨s', hs', hR | ⟨o', s₁, t₁, -, ht₁, -⟩⟩ :=
      G.steps_of_plusSim_rev G' R hfwd hnone ht' (Or.inl hst)
    · have hhs : G.Halted s' := by
        rw [← G.step_eq_none_iff]
        cases hs : G.step s' with
        | none => rfl
        | some p =>
          obtain ⟨o', s''⟩ := p
          rcases hfwd hR hs with ⟨t'', h, -⟩ | ⟨u, t'', h, -⟩ <;>
            rw [(G'.step_eq_none_iff t').2 hh] at h <;> cases h
      obtain ⟨e1, e2⟩ := hres hR hhs
      exact ⟨s', hs', hhs, hr.trans e1.symm, hm.trans e2.symm⟩
    · rw [(G'.step_eq_none_iff t').2 hh] at ht₁
      cases ht₁

/-- `obsEquiv_of_sim` is the special case where every source step is matched by
a single target step. -/
theorem obsEquiv_of_sim' (G' : Flowgraph V ι) (R : Config V ι → Config V ι → Prop)
    (hfwd : ∀ {s t s' : Config V ι} {o : Option ℤ}, R s t → G.step s = some (o, s') →
      ∃ t', G'.step t = some (o, t') ∧ R s' t')
    (hnone : ∀ {s t : Config V ι}, R s t → G.step s = none → G'.step t = none)
    (hres : ∀ {s t : Config V ι}, R s t → G.Halted s →
      G.resultValues s = G'.resultValues t ∧ s.mem = t.mem)
    {s t : Config V ι} (hst : R s t) : G.ObsEquiv G' s t :=
  G.traces_outcomes_eq_of_plusSim G' R (fun h hs => Or.inl (hfwd h hs)) hnone hres hst

/-- Computing a step from the instruction at the current node. -/
theorem step_eq_of_exec {c : Config V ι} {i : Instr V ι} (hc : G.code c.pc = i)
    {n : ι} {env : Env V} {mem : Mem} {o : Option ℤ}
    (hi : i.exec c.env c.mem = some (n, env, mem, o)) : G.step c = some (o, ⟨n, env, mem⟩) := by
  simp [step, hc, hi]

end Silmaril.Courses.Cambridge.OptimisingCompilers.Flowgraph
