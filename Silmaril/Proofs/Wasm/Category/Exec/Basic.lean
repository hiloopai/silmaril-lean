module

public import Silmaril.Wasm.Category.Exec.Defs

@[expose] public section

/-!
# Execution semantics, cofunctors and simulations: proofs
-/

namespace Silmaril.Wasm.Category

open CategoryTheory Relation Silmaril.Compile.Category

universe u

variable {L L' : Language.{u}}

namespace Exec

/-- A run from a final configuration of a deterministic execution stays there. -/
theorem Deterministic.eq_of_final {E : Exec L} (h : E.Deterministic) {t t' : E.Conf}
    {o : L.Obs} (hf : E.final t o) (r : ReflTransGen E.step t t') : t = t' := by
  rcases Relation.ReflTransGen.cases_head_iff.1 r with hr | ⟨u, hu, -⟩
  · exact hr
  · exact absurd hu (h.final_stuck _ _ _ hf)

/-- A deterministic program has at most one behaviour. -/
theorem Deterministic.beh_subsingleton {E : Exec L} (h : E.Deterministic) (p : L.Prog) :
    (L.beh p).Subsingleton := by
  have hU : Relator.RightUnique E.step := fun _ _ _ h₁ h₂ => h.step _ _ _ h₁ h₂
  intro o ho o' ho'
  have ho₁ : ∃ s ∈ E.init p, ∃ t, ReflTransGen E.step s t ∧ E.final t o := by
    rw [E.adequate] at ho
    exact ho
  have ho₂ : ∃ s ∈ E.init p, ∃ t, ReflTransGen E.step s t ∧ E.final t o' := by
    rw [E.adequate] at ho'
    exact ho'
  obtain ⟨s, hs, t, r, hf⟩ := ho₁
  obtain ⟨s', hs', t', r', hf'⟩ := ho₂
  have hss : s = s' := h.init p hs hs'
  have r'' : ReflTransGen E.step s t' := hss ▸ r'
  have htt : t = t' := by
    rcases r.total_of_right_unique hU r'' with r₃ | r₃
    · exact h.eq_of_final hf r₃
    · exact (h.eq_of_final hf' r₃).symm
  have hf'' : E.final t o' := htt ▸ hf'
  exact h.final _ _ _ hf hf''

end Exec

namespace RelCofunctor

variable {E : Exec L} {E' : Exec L'}

/-- Validity from behaviour inclusion, directly from the definition of `Valid`. -/
theorem valid_of_beh {c : L ⟶ L'} {p : L.Prog} {p' : L'.Prog}
    (hΦ : c.Φ (L.iface p) = L'.iface p')
    (h : ∀ o' ∈ L'.beh p', ∃ o ∈ L.beh p, c.R o o') : Valid c p p' :=
  ⟨hΦ, fun φ hφ => (L'.sat_iff _ _).2 fun o' ho' => by
    obtain ⟨o, ho, hR⟩ := h o' ho'
    exact ⟨o, (L.sat_iff p φ).1 hφ ho, hR⟩⟩

/-- A cofunctor makes `p'` a valid compilation of `p` at `c` when initial configurations are
matched and matched final observations are realisations of source observations. -/
theorem valid {c : L ⟶ L'} (κ : RelCofunctor E E') {p : L.Prog} {p' : L'.Prog}
    (hΦ : c.Φ (L.iface p) = L'.iface p')
    (hinit : ∀ s' ∈ E'.init p', ∃ s ∈ E.init p, κ.M s s')
    (hfinal : ∀ {s s' o'}, κ.M s s' → E'.final s' o' →
      ∃ o, c.R o o' ∧ ∃ t, ReflTransGen E.step s t ∧ E.final t o) :
    Valid c p p' := by
  refine valid_of_beh hΦ fun o' ho' => ?_
  have hrun : ∃ s' ∈ E'.init p', ∃ t', ReflTransGen E'.step s' t' ∧ E'.final t' o' := by
    rw [E'.adequate] at ho'
    exact ho'
  obtain ⟨s', hs', t', r', hf'⟩ := hrun
  obtain ⟨s, hs, hM⟩ := hinit s' hs'
  obtain ⟨t, r, hMt⟩ := κ.lift hM r'
  obtain ⟨o, hR, u, ru, hfu⟩ := hfinal hMt hf'
  have ho : o ∈ L.beh p := by
    rw [E.adequate]
    exact ⟨s, hs, u, r.trans ru, hfu⟩
  exact ⟨o, ho, hR⟩

/-- Coherence with the read-back model translation: final target observations read back to
final source observations. -/
theorem valid_of_readBack {c : L ⟶ L'} (hc : Convention.ReadBack c) (κ : RelCofunctor E E')
    {p : L.Prog} {p' : L'.Prog} (hΦ : c.Φ (L.iface p) = L'.iface p')
    (hinit : ∀ s' ∈ E'.init p', ∃ s ∈ E.init p, κ.M s s')
    (hfinal : ∀ {s s' o'}, κ.M s s' → E'.final s' o' →
      ∃ t, ReflTransGen E.step s t ∧ E.final t (hc.g o')) :
    Valid c p p' :=
  κ.valid hΦ hinit fun hM hf' => by
    obtain ⟨t, r, hf⟩ := hfinal hM hf'
    exact ⟨_, (hc.spec _ _).2 rfl, t, r, hf⟩

end RelCofunctor

/-- A backward simulation proves validity. -/
theorem BackwardSim.valid {c : L ⟶ L'} {E : Exec L} {E' : Exec L'} {p : L.Prog}
    {p' : L'.Prog} (σ : BackwardSim c E E' p p') (hΦ : c.Φ (L.iface p) = L'.iface p') :
    Valid c p p' :=
  σ.toRelCofunctor.valid hΦ σ.init σ.final

namespace ForwardSim

variable {c : L ⟶ L'} {E : Exec L} {E' : Exec L'} {p : L.Prog} {p' : L'.Prog}

/-- A source run from a matched pair is matched by a target run. -/
theorem run (σ : ForwardSim c E E' p p') {s t : E.Conf} {s' : E'.Conf} (hM : σ.M s s')
    (r : ReflTransGen E.step s t) : ∃ t', ReflTransGen E'.step s' t' ∧ σ.M t t' := by
  induction r with
  | refl => exact ⟨s', ReflTransGen.refl, hM⟩
  | tail _ hstep ih =>
    obtain ⟨u', ru', hu⟩ := ih
    obtain ⟨v', rv', hv⟩ := σ.step hu hstep
    exact ⟨v', ru'.trans rv', hv⟩

/-- Forward simulations preserve source behaviours: every source behaviour has a realisation
among the target behaviours. -/
theorem preserves (σ : ForwardSim c E E' p p') {o : L.Obs} (ho : o ∈ L.beh p) :
    ∃ o' ∈ L'.beh p', c.R o o' := by
  have hrun : ∃ s ∈ E.init p, ∃ t, ReflTransGen E.step s t ∧ E.final t o := by
    rw [E.adequate] at ho
    exact ho
  obtain ⟨s, hs, t, r, hf⟩ := hrun
  obtain ⟨s', hs', hM⟩ := σ.init s hs
  obtain ⟨t', rt', hMt⟩ := σ.run hM r
  obtain ⟨o', hR, u', ru', hfu⟩ := σ.final hMt hf
  have ho' : o' ∈ L'.beh p' := by
    rw [E'.adequate]
    exact ⟨s', hs', u', rt'.trans ru', hfu⟩
  exact ⟨o', ho', hR⟩

/-- **The forward-to-backward flip.** A forward simulation into a deterministic target, from a
source with some behaviour, proves validity. -/
theorem valid (σ : ForwardSim c E E' p p') (hdet : E'.Deterministic) (hne : (L.beh p).Nonempty)
    (hΦ : c.Φ (L.iface p) = L'.iface p') : Valid c p p' := by
  obtain ⟨o, ho⟩ := hne
  obtain ⟨o₂, ho₂, hR⟩ := σ.preserves ho
  refine RelCofunctor.valid_of_beh hΦ fun o' ho' => ?_
  exact ⟨o, ho, hdet.beh_subsingleton p' ho₂ ho' ▸ hR⟩

end ForwardSim

end Silmaril.Wasm.Category
