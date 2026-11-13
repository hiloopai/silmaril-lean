module

public import Silmaril.Games.Reduct.Thms
public import Silmaril.Games.Div.Thms
public import Silmaril.Proofs.Games.DInstitution.Mid

/-!
# The reduct of divergence-observing strategies: functoriality

Proofs of `DStrategy.reduct_id` and `DStrategy.reduct_comp` (`Silmaril.Games.DInstitution.Defs`).
The reduct is restated here as `reductD` (the same data) so that the proofs do not depend on the
header.
-/

public section

namespace Silmaril.Proofs.Games.DInstitution

open CategoryTheory Silmaril.Games

universe u

variable {G G' G'' : Game.{u}}

/-- An infinite play contained in another is equal to it. -/
theorem isInf_eq_of_subset {α : Type u} {I J : Set (List α)} (hI : IsInfPlay I)
    (hJ : IsInfPlay J) (h : I ⊆ J) : I = J := by
  refine Set.Subset.antisymm h fun t ht => ?_
  obtain ⟨p, hp, hl⟩ := hI.unbounded t.length
  have htp : t <+: p := hJ.prefix_of_length_le ht (h hp) hl
  exact hI.of_prefix hp htp

/-- The divergences of the reduct. -/
abbrev rdiv (f : G ⟶ G') (δ : DStrategy G'.E G'.F) : Set (List (Move G.E G.F)) :=
  {p | Legal p ∧ ∃ s ∈ δ.div, List.Forall₂ (Game.Rel f) s p}

/-- The infinite plays of the reduct. -/
abbrev rinf (f : G ⟶ G') (S : Strategy G'.E G'.F) (inf : Set (Set (List (Move G'.E G'.F)))) :
    Set (Set (List (Move G.E G.F))) :=
  {I | IsInfPlay I ∧ I ⊆ (Game.reduct f S).plays ∧
    ∃ J ∈ inf, ∀ p ∈ I, ∃ s ∈ J, List.Forall₂ (Game.Rel f) s p}

theorem rdiv_id (δ : DStrategy G.E G.F) : rdiv (𝟙 G) δ = δ.div := by
  ext p
  simp only [Set.mem_ofPred_eq, Game.forall₂_rel_id_iff]
  constructor
  · rintro ⟨-, s, hs, rfl⟩
    exact hs
  · intro h
    exact ⟨δ.toStrategy.legal (δ.div_mem h), p, h, rfl⟩

theorem rinf_id (δ : DStrategy G.E G.F) : rinf (𝟙 G) δ.toStrategy δ.inf = δ.inf := by
  ext I
  simp only [Set.mem_ofPred_eq, Game.forall₂_rel_id_iff, Game.reduct_id, exists_eq_right]
  constructor
  · rintro ⟨hI, -, J, hJ, hIJ⟩
    rwa [isInf_eq_of_subset hI (δ.inf_isInf hJ) hIJ]
  · intro h
    exact ⟨δ.inf_isInf h, δ.inf_sub h, I, h, fun _ hp => hp⟩

theorem rdiv_comp (f : G ⟶ G') (g : G' ⟶ G'') (δ : DStrategy G''.E G''.F) :
    rdiv (f ≫ g) δ = {p | Legal p ∧ ∃ t ∈ rdiv g δ, List.Forall₂ (Game.Rel f) t p} := by
  ext p
  constructor
  · rintro ⟨hp, s, hs, hr⟩
    obtain ⟨t, h₁, h₂⟩ := Game.rel_decomp f g hr
    have ht : Legal t := Game.legal_mid f g h₁ h₂ (δ.toStrategy.legal (δ.div_mem hs)) hp
    exact ⟨hp, t, ⟨ht, s, hs, h₁⟩, h₂⟩
  · rintro ⟨hp, t, ⟨-, s, hs, h₁⟩, h₂⟩
    exact ⟨hp, s, hs, Game.rel_comp f g h₁ h₂⟩

/-- The infinite-play half of `reduct_comp`, from the composite to the iterate. -/
theorem rinf_comp_sub (f : G ⟶ G') (g : G' ⟶ G'') (δ : DStrategy G''.E G''.F)
    {I : Set (List (Move G.E G.F))} (hI : I ∈ rinf (f ≫ g) δ.toStrategy δ.inf) :
    I ∈ rinf f (Game.reduct g δ.toStrategy) (rinf g δ.toStrategy δ.inf) := by
  obtain ⟨hInf, hsub, J, hJ, hIJ⟩ := hI
  have hsub' : I ⊆ (Game.reduct f (Game.reduct g δ.toStrategy)).plays := by
    rw [← Game.reduct_comp]
    exact hsub
  obtain ⟨c, hmono, hunb, hmid, hcov⟩ :=
    inf_mid (fun _ _ h => Game.rel_decomp_move f g h) hInf (δ.inf_isInf hJ) hIJ
  have hcn : ∀ n, c n ∈ Game.reduct g δ.toStrategy := by
    intro n
    obtain ⟨s, hs, p, hp, h₁, h₂⟩ := hmid n
    have hsl : Legal s := δ.toStrategy.legal (δ.inf_sub hJ hs)
    have hpl : Legal p := (Game.reduct (f ≫ g) δ.toStrategy).legal (hsub hp)
    exact (Game.mem_reduct_iff_rel g _ _).2
      ⟨Game.legal_mid f g h₁ h₂ hsl hpl, s, δ.inf_sub hJ hs, h₁⟩
  refine ⟨hInf, hsub', c.lim, ⟨Chain.isInfPlay_lim hmono hunb, ?_, J, hJ, ?_⟩, ?_⟩
  · rintro t ⟨n, htn⟩
    exact (Game.reduct g δ.toStrategy).of_prefix (hcn n) htn
  · rintro t ⟨n, htn⟩
    obtain ⟨s, hs, -, -, h₁, -⟩ := hmid n
    have ht : t = (c n).take t.length := List.prefix_iff_eq_take.1 htn
    refine ⟨s.take t.length, (δ.inf_isInf hJ).of_prefix hs (List.take_prefix _ _), ?_⟩
    have h := List.forall₂_take t.length h₁
    rwa [← ht] at h
  · intro p hp
    obtain ⟨n, hn⟩ := hcov p hp
    exact ⟨c n, Chain.mem_lim_self c n, hn⟩

/-- The infinite-play half of `reduct_comp`, from the iterate to the composite. -/
theorem rinf_comp_sup (f : G ⟶ G') (g : G' ⟶ G'') (δ : DStrategy G''.E G''.F)
    {I : Set (List (Move G.E G.F))}
    (hI : I ∈ rinf f (Game.reduct g δ.toStrategy) (rinf g δ.toStrategy δ.inf)) :
    I ∈ rinf (f ≫ g) δ.toStrategy δ.inf := by
  obtain ⟨hInf, hsub, J', ⟨-, -, J, hJ, hJ'⟩, hIJ'⟩ := hI
  refine ⟨hInf, ?_, J, hJ, fun p hp => ?_⟩
  · rw [Game.reduct_comp]
    exact hsub
  · obtain ⟨t, ht, h₂⟩ := hIJ' p hp
    obtain ⟨s, hs, h₁⟩ := hJ' t ht
    exact ⟨s, hs, Game.rel_comp f g h₁ h₂⟩

/-- The reduct of a divergence-observing strategy, as in `DStrategy.reduct`. -/
@[expose] def reductD (f : G ⟶ G') (δ : DStrategy G'.E G'.F) : DStrategy G.E G.F where
  toStrategy := Game.reduct f δ.toStrategy
  div := rdiv f δ
  inf := rinf f δ.toStrategy δ.inf
  div_mem := fun ⟨hp, s, hs, hr⟩ =>
    (Game.mem_reduct_iff_rel f _ _).2 ⟨hp, s, δ.div_mem hs, hr⟩
  div_run := fun ⟨hp, _, hs, hr⟩ =>
    let ⟨_, hq⟩ := δ.div_run hs
    Game.run_of_rel f hr hq hp
  inf_isInf h := h.1
  inf_sub h := h.2.1

theorem reduct_id (δ : DStrategy G.E G.F) : reductD (𝟙 G) δ = δ :=
  DStrategy.ext (Game.reduct_id G δ.toStrategy) (rdiv_id δ) (rinf_id δ)

theorem reduct_comp (f : G ⟶ G') (g : G' ⟶ G'') (δ : DStrategy G''.E G''.F) :
    reductD (f ≫ g) δ = reductD f (reductD g δ) :=
  DStrategy.ext (Game.reduct_comp f g δ.toStrategy) (rdiv_comp f g δ)
    (Set.ext fun _ => ⟨rinf_comp_sub f g δ, rinf_comp_sup f g δ⟩)

end Silmaril.Proofs.Games.DInstitution
