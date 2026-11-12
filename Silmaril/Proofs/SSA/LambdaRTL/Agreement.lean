module

public import Silmaril.SSA.LambdaRTL.Defs

/-!
# λRTL vs lexical λSSA: frame, congruence and agreement (proofs)

Restated in `Silmaril.SSA.LambdaRTL.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL

open Silmaril.SSA.LambdaRTL

universe v w

variable {V L : Type w} {F F' : Type v} {M : Type w → Type w} {α : Type w}

section Upd

variable [DecidableEq V]

theorem upd_self (σ : V → α) (x : V) (a : α) : upd σ x a x = a := by
  simp [upd]

theorem upd_of_ne (σ : V → α) {x y : V} (a : α) (h : y ≠ x) : upd σ x a y = σ y := by
  simp [upd, h]

end Upd

/-! ## Congruence: evaluation depends only on free variables -/

theorem Val.eval_congr [DecidableEq V] (m : Model F M α) {σ₁ σ₂ : V → α} :
    ∀ (a : Val V), (∀ y ∈ a.fv, σ₁ y = σ₂ y) → a.eval m σ₁ = a.eval m σ₂
  | .var x, h => h x (by simp [Val.fv])
  | .unit, _ => rfl
  | .pair a b, h => by
      simp only [Val.eval]
      rw [Val.eval_congr m a (fun y hy => h y (by simp [Val.fv, hy])),
        Val.eval_congr m b (fun y hy => h y (by simp [Val.fv, hy]))]

theorem Op.eval_congr [Monad M] [DecidableEq V] (m : Model F M α) {σ₁ σ₂ : V → α}
    (o : Op V F) (h : ∀ y ∈ o.fv, σ₁ y = σ₂ y) : o.eval m σ₁ = o.eval m σ₂ := by
  cases o <;> simp only [Op.eval, Op.fv] at h ⊢ <;> rw [Val.eval_congr m _ h]

/-- Agreement of two environments on `S` after updating both at the same point. -/
theorem upd_agree [DecidableEq V] {σ₁ σ₂ : V → α} {S : Finset V} (x : V) (a : α)
    (h : ∀ y ∈ S.erase x, σ₁ y = σ₂ y) : ∀ y ∈ S, upd σ₁ x a y = upd σ₂ x a y := by
  intro y hy
  by_cases hyx : y = x
  · subst hyx; simp [upd]
  · rw [upd_of_ne _ _ hyx, upd_of_ne _ _ hyx]
    exact h y (Finset.mem_erase.2 ⟨hyx, hy⟩)

variable [Monad M] [DecidableEq V] [DecidableEq L]

/-- The lexical semantics only reads free variables. -/
theorem Region.evalSSA_congr (m : Model F M α) :
    ∀ (r : Region V L F) {ρ₁ ρ₂ : V → α}, (∀ y ∈ r.fv, ρ₁ y = ρ₂ y) →
      r.evalSSA m ρ₁ = r.evalSSA m ρ₂
  | .br ℓ a, ρ₁, ρ₂, h => by
      simp only [Region.evalSSA]
      rw [Val.eval_congr m a h]
  | .let1 x o r, ρ₁, ρ₂, h => by
      simp only [Region.evalSSA]
      rw [Op.eval_congr m o (fun y hy => h y (by simp [Region.fv, hy]))]
      congr 1; funext a
      exact Region.evalSSA_congr m r (upd_agree x a (fun y hy => h y (by simp [Region.fv, hy])))
  | .let2 x y o r, ρ₁, ρ₂, h => by
      simp only [Region.evalSSA]
      rw [Op.eval_congr m o (fun z hz => h z (by simp [Region.fv, hz]))]
      congr 1; funext p
      apply Region.evalSSA_congr m r
      apply upd_agree y p.2
      intro z hz
      apply upd_agree x p.1 _ z hz
      intro w hw
      exact h w (by simp [Region.fv, hw])
  | .case o x r y s, ρ₁, ρ₂, h => by
      simp only [Region.evalSSA]
      rw [Op.eval_congr m o (fun z hz => h z (by simp [Region.fv, hz]))]
      congr 1; funext c
      cases c with
      | inl a =>
          exact Region.evalSSA_congr m r
            (upd_agree x a (fun z hz => h z (by simp [Region.fv, hz])))
      | inr b =>
          exact Region.evalSSA_congr m s
            (upd_agree y b (fun z hz => h z (by simp [Region.fv, hz])))
  | .join r ℓ x t, ρ₁, ρ₂, h => by
      simp only [Region.evalSSA]
      rw [Region.evalSSA_congr m r (fun z hz => h z (by simp [Region.fv, hz]))]
      congr 1; funext e
      split
      · exact Region.evalSSA_congr m t
          (upd_agree x e.2 (fun z hz => h z (by simp [Region.fv, hz])))
      · rfl

/-! ## Frame: λRTL only writes registers it assigns -/

variable [LawfulMonad M]

/-- **Frame lemma**, stated without a support/possibility modality: two continuations that agree
on every outcome whose store agrees with the initial store outside `r.bound` give equal
results. -/
theorem Region.evalRTL_frame (m : Model F M α) {β : Type w} :
    ∀ (r : Region V L F) (σ : V → α) (f g : L × α × (V → α) → M β),
      (∀ l a σ', (∀ y, y ∉ r.bound → σ' y = σ y) → f (l, a, σ') = g (l, a, σ')) →
      (r.evalRTL m σ >>= f) = (r.evalRTL m σ >>= g)
  | .br ℓ a, σ, f, g, h => by
      simp only [Region.evalRTL, pure_bind]
      exact h _ _ _ (fun _ _ => rfl)
  | .let1 x o r, σ, f, g, h => by
      simp only [Region.evalRTL, bind_assoc]
      congr 1; funext a
      apply Region.evalRTL_frame m r
      intro l b σ' hσ'
      apply h
      intro y hy
      have hyx : y ≠ x := fun e => hy (by simp [Region.bound, e])
      have hyr : y ∉ r.bound := fun e => hy (by simp [Region.bound, e])
      rw [hσ' y hyr, upd_of_ne _ _ hyx]
  | .let2 x y o r, σ, f, g, h => by
      simp only [Region.evalRTL, bind_assoc]
      congr 1; funext a; congr 1; funext p
      apply Region.evalRTL_frame m r
      intro l b σ' hσ'
      apply h
      intro z hz
      have hzx : z ≠ x := fun e => hz (by simp [Region.bound, e])
      have hzy : z ≠ y := fun e => hz (by simp [Region.bound, e])
      have hzr : z ∉ r.bound := fun e => hz (by simp [Region.bound, e])
      rw [hσ' z hzr, upd_of_ne _ _ hzy, upd_of_ne _ _ hzx]
  | .case o x r y s, σ, f, g, h => by
      simp only [Region.evalRTL, bind_assoc]
      congr 1; funext a; congr 1; funext c
      cases c with
      | inl b =>
          apply Region.evalRTL_frame m r
          intro l b' σ' hσ'
          apply h
          intro z hz
          have hzx : z ≠ x := fun e => hz (by simp [Region.bound, e])
          have hzr : z ∉ r.bound := fun e => hz (by simp [Region.bound, e])
          rw [hσ' z hzr, upd_of_ne _ _ hzx]
      | inr b =>
          apply Region.evalRTL_frame m s
          intro l b' σ' hσ'
          apply h
          intro z hz
          have hzy : z ≠ y := fun e => hz (by simp [Region.bound, e])
          have hzs : z ∉ s.bound := fun e => hz (by simp [Region.bound, e])
          rw [hσ' z hzs, upd_of_ne _ _ hzy]
  | .join r ℓ x t, σ, f, g, h => by
      simp only [Region.evalRTL, bind_assoc]
      apply Region.evalRTL_frame m r
      intro l a σ' hσ'
      dsimp only
      split
      · apply Region.evalRTL_frame m t
        intro l' b σ'' hσ''
        apply h
        intro z hz
        have hzr : z ∉ r.bound := fun e => hz (by simp [Region.bound, e])
        have hzx : z ≠ x := fun e => hz (by simp [Region.bound, e])
        have hzt : z ∉ t.bound := fun e => hz (by simp [Region.bound, e])
        rw [hσ'' z hzt, upd_of_ne _ _ hzx, hσ' z hzr]
      · simp only [pure_bind]
        apply h
        intro z hz
        exact hσ' z (fun e => hz (by simp [Region.bound, e]))

/-! ## Agreement of the two readings under no-clobbering -/

/-- Under `NoClobber`, the observable λRTL semantics is the lexical λSSA semantics. -/
theorem Region.evalObs_eq_evalSSA (m : Model F M α) :
    ∀ (r : Region V L F), r.NoClobber → ∀ σ : V → α, r.evalObs m σ = r.evalSSA m σ
  | .br ℓ a, _, σ => by
      simp [Region.evalObs, Region.evalRTL, Region.evalSSA, obs]
  | .let1 x o r, hr, σ => by
      simp only [Region.evalObs, Region.evalRTL, Region.evalSSA, map_bind]
      congr 1; funext a
      exact Region.evalObs_eq_evalSSA m r hr _
  | .let2 x y o r, hr, σ => by
      simp only [Region.evalObs, Region.evalRTL, Region.evalSSA, map_bind]
      congr 1; funext p
      exact Region.evalObs_eq_evalSSA m r hr _
  | .case o x r y s, hr, σ => by
      simp only [Region.evalObs, Region.evalRTL, Region.evalSSA, map_bind]
      congr 1; funext c
      cases c with
      | inl b => exact Region.evalObs_eq_evalSSA m r hr.1 _
      | inr b => exact Region.evalObs_eq_evalSSA m s hr.2 _
  | .join r ℓ x t, hr, σ => by
      obtain ⟨hr, ht, hdisj⟩ := hr
      have ihr := Region.evalObs_eq_evalSSA m r hr σ
      simp only [Region.evalObs] at ihr
      simp only [Region.evalObs, Region.evalRTL, Region.evalSSA, map_bind]
      rw [← ihr, bind_map_left]
      apply Region.evalRTL_frame m r
      intro l a σ' hσ'
      by_cases hl : l = ℓ
      · subst hl
        simp only [obs, ↓reduceIte]
        exact (Region.evalObs_eq_evalSSA m t ht _).trans
          (Region.evalSSA_congr m t
            (upd_agree x a fun z hz => hσ' z (Finset.disjoint_left.1 hdisj hz)))
      · simp [obs, hl]

/-! ## Dominance-scoped SSA implies no clobbering -/

omit [Monad M] [DecidableEq L] [LawfulMonad M] in
theorem Region.fv_subset_of_isSSA :
    ∀ (r : Region V L F) (Γ : Finset V), r.IsSSA Γ → r.fv ⊆ Γ
  | .br _ a, Γ, h => h
  | .let1 x o r, Γ, ⟨ho, _, hr⟩ => fun z hz => by
      simp only [Region.fv, Finset.mem_union, Finset.mem_erase] at hz
      rcases hz with hz | ⟨hzx, hz⟩
      · exact ho hz
      · have := Region.fv_subset_of_isSSA r _ hr hz
        simpa [hzx] using this
  | .let2 x y o r, Γ, ⟨ho, _, _, _, hr⟩ => fun z hz => by
      simp only [Region.fv, Finset.mem_union, Finset.mem_erase] at hz
      rcases hz with hz | ⟨hzx, hzy, hz⟩
      · exact ho hz
      · have := Region.fv_subset_of_isSSA r _ hr hz
        simpa [hzx, hzy] using this
  | .case o x r y s, Γ, ⟨ho, _, _, hr, hs⟩ => fun z hz => by
      simp only [Region.fv, Finset.mem_union, Finset.mem_erase] at hz
      rcases hz with (hz | ⟨hzx, hz⟩) | ⟨hzy, hz⟩
      · exact ho hz
      · have := Region.fv_subset_of_isSSA r _ hr hz
        simpa [hzx] using this
      · have := Region.fv_subset_of_isSSA s _ hs hz
        simpa [hzy] using this
  | .join r _ x t, Γ, ⟨hr, _, ht⟩ => fun z hz => by
      simp only [Region.fv, Finset.mem_union, Finset.mem_erase] at hz
      rcases hz with hz | ⟨hzx, hz⟩
      · exact Region.fv_subset_of_isSSA r _ hr hz
      · have := Region.fv_subset_of_isSSA t _ ht hz
        simpa [hzx] using this

omit [Monad M] [DecidableEq L] [LawfulMonad M] in
theorem Region.bound_disjoint_of_isSSA :
    ∀ (r : Region V L F) (Γ : Finset V), r.IsSSA Γ → Disjoint r.bound Γ
  | .br _ _, _, _ => by simp [Region.bound]
  | .let1 x o r, Γ, ⟨_, hx, hr⟩ => by
      have := Region.bound_disjoint_of_isSSA r _ hr
      simp only [Region.bound, Finset.disjoint_insert_left]
      exact ⟨hx, Finset.disjoint_of_subset_right (Finset.subset_insert _ _) this⟩
  | .let2 x y o r, Γ, ⟨_, hx, hy, _, hr⟩ => by
      have := Region.bound_disjoint_of_isSSA r _ hr
      simp only [Region.bound, Finset.disjoint_insert_left]
      refine ⟨hx, hy, Finset.disjoint_of_subset_right ?_ this⟩
      intro z hz; simp [hz]
  | .case o x r y s, Γ, ⟨_, hx, hy, hr, hs⟩ => by
      have h1 := Region.bound_disjoint_of_isSSA r _ hr
      have h2 := Region.bound_disjoint_of_isSSA s _ hs
      simp only [Region.bound, Finset.disjoint_insert_left, Finset.disjoint_union_left]
      exact ⟨hx, hy, Finset.disjoint_of_subset_right (Finset.subset_insert _ _) h1,
        Finset.disjoint_of_subset_right (Finset.subset_insert _ _) h2⟩
  | .join r _ x t, Γ, ⟨hr, hx, ht⟩ => by
      have h1 := Region.bound_disjoint_of_isSSA r _ hr
      have h2 := Region.bound_disjoint_of_isSSA t _ ht
      simp only [Region.bound, Finset.disjoint_insert_left, Finset.disjoint_union_left]
      exact ⟨h1, hx, Finset.disjoint_of_subset_right (Finset.subset_insert _ _) h2⟩

omit [Monad M] [DecidableEq L] [LawfulMonad M] in
theorem Region.noClobber_of_isSSA :
    ∀ (r : Region V L F) (Γ : Finset V), r.IsSSA Γ → r.NoClobber
  | .br _ _, _, _ => trivial
  | .let1 _ _ r, _, ⟨_, _, hr⟩ => Region.noClobber_of_isSSA r _ hr
  | .let2 _ _ _ r, _, ⟨_, _, _, _, hr⟩ => Region.noClobber_of_isSSA r _ hr
  | .case _ _ r _ s, _, ⟨_, _, _, hr, hs⟩ =>
      ⟨Region.noClobber_of_isSSA r _ hr, Region.noClobber_of_isSSA s _ hs⟩
  | .join r _ x t, Γ, ⟨hr, _, ht⟩ => by
      refine ⟨Region.noClobber_of_isSSA r _ hr, Region.noClobber_of_isSSA t _ ht, ?_⟩
      have hfv := Region.fv_subset_of_isSSA t _ ht
      have hb := Region.bound_disjoint_of_isSSA r _ hr
      rw [Finset.disjoint_left]
      intro z hz hzb
      rw [Finset.mem_erase] at hz
      have : z ∈ Γ := by simpa [hz.1] using hfv hz.2
      exact Finset.disjoint_left.1 hb hzb this

/-! ## Instruction renaming commutes with both semantics -/

omit [Monad M] [DecidableEq V] [DecidableEq L] [LawfulMonad M] in
theorem Val.eval_reduct (h : F → F') (m : Model F' M α) (σ : V → α) :
    ∀ a : Val V, a.eval (m.reduct h) σ = a.eval m σ
  | .var _ => rfl
  | .unit => rfl
  | .pair a b => by simp only [Val.eval, Val.eval_reduct h m σ a, Val.eval_reduct h m σ b]; rfl

omit [DecidableEq V] [DecidableEq L] [LawfulMonad M] in
theorem Op.eval_mapOp (h : F → F') (m : Model F' M α) (σ : V → α) (o : Op V F) :
    (o.mapOp h).eval m σ = o.eval (m.reduct h) σ := by
  cases o <;> simp only [Op.mapOp, Op.eval, Val.eval_reduct] <;> rfl

omit [LawfulMonad M] in
theorem Region.evalSSA_mapOp (h : F → F') (m : Model F' M α) :
    ∀ (r : Region V L F) (ρ : V → α), (r.mapOp h).evalSSA m ρ = r.evalSSA (m.reduct h) ρ
  | .br _ a, _ => by simp only [Region.mapOp, Region.evalSSA, Val.eval_reduct]
  | .let1 x o r, ρ => by
      simp only [Region.mapOp, Region.evalSSA, Op.eval_mapOp, Region.evalSSA_mapOp h m r]
  | .let2 x y o r, ρ => by
      simp only [Region.mapOp, Region.evalSSA, Op.eval_mapOp, Region.evalSSA_mapOp h m r]; rfl
  | .case o x r y s, ρ => by
      simp only [Region.mapOp, Region.evalSSA, Op.eval_mapOp, Region.evalSSA_mapOp h m r,
        Region.evalSSA_mapOp h m s]; rfl
  | .join r ℓ x t, ρ => by
      simp only [Region.mapOp, Region.evalSSA, Region.evalSSA_mapOp h m r,
        Region.evalSSA_mapOp h m t]

omit [LawfulMonad M] in
theorem Region.evalRTL_mapOp (h : F → F') (m : Model F' M α) :
    ∀ (r : Region V L F) (σ : V → α), (r.mapOp h).evalRTL m σ = r.evalRTL (m.reduct h) σ
  | .br _ a, _ => by simp only [Region.mapOp, Region.evalRTL, Val.eval_reduct]
  | .let1 x o r, σ => by
      simp only [Region.mapOp, Region.evalRTL, Op.eval_mapOp, Region.evalRTL_mapOp h m r]
  | .let2 x y o r, σ => by
      simp only [Region.mapOp, Region.evalRTL, Op.eval_mapOp, Region.evalRTL_mapOp h m r]; rfl
  | .case o x r y s, σ => by
      simp only [Region.mapOp, Region.evalRTL, Op.eval_mapOp, Region.evalRTL_mapOp h m r,
        Region.evalRTL_mapOp h m s]; rfl
  | .join r ℓ x t, σ => by
      simp only [Region.mapOp, Region.evalRTL, Region.evalRTL_mapOp h m r,
        Region.evalRTL_mapOp h m t]

omit [Monad M] [DecidableEq L] [LawfulMonad M] in
theorem Op.fv_mapOp (h : F → F') (o : Op V F) : (o.mapOp h).fv = o.fv := by
  cases o <;> rfl

omit [Monad M] [DecidableEq L] [LawfulMonad M] in
theorem Region.fv_mapOp (h : F → F') :
    ∀ r : Region V L F, (r.mapOp h).fv = r.fv
  | .br _ _ => rfl
  | .let1 _ o r => by simp only [Region.mapOp, Region.fv, Op.fv_mapOp, Region.fv_mapOp h r]
  | .let2 _ _ o r => by simp only [Region.mapOp, Region.fv, Op.fv_mapOp, Region.fv_mapOp h r]
  | .case o _ r _ s => by
      simp only [Region.mapOp, Region.fv, Op.fv_mapOp, Region.fv_mapOp h r, Region.fv_mapOp h s]
  | .join r _ _ t => by
      simp only [Region.mapOp, Region.fv, Region.fv_mapOp h r, Region.fv_mapOp h t]

omit [Monad M] [DecidableEq L] [LawfulMonad M] in
theorem Region.isSSA_mapOp (h : F → F') :
    ∀ (r : Region V L F) (Γ : Finset V), (r.mapOp h).IsSSA Γ ↔ r.IsSSA Γ
  | .br _ _, _ => Iff.rfl
  | .let1 _ o r, _ => by
      simp only [Region.mapOp, Region.IsSSA, Op.fv_mapOp, Region.isSSA_mapOp h r]
  | .let2 _ _ o r, _ => by
      simp only [Region.mapOp, Region.IsSSA, Op.fv_mapOp, Region.isSSA_mapOp h r]
  | .case o _ r _ s, _ => by
      simp only [Region.mapOp, Region.IsSSA, Op.fv_mapOp, Region.isSSA_mapOp h r,
        Region.isSSA_mapOp h s]
  | .join r _ _ t, _ => by
      simp only [Region.mapOp, Region.IsSSA, Region.isSSA_mapOp h r, Region.isSSA_mapOp h t]

end Silmaril.Proofs.SSA.LambdaRTL

namespace Silmaril.Proofs.SSA.LambdaRTL

open Silmaril.SSA.LambdaRTL

universe v₂ w₂

variable {V L : Type w₂} {F F' F'' : Type v₂}

theorem Op.mapOp_id (o : Op V F) : o.mapOp id = o := by cases o <;> rfl

theorem Op.mapOp_comp (h : F → F') (k : F' → F'') (o : Op V F) :
    o.mapOp (k ∘ h) = (o.mapOp h).mapOp k := by cases o <;> rfl

theorem Region.mapOp_id : ∀ r : Region V L F, r.mapOp id = r
  | .br _ _ => rfl
  | .let1 _ o r => by simp only [Region.mapOp, Op.mapOp_id, Region.mapOp_id r]
  | .let2 _ _ o r => by simp only [Region.mapOp, Op.mapOp_id, Region.mapOp_id r]
  | .case o _ r _ s => by simp only [Region.mapOp, Op.mapOp_id, Region.mapOp_id r, Region.mapOp_id s]
  | .join r _ _ t => by simp only [Region.mapOp, Region.mapOp_id r, Region.mapOp_id t]

theorem Region.mapOp_comp (h : F → F') (k : F' → F'') :
    ∀ r : Region V L F, r.mapOp (k ∘ h) = (r.mapOp h).mapOp k
  | .br _ _ => rfl
  | .let1 _ o r => by
      simp only [Region.mapOp, Op.mapOp_comp h k o, Region.mapOp_comp h k r]
  | .let2 _ _ o r => by
      simp only [Region.mapOp, Op.mapOp_comp h k o, Region.mapOp_comp h k r]
  | .case o _ r _ s => by
      simp only [Region.mapOp, Op.mapOp_comp h k o, Region.mapOp_comp h k r,
        Region.mapOp_comp h k s]
  | .join r _ _ t => by
      simp only [Region.mapOp, Region.mapOp_comp h k r, Region.mapOp_comp h k t]

end Silmaril.Proofs.SSA.LambdaRTL
