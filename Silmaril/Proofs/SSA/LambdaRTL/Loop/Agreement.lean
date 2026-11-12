module

public import Silmaril.SSA.LambdaRTL.Loop.Defs
import Silmaril.Proofs.SSA.LambdaRTL.Agreement

/-!
# λRTL with loops vs lexical λSSA: frame, congruence and agreement (proofs)

Restated in `Silmaril.SSA.LambdaRTL.Loop.Thms`.

The loop cases go through the Elgot laws only, in the form of `iter_eq_of_retract`: two
iterations agree on the image of a pure retraction `h` of the state space when the first body
keeps its continuation states in that image and its image under `h`/`k` is the second body.
For a loop with fixed definition-site store `σ` and assigned set `S`, the retraction
`retract σ S (a, τ) = (a, σ|_{∁S} ∪ τ|_S)` resets every register outside `S` to `σ`; the frame
lemma for the handler shows that the λRTL body maps the image of `retract` into itself, and on
that image the handler's live-ins (disjoint from `S` by `NoClobber`) are those of `σ`. This
replaces the bind-congruence frame lemma, which cannot be fed to the (pure, all-inputs)
uniformity law directly.
-/

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.Loop

open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.Loop Silmaril.Elgot

universe v w

/-! ## Uniformity through a pure retraction -/

section Elgot

variable {m : Type w → Type w} [Monad m] [LawfulMonad m] [Iterate m] [LawfulElgotMonad m]

/-- **Uniformity on the image of a retraction.** If the body `f`, started in the image of
`h : A → A`, only continues in that image (`hf`), and its continuation states mapped by
`k : A → C` give the body `g` (`hfg`), then iterating `f` from `h a` is iterating `g` from
`k a`. Two instances of the (pure) uniformity law for the body `f ∘ h`. -/
theorem iter_eq_of_retract {A B C : Type w} (f : A → m (B ⊕ A)) (g : C → m (B ⊕ C))
    (h : A → A) (k : A → C)
    (hf : ∀ a, (f (h a) >>= fun s => pure (Sum.map id h s)) = f (h a))
    (hfg : ∀ a, (f (h a) >>= fun s => pure (Sum.map id k s)) = g (k a)) (a : A) :
    iter f (h a) = iter g (k a) := by
  have u1 := LawfulElgotMonad.uniformity (fun a => f (h a)) f h (by
    funext a
    simp only [Bind.kleisliRight, liftPure, Function.comp_def, pure_bind]
    exact hf a)
  have u2 := LawfulElgotMonad.uniformity (fun a => f (h a)) g k (by
    funext a
    simp only [Bind.kleisliRight, liftPure, Function.comp_def, pure_bind]
    exact hfg a)
  have e1 := congrFun u1 a
  have e2 := congrFun u2 a
  simp only [Bind.kleisliRight, liftPure, Function.comp_def, pure_bind] at e1 e2
  exact e1.symm.trans e2

omit [Iterate m] [LawfulElgotMonad m] in
/-- `mapReturn` along a pure map is a functorial map of the body. -/
theorem mapReturn_pure {A B C : Type w} (f : A → m (B ⊕ A)) (g : B → C) :
    mapReturn f (fun b => pure (g b)) = fun a => Sum.map g id <$> f a := by
  funext a
  simp only [mapReturn, map_eq_pure_bind]
  congr 1
  funext s
  cases s <;> simp [Function.comp_def]

/-- Naturality for a pure post-map. -/
theorem map_iter {A B C : Type w} (f : A → m (B ⊕ A)) (g : B → C) (a : A) :
    g <$> iter f a = iter (fun a => Sum.map g id <$> f a) a := by
  have := congrFun (LawfulElgotMonad.naturality f (fun b => pure (g b))) a
  rw [mapReturn_pure] at this
  simpa only [Bind.kleisliRight, map_eq_pure_bind, Function.comp_def] using this

end Elgot

/-! ## Restoring a store outside a set of registers -/

section Mix

variable {V : Type w} {α : Type w} [DecidableEq V]

/-- `τ` on `S`, `σ` elsewhere. -/
def mix (σ : V → α) (S : Finset V) (τ : V → α) : V → α :=
  fun y => if y ∈ S then τ y else σ y

/-- The retraction of loop states onto those whose store is `σ` outside `S`. -/
def retract (σ : V → α) (S : Finset V) (p : α × (V → α)) : α × (V → α) :=
  (p.1, mix σ S p.2)

/-- The same retraction on outcomes. -/
def restore {L : Type w} (σ : V → α) (S : Finset V) (e : L × α × (V → α)) :
    L × α × (V → α) :=
  (e.1, e.2.1, mix σ S e.2.2)

theorem mix_of_not_mem (σ τ : V → α) {S : Finset V} {y : V} (hy : y ∉ S) :
    mix σ S τ y = σ y := by
  simp [mix, hy]

theorem mix_eq_self {σ τ : V → α} {S : Finset V} (h : ∀ y, y ∉ S → τ y = σ y) :
    mix σ S τ = τ := by
  funext y
  by_cases hy : y ∈ S
  · simp [mix, hy]
  · simp [mix, hy, h y hy]

/-- A store produced by a handler (which assigns only `T ⊆ S`) from `(mix σ S ω)[x ↦ a]`,
`x ∈ S`, is fixed by `mix σ S`. -/
theorem mix_framed {σ ω σ' : V → α} {S T : Finset V} {x : V} {a : α} (hx : x ∈ S)
    (hT : T ⊆ S) (h : ∀ y, y ∉ T → σ' y = upd (mix σ S ω) x a y) : mix σ S σ' = σ' := by
  apply mix_eq_self
  intro y hy
  have hyx : y ≠ x := fun e => hy (e ▸ hx)
  rw [h y (fun e => hy (hT e)), Silmaril.Proofs.SSA.LambdaRTL.upd_of_ne _ _ hyx,
    mix_of_not_mem _ _ hy]

end Mix

variable {V L : Type w} {F F' : Type v} {M : Type w → Type w} {α : Type w}

/-! ## Congruence: evaluation depends only on free variables -/

variable [Monad M] [Iterate M] [DecidableEq V] [DecidableEq L]

/-- The lexical semantics only reads free variables. -/
theorem Region.evalSSA_congr (m : Model F M α) :
    ∀ (r : Loop.Region V L F) {ρ₁ ρ₂ : V → α}, (∀ y ∈ r.fv, ρ₁ y = ρ₂ y) →
      r.evalSSA m ρ₁ = r.evalSSA m ρ₂
  | .br ℓ a, ρ₁, ρ₂, h => by
      simp only [Loop.Region.evalSSA]
      rw [Silmaril.Proofs.SSA.LambdaRTL.Val.eval_congr m a h]
  | .let1 x o r, ρ₁, ρ₂, h => by
      simp only [Loop.Region.evalSSA]
      rw [Silmaril.Proofs.SSA.LambdaRTL.Op.eval_congr m o
        (fun y hy => h y (by simp [Loop.Region.fv, hy]))]
      congr 1; funext a
      exact Region.evalSSA_congr m r (Silmaril.Proofs.SSA.LambdaRTL.upd_agree x a
        (fun y hy => h y (by simp [Loop.Region.fv, hy])))
  | .let2 x y o r, ρ₁, ρ₂, h => by
      simp only [Loop.Region.evalSSA]
      rw [Silmaril.Proofs.SSA.LambdaRTL.Op.eval_congr m o
        (fun z hz => h z (by simp [Loop.Region.fv, hz]))]
      congr 1; funext p
      apply Region.evalSSA_congr m r
      apply Silmaril.Proofs.SSA.LambdaRTL.upd_agree y p.2
      intro z hz
      apply Silmaril.Proofs.SSA.LambdaRTL.upd_agree x p.1 _ z hz
      intro w hw
      exact h w (by simp [Loop.Region.fv, hw])
  | .case o x r y s, ρ₁, ρ₂, h => by
      simp only [Loop.Region.evalSSA]
      rw [Silmaril.Proofs.SSA.LambdaRTL.Op.eval_congr m o
        (fun z hz => h z (by simp [Loop.Region.fv, hz]))]
      congr 1; funext c
      cases c with
      | inl a =>
          exact Region.evalSSA_congr m r (Silmaril.Proofs.SSA.LambdaRTL.upd_agree x a
            (fun z hz => h z (by simp [Loop.Region.fv, hz])))
      | inr b =>
          exact Region.evalSSA_congr m s (Silmaril.Proofs.SSA.LambdaRTL.upd_agree y b
            (fun z hz => h z (by simp [Loop.Region.fv, hz])))
  | .join r ℓ x t, ρ₁, ρ₂, h => by
      simp only [Loop.Region.evalSSA]
      rw [Region.evalSSA_congr m r (fun z hz => h z (by simp [Loop.Region.fv, hz]))]
      congr 1; funext e
      split
      · exact Region.evalSSA_congr m t (Silmaril.Proofs.SSA.LambdaRTL.upd_agree x e.2
          (fun z hz => h z (by simp [Loop.Region.fv, hz])))
      · rfl
  | .loop r ℓ x t, ρ₁, ρ₂, h => by
      simp only [Loop.Region.evalSSA]
      rw [Region.evalSSA_congr m r (fun z hz => h z (by simp [Loop.Region.fv, hz]))]
      have ht : ∀ a, t.evalSSA m (upd ρ₁ x a) = t.evalSSA m (upd ρ₂ x a) := fun a =>
        Region.evalSSA_congr m t (Silmaril.Proofs.SSA.LambdaRTL.upd_agree x a
          (fun z hz => h z (by simp [Loop.Region.fv, hz])))
      simp only [ht]

/-! ## Frame: λRTL only writes registers it assigns -/

variable [LawfulMonad M]

omit [Iterate M] [DecidableEq V] [DecidableEq L] in
/-- The frame property in functorial form, derived from the bind-congruence form. -/
theorem map_congr_of_frame {β : Type w} {X : M (L × α × (V → α))} {P : (V → α) → Prop}
    (frame : ∀ (f g : L × α × (V → α) → M β),
      (∀ l a σ', P σ' → f (l, a, σ') = g (l, a, σ')) → (X >>= f) = (X >>= g))
    (φ ψ : L × α × (V → α) → β) (h : ∀ l a σ', P σ' → φ (l, a, σ') = ψ (l, a, σ')) :
    φ <$> X = ψ <$> X := by
  simp only [map_eq_pure_bind]
  exact frame _ _ (fun l a σ' hσ' => by simp only [h l a σ' hσ'])

section LoopStep

variable [LawfulElgotMonad M]

/-- One λRTL loop iteration preserves the retracted states, and restoring the exits is a
no-op on them. Hence the λRTL loop from a state that is `σ` outside `S` only exits with stores
that are `σ` outside `S`. -/
theorem iter_restore (m : Model F M α) (t : Loop.Region V L F) (ℓ : L) (x : V) (σ : V → α)
    (S : Finset V) (hx : x ∈ S) (hT : t.bound ⊆ S)
    (tframe : ∀ (τ : V → α) (φ ψ : L × α × (V → α) → (L × α × (V → α)) ⊕ (α × (V → α))),
      (∀ l a σ', (∀ y, y ∉ t.bound → σ' y = τ y) → φ (l, a, σ') = ψ (l, a, σ')) →
      φ <$> t.evalRTL m τ = ψ <$> t.evalRTL m τ)
    (p : α × (V → α)) (hp : ∀ y, y ∉ S → p.2 y = σ y) :
    iter (fun p => routeRTL ℓ <$> t.evalRTL m (upd p.2 x p.1)) p =
      restore σ S <$> iter (fun p => routeRTL ℓ <$> t.evalRTL m (upd p.2 x p.1)) p := by
  have hpr : p = retract σ S p := by
    obtain ⟨a, τ⟩ := p
    simp only [retract, mix_eq_self hp]
  rw [map_iter, hpr]
  symm
  apply iter_eq_of_retract
  · intro q
    simp only [retract, Functor.map_map, bind_pure_comp]
    apply tframe
    intro l b σ' hσ'
    have hmix := mix_framed (σ := σ) (ω := q.2) (a := q.1) hx hT hσ'
    simp only [routeRTL]
    split <;> simp [Sum.map, retract, restore, hmix]
  · intro q
    simp only [retract, Functor.map_map, bind_pure_comp]
    apply tframe
    intro l b σ' hσ'
    have hmix := mix_framed (σ := σ) (ω := q.2) (a := q.1) hx hT hσ'
    simp only [routeRTL]
    split <;> simp [Sum.map, retract, restore, hmix]

/-- The λRTL loop, observed, from a state that is `σ` outside `S` is the lexical loop with
definition-site environment `σ`, provided the handler agrees observationally with its lexical
reading and its live-ins avoid `S`. -/
theorem iter_obs (m : Model F M α) (t : Loop.Region V L F) (ℓ : L) (x : V) (σ : V → α)
    (S : Finset V) (hx : x ∈ S) (hT : t.bound ⊆ S) (hD : Disjoint (t.fv.erase x) S)
    (tframe : ∀ (τ : V → α) (φ ψ : L × α × (V → α) → (L × α) ⊕ (α × (V → α))),
      (∀ l a σ', (∀ y, y ∉ t.bound → σ' y = τ y) → φ (l, a, σ') = ψ (l, a, σ')) →
      φ <$> t.evalRTL m τ = ψ <$> t.evalRTL m τ)
    (tagree : ∀ τ, t.evalObs m τ = t.evalSSA m τ)
    (p : α × (V → α)) (hp : ∀ y, y ∉ S → p.2 y = σ y) :
    obs <$> iter (fun p => routeRTL ℓ <$> t.evalRTL m (upd p.2 x p.1)) p =
      iter (fun a => routeSSA ℓ <$> t.evalSSA m (upd σ x a)) p.1 := by
  have hpr : p = retract σ S p := by
    obtain ⟨a, τ⟩ := p
    simp only [retract, mix_eq_self hp]
  rw [map_iter]
  conv_lhs => rw [hpr]
  apply iter_eq_of_retract (k := Prod.fst)
  · intro q
    simp only [retract, Functor.map_map, bind_pure_comp]
    apply tframe
    intro l b σ' hσ'
    have hmix := mix_framed (σ := σ) (ω := q.2) (a := q.1) hx hT hσ'
    simp only [routeRTL]
    split <;> simp [Sum.map, retract, hmix]
  · intro q
    simp only [retract, Functor.map_map, bind_pure_comp]
    have hroute : (fun e : L × α × (V → α) =>
        Sum.map id Prod.fst (Sum.map obs id (routeRTL ℓ e))) = fun e => routeSSA ℓ (obs e) := by
      funext e
      by_cases he : e.1 = ℓ <;> simp [routeRTL, routeSSA, obs, he]
    rw [hroute, ← Functor.map_map]
    change routeSSA ℓ <$> t.evalObs m _ = _
    rw [tagree]
    congr 1
    apply Region.evalSSA_congr m t
    intro y hy
    by_cases hyx : y = x
    · subst hyx
      simp [upd]
    · have hyS : y ∉ S := Finset.disjoint_left.1 hD (Finset.mem_erase.2 ⟨hyx, hy⟩)
      rw [Silmaril.Proofs.SSA.LambdaRTL.upd_of_ne _ _ hyx,
        Silmaril.Proofs.SSA.LambdaRTL.upd_of_ne _ _ hyx, mix_of_not_mem _ _ hyS]

end LoopStep

variable [LawfulElgotMonad M]

/-- **Frame lemma** with loops (bind-congruence form): two continuations that agree on every
outcome whose store agrees with the initial store outside `r.bound` give equal results. -/
theorem Region.evalRTL_frame' (m : Model F M α) :
    ∀ (r : Loop.Region V L F) (β : Type w) (σ : V → α) (f g : L × α × (V → α) → M β),
      (∀ l a σ', (∀ y, y ∉ r.bound → σ' y = σ y) → f (l, a, σ') = g (l, a, σ')) →
      (r.evalRTL m σ >>= f) = (r.evalRTL m σ >>= g)
  | .br ℓ a, β, σ, f, g, h => by
      simp only [Loop.Region.evalRTL, pure_bind]
      exact h _ _ _ (fun _ _ => rfl)
  | .let1 x o r, β, σ, f, g, h => by
      simp only [Loop.Region.evalRTL, bind_assoc]
      congr 1; funext a
      apply Region.evalRTL_frame' m r β
      intro l b σ' hσ'
      apply h
      intro y hy
      have hyx : y ≠ x := fun e => hy (by simp [Loop.Region.bound, e])
      have hyr : y ∉ r.bound := fun e => hy (by simp [Loop.Region.bound, e])
      rw [hσ' y hyr, Silmaril.Proofs.SSA.LambdaRTL.upd_of_ne _ _ hyx]
  | .let2 x y o r, β, σ, f, g, h => by
      simp only [Loop.Region.evalRTL, bind_assoc]
      congr 1; funext a; congr 1; funext p
      apply Region.evalRTL_frame' m r β
      intro l b σ' hσ'
      apply h
      intro z hz
      have hzx : z ≠ x := fun e => hz (by simp [Loop.Region.bound, e])
      have hzy : z ≠ y := fun e => hz (by simp [Loop.Region.bound, e])
      have hzr : z ∉ r.bound := fun e => hz (by simp [Loop.Region.bound, e])
      rw [hσ' z hzr, Silmaril.Proofs.SSA.LambdaRTL.upd_of_ne _ _ hzy,
        Silmaril.Proofs.SSA.LambdaRTL.upd_of_ne _ _ hzx]
  | .case o x r y s, β, σ, f, g, h => by
      simp only [Loop.Region.evalRTL, bind_assoc]
      congr 1; funext a; congr 1; funext c
      cases c with
      | inl b =>
          apply Region.evalRTL_frame' m r β
          intro l b' σ' hσ'
          apply h
          intro z hz
          have hzx : z ≠ x := fun e => hz (by simp [Loop.Region.bound, e])
          have hzr : z ∉ r.bound := fun e => hz (by simp [Loop.Region.bound, e])
          rw [hσ' z hzr, Silmaril.Proofs.SSA.LambdaRTL.upd_of_ne _ _ hzx]
      | inr b =>
          apply Region.evalRTL_frame' m s β
          intro l b' σ' hσ'
          apply h
          intro z hz
          have hzy : z ≠ y := fun e => hz (by simp [Loop.Region.bound, e])
          have hzs : z ∉ s.bound := fun e => hz (by simp [Loop.Region.bound, e])
          rw [hσ' z hzs, Silmaril.Proofs.SSA.LambdaRTL.upd_of_ne _ _ hzy]
  | .join r ℓ x t, β, σ, f, g, h => by
      simp only [Loop.Region.evalRTL, bind_assoc]
      apply Region.evalRTL_frame' m r β
      intro l a σ' hσ'
      dsimp only
      split
      · apply Region.evalRTL_frame' m t β
        intro l' b σ'' hσ''
        apply h
        intro z hz
        have hzr : z ∉ r.bound := fun e => hz (by simp [Loop.Region.bound, e])
        have hzx : z ≠ x := fun e => hz (by simp [Loop.Region.bound, e])
        have hzt : z ∉ t.bound := fun e => hz (by simp [Loop.Region.bound, e])
        rw [hσ'' z hzt, Silmaril.Proofs.SSA.LambdaRTL.upd_of_ne _ _ hzx, hσ' z hzr]
      · simp only [pure_bind]
        apply h
        intro z hz
        exact hσ' z (fun e => hz (by simp [Loop.Region.bound, e]))
  | .loop r ℓ x t, β, σ, f, g, h => by
      simp only [Loop.Region.evalRTL, bind_assoc]
      apply Region.evalRTL_frame' m r β
      intro l a σ' hσ'
      dsimp only
      split
      · have hx : x ∈ (Loop.Region.loop r ℓ x t).bound := by simp [Loop.Region.bound]
        have hT : t.bound ⊆ (Loop.Region.loop r ℓ x t).bound := by
          intro z hz; simp [Loop.Region.bound, hz]
        rw [iter_restore m t ℓ x σ _ hx hT
          (fun τ φ ψ hφψ => map_congr_of_frame
            (fun f g hfg => Region.evalRTL_frame' m t _ τ f g hfg) φ ψ hφψ)
          (a, σ') (fun y hy => hσ' y (fun e => hy (by simp [Loop.Region.bound, e]))),
          bind_map_left, bind_map_left]
        congr 1; funext e
        apply h
        intro y hy
        exact mix_of_not_mem _ _ hy
      · simp only [pure_bind]
        apply h
        intro z hz
        exact hσ' z (fun e => hz (by simp [Loop.Region.bound, e]))

/-- **Frame lemma** with loops (bind-congruence form). -/
theorem Region.evalRTL_frame (m : Model F M α) {β : Type w} (r : Loop.Region V L F)
    (σ : V → α) (f g : L × α × (V → α) → M β)
    (h : ∀ l a σ', (∀ y, y ∉ r.bound → σ' y = σ y) → f (l, a, σ') = g (l, a, σ')) :
    (r.evalRTL m σ >>= f) = (r.evalRTL m σ >>= g) :=
  Region.evalRTL_frame' m r β σ f g h

/-! ## Agreement of the two readings under no-clobbering -/

/-- Under `NoClobber`, the observable λRTL semantics with loops is the lexical λSSA
semantics. -/
theorem Region.evalObs_eq_evalSSA (m : Model F M α) :
    ∀ (r : Loop.Region V L F), r.NoClobber → ∀ σ : V → α, r.evalObs m σ = r.evalSSA m σ
  | .br ℓ a, _, σ => by
      simp [Loop.Region.evalObs, Loop.Region.evalRTL, Loop.Region.evalSSA, obs]
  | .let1 x o r, hr, σ => by
      simp only [Loop.Region.evalObs, Loop.Region.evalRTL, Loop.Region.evalSSA, map_bind]
      congr 1; funext a
      exact Region.evalObs_eq_evalSSA m r hr _
  | .let2 x y o r, hr, σ => by
      simp only [Loop.Region.evalObs, Loop.Region.evalRTL, Loop.Region.evalSSA, map_bind]
      congr 1; funext p
      exact Region.evalObs_eq_evalSSA m r hr _
  | .case o x r y s, hr, σ => by
      simp only [Loop.Region.evalObs, Loop.Region.evalRTL, Loop.Region.evalSSA, map_bind]
      congr 1; funext c
      cases c with
      | inl b => exact Region.evalObs_eq_evalSSA m r hr.1 _
      | inr b => exact Region.evalObs_eq_evalSSA m s hr.2 _
  | .join r ℓ x t, hr, σ => by
      obtain ⟨hr, ht, hdisj⟩ := hr
      have ihr := Region.evalObs_eq_evalSSA m r hr σ
      simp only [Loop.Region.evalObs] at ihr
      simp only [Loop.Region.evalObs, Loop.Region.evalRTL, Loop.Region.evalSSA, map_bind]
      rw [← ihr, bind_map_left]
      apply Region.evalRTL_frame m r
      intro l a σ' hσ'
      by_cases hl : l = ℓ
      · subst hl
        simp only [obs, ↓reduceIte]
        exact (Region.evalObs_eq_evalSSA m t ht _).trans
          (Region.evalSSA_congr m t (Silmaril.Proofs.SSA.LambdaRTL.upd_agree x a
            fun z hz => hσ' z (Finset.disjoint_left.1 hdisj hz)))
      · simp [obs, hl]
  | .loop r ℓ x t, hr, σ => by
      obtain ⟨hr, ht, hdisj⟩ := hr
      have ihr := Region.evalObs_eq_evalSSA m r hr σ
      simp only [Loop.Region.evalObs] at ihr
      simp only [Loop.Region.evalObs, Loop.Region.evalRTL, Loop.Region.evalSSA, map_bind]
      rw [← ihr, bind_map_left]
      apply Region.evalRTL_frame m r
      intro l a σ' hσ'
      by_cases hl : l = ℓ
      · subst hl
        simp only [obs, ↓reduceIte]
        have hD : Disjoint (t.fv.erase x) (r.bound ∪ insert x t.bound) := by
          rw [Finset.disjoint_left]
          intro z hz hzS
          have hzx : z ≠ x := (Finset.mem_erase.1 hz).1
          have : z ∈ r.bound ∪ t.bound := by
            simp only [Finset.mem_union, Finset.mem_insert] at hzS ⊢
            tauto
          exact Finset.disjoint_left.1 hdisj hz this
        exact iter_obs m t l x σ (r.bound ∪ insert x t.bound) (by simp)
          (fun z hz => by simp [hz]) hD
          (fun τ φ ψ hφψ => map_congr_of_frame
            (fun f g hfg => Region.evalRTL_frame m t τ f g hfg) φ ψ hφψ)
          (Region.evalObs_eq_evalSSA m t ht) (a, σ')
          (fun y hy => hσ' y (fun e => hy (by simp [e])))
      · simp [obs, hl]

/-! ## Dominance-scoped SSA implies no clobbering -/

omit [Monad M] [Iterate M] [DecidableEq L] [LawfulMonad M] [LawfulElgotMonad M] in
theorem Region.fv_subset_of_isSSA :
    ∀ (r : Loop.Region V L F) (Γ : Finset V), r.IsSSA Γ → r.fv ⊆ Γ
  | .br _ a, Γ, h => h
  | .let1 x o r, Γ, ⟨ho, _, hr⟩ => fun z hz => by
      simp only [Loop.Region.fv, Finset.mem_union, Finset.mem_erase] at hz
      rcases hz with hz | ⟨hzx, hz⟩
      · exact ho hz
      · have := Region.fv_subset_of_isSSA r _ hr hz
        simpa [hzx] using this
  | .let2 x y o r, Γ, ⟨ho, _, _, _, hr⟩ => fun z hz => by
      simp only [Loop.Region.fv, Finset.mem_union, Finset.mem_erase] at hz
      rcases hz with hz | ⟨hzx, hzy, hz⟩
      · exact ho hz
      · have := Region.fv_subset_of_isSSA r _ hr hz
        simpa [hzx, hzy] using this
  | .case o x r y s, Γ, ⟨ho, _, _, hr, hs⟩ => fun z hz => by
      simp only [Loop.Region.fv, Finset.mem_union, Finset.mem_erase] at hz
      rcases hz with (hz | ⟨hzx, hz⟩) | ⟨hzy, hz⟩
      · exact ho hz
      · have := Region.fv_subset_of_isSSA r _ hr hz
        simpa [hzx] using this
      · have := Region.fv_subset_of_isSSA s _ hs hz
        simpa [hzy] using this
  | .join r _ x t, Γ, ⟨hr, _, ht⟩ => fun z hz => by
      simp only [Loop.Region.fv, Finset.mem_union, Finset.mem_erase] at hz
      rcases hz with hz | ⟨hzx, hz⟩
      · exact Region.fv_subset_of_isSSA r _ hr hz
      · have := Region.fv_subset_of_isSSA t _ ht hz
        simpa [hzx] using this
  | .loop r _ x t, Γ, ⟨hr, _, ht⟩ => fun z hz => by
      simp only [Loop.Region.fv, Finset.mem_union, Finset.mem_erase] at hz
      rcases hz with hz | ⟨hzx, hz⟩
      · exact Region.fv_subset_of_isSSA r _ hr hz
      · have := Region.fv_subset_of_isSSA t _ ht hz
        simpa [hzx] using this

omit [Monad M] [Iterate M] [DecidableEq L] [LawfulMonad M] [LawfulElgotMonad M] in
theorem Region.bound_disjoint_of_isSSA :
    ∀ (r : Loop.Region V L F) (Γ : Finset V), r.IsSSA Γ → Disjoint r.bound Γ
  | .br _ _, _, _ => by simp [Loop.Region.bound]
  | .let1 x o r, Γ, ⟨_, hx, hr⟩ => by
      have := Region.bound_disjoint_of_isSSA r _ hr
      simp only [Loop.Region.bound, Finset.disjoint_insert_left]
      exact ⟨hx, Finset.disjoint_of_subset_right (Finset.subset_insert _ _) this⟩
  | .let2 x y o r, Γ, ⟨_, hx, hy, _, hr⟩ => by
      have := Region.bound_disjoint_of_isSSA r _ hr
      simp only [Loop.Region.bound, Finset.disjoint_insert_left]
      refine ⟨hx, hy, Finset.disjoint_of_subset_right ?_ this⟩
      intro z hz; simp [hz]
  | .case o x r y s, Γ, ⟨_, hx, hy, hr, hs⟩ => by
      have h1 := Region.bound_disjoint_of_isSSA r _ hr
      have h2 := Region.bound_disjoint_of_isSSA s _ hs
      simp only [Loop.Region.bound, Finset.disjoint_insert_left, Finset.disjoint_union_left]
      exact ⟨hx, hy, Finset.disjoint_of_subset_right (Finset.subset_insert _ _) h1,
        Finset.disjoint_of_subset_right (Finset.subset_insert _ _) h2⟩
  | .join r _ x t, Γ, ⟨hr, hx, ht⟩ => by
      have h1 := Region.bound_disjoint_of_isSSA r _ hr
      have h2 := Region.bound_disjoint_of_isSSA t _ ht
      simp only [Loop.Region.bound, Finset.disjoint_insert_left, Finset.disjoint_union_left]
      exact ⟨h1, hx, Finset.disjoint_of_subset_right (Finset.subset_insert _ _) h2⟩
  | .loop r _ x t, Γ, ⟨hr, hx, ht⟩ => by
      have h1 := Region.bound_disjoint_of_isSSA r _ hr
      have h2 := Region.bound_disjoint_of_isSSA t _ ht
      simp only [Loop.Region.bound, Finset.disjoint_insert_left, Finset.disjoint_union_left]
      exact ⟨h1, hx, Finset.disjoint_of_subset_right (Finset.subset_insert _ _) h2⟩

omit [Monad M] [Iterate M] [DecidableEq L] [LawfulMonad M] [LawfulElgotMonad M] in
theorem Region.noClobber_of_isSSA :
    ∀ (r : Loop.Region V L F) (Γ : Finset V), r.IsSSA Γ → r.NoClobber
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
  | .loop r _ x t, Γ, ⟨hr, _, ht⟩ => by
      refine ⟨Region.noClobber_of_isSSA r _ hr, Region.noClobber_of_isSSA t _ ht, ?_⟩
      have hfv := Region.fv_subset_of_isSSA t _ ht
      have hb := Region.bound_disjoint_of_isSSA r _ hr
      have hbt := Region.bound_disjoint_of_isSSA t _ ht
      rw [Finset.disjoint_left]
      intro z hz hzb
      rw [Finset.mem_erase] at hz
      have hzΓ : z ∈ Γ := by simpa [hz.1] using hfv hz.2
      rcases Finset.mem_union.1 hzb with hzb | hzb
      · exact Finset.disjoint_left.1 hb hzb hzΓ
      · exact Finset.disjoint_left.1 hbt hzb (Finset.mem_insert_of_mem hzΓ)

/-! ## Instruction renaming commutes with both semantics -/

omit [LawfulMonad M] [LawfulElgotMonad M] in
theorem Region.evalSSA_mapOp (h : F → F') (m : Model F' M α) :
    ∀ (r : Loop.Region V L F) (ρ : V → α), (r.mapOp h).evalSSA m ρ = r.evalSSA (m.reduct h) ρ
  | .br _ a, _ => by
      simp only [Loop.Region.mapOp, Loop.Region.evalSSA,
        Silmaril.Proofs.SSA.LambdaRTL.Val.eval_reduct]
  | .let1 x o r, ρ => by
      simp only [Loop.Region.mapOp, Loop.Region.evalSSA,
        Silmaril.Proofs.SSA.LambdaRTL.Op.eval_mapOp, Region.evalSSA_mapOp h m r]
  | .let2 x y o r, ρ => by
      simp only [Loop.Region.mapOp, Loop.Region.evalSSA,
        Silmaril.Proofs.SSA.LambdaRTL.Op.eval_mapOp, Region.evalSSA_mapOp h m r]; rfl
  | .case o x r y s, ρ => by
      simp only [Loop.Region.mapOp, Loop.Region.evalSSA,
        Silmaril.Proofs.SSA.LambdaRTL.Op.eval_mapOp, Region.evalSSA_mapOp h m r,
        Region.evalSSA_mapOp h m s]; rfl
  | .join r ℓ x t, ρ => by
      simp only [Loop.Region.mapOp, Loop.Region.evalSSA, Region.evalSSA_mapOp h m r,
        Region.evalSSA_mapOp h m t]
  | .loop r ℓ x t, ρ => by
      simp only [Loop.Region.mapOp, Loop.Region.evalSSA, Region.evalSSA_mapOp h m r,
        Region.evalSSA_mapOp h m t]

omit [LawfulMonad M] [LawfulElgotMonad M] in
theorem Region.evalRTL_mapOp (h : F → F') (m : Model F' M α) :
    ∀ (r : Loop.Region V L F) (σ : V → α), (r.mapOp h).evalRTL m σ = r.evalRTL (m.reduct h) σ
  | .br _ a, _ => by
      simp only [Loop.Region.mapOp, Loop.Region.evalRTL,
        Silmaril.Proofs.SSA.LambdaRTL.Val.eval_reduct]
  | .let1 x o r, σ => by
      simp only [Loop.Region.mapOp, Loop.Region.evalRTL,
        Silmaril.Proofs.SSA.LambdaRTL.Op.eval_mapOp, Region.evalRTL_mapOp h m r]
  | .let2 x y o r, σ => by
      simp only [Loop.Region.mapOp, Loop.Region.evalRTL,
        Silmaril.Proofs.SSA.LambdaRTL.Op.eval_mapOp, Region.evalRTL_mapOp h m r]; rfl
  | .case o x r y s, σ => by
      simp only [Loop.Region.mapOp, Loop.Region.evalRTL,
        Silmaril.Proofs.SSA.LambdaRTL.Op.eval_mapOp, Region.evalRTL_mapOp h m r,
        Region.evalRTL_mapOp h m s]; rfl
  | .join r ℓ x t, σ => by
      simp only [Loop.Region.mapOp, Loop.Region.evalRTL, Region.evalRTL_mapOp h m r,
        Region.evalRTL_mapOp h m t]
  | .loop r ℓ x t, σ => by
      simp only [Loop.Region.mapOp, Loop.Region.evalRTL, Region.evalRTL_mapOp h m r,
        Region.evalRTL_mapOp h m t]

omit [Monad M] [Iterate M] [DecidableEq L] [LawfulMonad M] [LawfulElgotMonad M] in
theorem Region.fv_mapOp (h : F → F') :
    ∀ r : Loop.Region V L F, (r.mapOp h).fv = r.fv
  | .br _ _ => rfl
  | .let1 _ o r => by
      simp only [Loop.Region.mapOp, Loop.Region.fv, Silmaril.Proofs.SSA.LambdaRTL.Op.fv_mapOp,
        Region.fv_mapOp h r]
  | .let2 _ _ o r => by
      simp only [Loop.Region.mapOp, Loop.Region.fv, Silmaril.Proofs.SSA.LambdaRTL.Op.fv_mapOp,
        Region.fv_mapOp h r]
  | .case o _ r _ s => by
      simp only [Loop.Region.mapOp, Loop.Region.fv, Silmaril.Proofs.SSA.LambdaRTL.Op.fv_mapOp,
        Region.fv_mapOp h r, Region.fv_mapOp h s]
  | .join r _ _ t => by
      simp only [Loop.Region.mapOp, Loop.Region.fv, Region.fv_mapOp h r, Region.fv_mapOp h t]
  | .loop r _ _ t => by
      simp only [Loop.Region.mapOp, Loop.Region.fv, Region.fv_mapOp h r, Region.fv_mapOp h t]

omit [Monad M] [Iterate M] [DecidableEq L] [LawfulMonad M] [LawfulElgotMonad M] in
theorem Region.isSSA_mapOp (h : F → F') :
    ∀ (r : Loop.Region V L F) (Γ : Finset V), (r.mapOp h).IsSSA Γ ↔ r.IsSSA Γ
  | .br _ _, _ => Iff.rfl
  | .let1 _ o r, _ => by
      simp only [Loop.Region.mapOp, Loop.Region.IsSSA, Silmaril.Proofs.SSA.LambdaRTL.Op.fv_mapOp,
        Region.isSSA_mapOp h r]
  | .let2 _ _ o r, _ => by
      simp only [Loop.Region.mapOp, Loop.Region.IsSSA, Silmaril.Proofs.SSA.LambdaRTL.Op.fv_mapOp,
        Region.isSSA_mapOp h r]
  | .case o _ r _ s, _ => by
      simp only [Loop.Region.mapOp, Loop.Region.IsSSA, Silmaril.Proofs.SSA.LambdaRTL.Op.fv_mapOp,
        Region.isSSA_mapOp h r, Region.isSSA_mapOp h s]
  | .join r _ _ t, _ => by
      simp only [Loop.Region.mapOp, Loop.Region.IsSSA, Region.isSSA_mapOp h r,
        Region.isSSA_mapOp h t]
  | .loop r _ _ t, _ => by
      simp only [Loop.Region.mapOp, Loop.Region.IsSSA, Region.isSSA_mapOp h r,
        Region.isSSA_mapOp h t]

/-! ## The acyclic fragment embeds -/

omit [LawfulMonad M] [LawfulElgotMonad M] in
theorem Region.evalSSA_ofAcyclic (m : Model F M α) :
    ∀ (r : Silmaril.SSA.LambdaRTL.Region V L F) (ρ : V → α),
      (Loop.Region.ofAcyclic r).evalSSA m ρ = r.evalSSA m ρ
  | .br _ _, _ => rfl
  | .let1 x o r, ρ => by
      simp only [Loop.Region.ofAcyclic, Loop.Region.evalSSA, Silmaril.SSA.LambdaRTL.Region.evalSSA,
        Region.evalSSA_ofAcyclic m r]
  | .let2 x y o r, ρ => by
      simp only [Loop.Region.ofAcyclic, Loop.Region.evalSSA, Silmaril.SSA.LambdaRTL.Region.evalSSA,
        Region.evalSSA_ofAcyclic m r]
  | .case o x r y s, ρ => by
      simp only [Loop.Region.ofAcyclic, Loop.Region.evalSSA, Silmaril.SSA.LambdaRTL.Region.evalSSA]
      congr 1; funext c
      cases c <;> simp only [Region.evalSSA_ofAcyclic m r, Region.evalSSA_ofAcyclic m s]
  | .join r ℓ x t, ρ => by
      simp only [Loop.Region.ofAcyclic, Loop.Region.evalSSA, Silmaril.SSA.LambdaRTL.Region.evalSSA,
        Region.evalSSA_ofAcyclic m r, Region.evalSSA_ofAcyclic m t]

omit [LawfulMonad M] [LawfulElgotMonad M] in
theorem Region.evalRTL_ofAcyclic (m : Model F M α) :
    ∀ (r : Silmaril.SSA.LambdaRTL.Region V L F) (σ : V → α),
      (Loop.Region.ofAcyclic r).evalRTL m σ = r.evalRTL m σ
  | .br _ _, _ => rfl
  | .let1 x o r, σ => by
      simp only [Loop.Region.ofAcyclic, Loop.Region.evalRTL, Silmaril.SSA.LambdaRTL.Region.evalRTL,
        Region.evalRTL_ofAcyclic m r]
  | .let2 x y o r, σ => by
      simp only [Loop.Region.ofAcyclic, Loop.Region.evalRTL, Silmaril.SSA.LambdaRTL.Region.evalRTL,
        Region.evalRTL_ofAcyclic m r]
  | .case o x r y s, σ => by
      simp only [Loop.Region.ofAcyclic, Loop.Region.evalRTL, Silmaril.SSA.LambdaRTL.Region.evalRTL]
      congr 1; funext c
      cases c <;> simp only [Region.evalRTL_ofAcyclic m r, Region.evalRTL_ofAcyclic m s]
  | .join r ℓ x t, σ => by
      simp only [Loop.Region.ofAcyclic, Loop.Region.evalRTL, Silmaril.SSA.LambdaRTL.Region.evalRTL,
        Region.evalRTL_ofAcyclic m r, Region.evalRTL_ofAcyclic m t]

omit [Monad M] [Iterate M] [DecidableEq L] [LawfulMonad M] [LawfulElgotMonad M] in
theorem Region.fv_ofAcyclic :
    ∀ r : Silmaril.SSA.LambdaRTL.Region V L F, (Loop.Region.ofAcyclic r).fv = r.fv
  | .br _ _ => rfl
  | .let1 _ _ r => by
      simp only [Loop.Region.ofAcyclic, Loop.Region.fv, Silmaril.SSA.LambdaRTL.Region.fv,
        Region.fv_ofAcyclic r]
  | .let2 _ _ _ r => by
      simp only [Loop.Region.ofAcyclic, Loop.Region.fv, Silmaril.SSA.LambdaRTL.Region.fv,
        Region.fv_ofAcyclic r]
  | .case _ _ r _ s => by
      simp only [Loop.Region.ofAcyclic, Loop.Region.fv, Silmaril.SSA.LambdaRTL.Region.fv,
        Region.fv_ofAcyclic r, Region.fv_ofAcyclic s]
  | .join r _ _ t => by
      simp only [Loop.Region.ofAcyclic, Loop.Region.fv, Silmaril.SSA.LambdaRTL.Region.fv,
        Region.fv_ofAcyclic r, Region.fv_ofAcyclic t]

omit [Monad M] [Iterate M] [DecidableEq L] [LawfulMonad M] [LawfulElgotMonad M] in
theorem Region.bound_ofAcyclic :
    ∀ r : Silmaril.SSA.LambdaRTL.Region V L F, (Loop.Region.ofAcyclic r).bound = r.bound
  | .br _ _ => rfl
  | .let1 _ _ r => by
      simp only [Loop.Region.ofAcyclic, Loop.Region.bound, Silmaril.SSA.LambdaRTL.Region.bound,
        Region.bound_ofAcyclic r]
  | .let2 _ _ _ r => by
      simp only [Loop.Region.ofAcyclic, Loop.Region.bound, Silmaril.SSA.LambdaRTL.Region.bound,
        Region.bound_ofAcyclic r]
  | .case _ _ r _ s => by
      simp only [Loop.Region.ofAcyclic, Loop.Region.bound, Silmaril.SSA.LambdaRTL.Region.bound,
        Region.bound_ofAcyclic r, Region.bound_ofAcyclic s]
  | .join r _ _ t => by
      simp only [Loop.Region.ofAcyclic, Loop.Region.bound, Silmaril.SSA.LambdaRTL.Region.bound,
        Region.bound_ofAcyclic r, Region.bound_ofAcyclic t]

omit [Monad M] [Iterate M] [DecidableEq L] [LawfulMonad M] [LawfulElgotMonad M] in
theorem Region.noClobber_ofAcyclic :
    ∀ r : Silmaril.SSA.LambdaRTL.Region V L F, (Loop.Region.ofAcyclic r).NoClobber ↔ r.NoClobber
  | .br _ _ => Iff.rfl
  | .let1 _ _ r => Region.noClobber_ofAcyclic r
  | .let2 _ _ _ r => Region.noClobber_ofAcyclic r
  | .case _ _ r _ s => by
      simp only [Loop.Region.ofAcyclic, Loop.Region.NoClobber, Silmaril.SSA.LambdaRTL.Region.NoClobber,
        Region.noClobber_ofAcyclic r, Region.noClobber_ofAcyclic s]
  | .join r _ _ t => by
      simp only [Loop.Region.ofAcyclic, Loop.Region.NoClobber, Silmaril.SSA.LambdaRTL.Region.NoClobber,
        Region.noClobber_ofAcyclic r, Region.noClobber_ofAcyclic t, Region.fv_ofAcyclic,
        Region.bound_ofAcyclic]

omit [Monad M] [Iterate M] [DecidableEq L] [LawfulMonad M] [LawfulElgotMonad M] in
theorem Region.isSSA_ofAcyclic :
    ∀ (r : Silmaril.SSA.LambdaRTL.Region V L F) (Γ : Finset V),
      (Loop.Region.ofAcyclic r).IsSSA Γ ↔ r.IsSSA Γ
  | .br _ _, _ => Iff.rfl
  | .let1 _ _ r, _ => by
      simp only [Loop.Region.ofAcyclic, Loop.Region.IsSSA, Silmaril.SSA.LambdaRTL.Region.IsSSA,
        Region.isSSA_ofAcyclic r]
  | .let2 _ _ _ r, _ => by
      simp only [Loop.Region.ofAcyclic, Loop.Region.IsSSA, Silmaril.SSA.LambdaRTL.Region.IsSSA,
        Region.isSSA_ofAcyclic r]
  | .case _ _ r _ s, _ => by
      simp only [Loop.Region.ofAcyclic, Loop.Region.IsSSA, Silmaril.SSA.LambdaRTL.Region.IsSSA,
        Region.isSSA_ofAcyclic r, Region.isSSA_ofAcyclic s]
  | .join r _ _ t, _ => by
      simp only [Loop.Region.ofAcyclic, Loop.Region.IsSSA, Silmaril.SSA.LambdaRTL.Region.IsSSA,
        Region.isSSA_ofAcyclic r, Region.isSSA_ofAcyclic t]

end Silmaril.Proofs.SSA.LambdaRTL.Loop

namespace Silmaril.Proofs.SSA.LambdaRTL.Loop

open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.Loop

universe v₂ w₂

variable {V L : Type w₂} {F F' F'' : Type v₂}

theorem Region.mapOp_id : ∀ r : Loop.Region V L F, r.mapOp id = r
  | .br _ _ => rfl
  | .let1 _ o r => by
      simp only [Loop.Region.mapOp, Silmaril.Proofs.SSA.LambdaRTL.Op.mapOp_id, Region.mapOp_id r]
  | .let2 _ _ o r => by
      simp only [Loop.Region.mapOp, Silmaril.Proofs.SSA.LambdaRTL.Op.mapOp_id, Region.mapOp_id r]
  | .case o _ r _ s => by
      simp only [Loop.Region.mapOp, Silmaril.Proofs.SSA.LambdaRTL.Op.mapOp_id, Region.mapOp_id r,
        Region.mapOp_id s]
  | .join r _ _ t => by simp only [Loop.Region.mapOp, Region.mapOp_id r, Region.mapOp_id t]
  | .loop r _ _ t => by simp only [Loop.Region.mapOp, Region.mapOp_id r, Region.mapOp_id t]

theorem Region.mapOp_comp (h : F → F') (k : F' → F'') :
    ∀ r : Loop.Region V L F, r.mapOp (k ∘ h) = (r.mapOp h).mapOp k
  | .br _ _ => rfl
  | .let1 _ o r => by
      simp only [Loop.Region.mapOp, Silmaril.Proofs.SSA.LambdaRTL.Op.mapOp_comp h k o,
        Region.mapOp_comp h k r]
  | .let2 _ _ o r => by
      simp only [Loop.Region.mapOp, Silmaril.Proofs.SSA.LambdaRTL.Op.mapOp_comp h k o,
        Region.mapOp_comp h k r]
  | .case o _ r _ s => by
      simp only [Loop.Region.mapOp, Silmaril.Proofs.SSA.LambdaRTL.Op.mapOp_comp h k o,
        Region.mapOp_comp h k r, Region.mapOp_comp h k s]
  | .join r _ _ t => by
      simp only [Loop.Region.mapOp, Region.mapOp_comp h k r, Region.mapOp_comp h k t]
  | .loop r _ _ t => by
      simp only [Loop.Region.mapOp, Region.mapOp_comp h k r, Region.mapOp_comp h k t]

theorem Region.mapOp_ofAcyclic (h : F → F') :
    ∀ r : Silmaril.SSA.LambdaRTL.Region V L F, (Loop.Region.ofAcyclic r).mapOp h =
      Loop.Region.ofAcyclic (r.mapOp h)
  | .br _ _ => rfl
  | .let1 _ _ r => by
      simp only [Loop.Region.ofAcyclic, Loop.Region.mapOp, Silmaril.SSA.LambdaRTL.Region.mapOp,
        Region.mapOp_ofAcyclic h r]
  | .let2 _ _ _ r => by
      simp only [Loop.Region.ofAcyclic, Loop.Region.mapOp, Silmaril.SSA.LambdaRTL.Region.mapOp,
        Region.mapOp_ofAcyclic h r]
  | .case _ _ r _ s => by
      simp only [Loop.Region.ofAcyclic, Loop.Region.mapOp, Silmaril.SSA.LambdaRTL.Region.mapOp,
        Region.mapOp_ofAcyclic h r, Region.mapOp_ofAcyclic h s]
  | .join r _ _ t => by
      simp only [Loop.Region.ofAcyclic, Loop.Region.mapOp, Silmaril.SSA.LambdaRTL.Region.mapOp,
        Region.mapOp_ofAcyclic h r, Region.mapOp_ofAcyclic h t]

end Silmaril.Proofs.SSA.LambdaRTL.Loop
