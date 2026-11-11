module

public import Silmaril.Wasm.FnInst.Models.Base.Defs

/-!
# Partial modules and semantic models: the basic facts

* `Sen.map_id`, `Sen.map_comp`, `Sen.holds_map` (a translated sentence holds in an environment
  iff the original holds in its restriction);
* `semSat_reduct_iff`: the satisfaction condition of the semantic models (c);
* `PMod.den_reduct`: the denotation commutes with reducts (strictly);
* `PMod.den_anti`: **monotonicity in information**: more information gives fewer
  environments; `PMod.den_bot`: the least informative model denotes every environment;
  `PMod.bot_le`, `PMod.le_refl`, `PMod.le_trans`;
* `mem_sol_update`, `sol_update_eq`: replacing the body of one function by an equivalent
  candidate (equivalent in every solution of the *other* bodies) leaves the solutions of the
  whole module unchanged; `sol_replace_of_sat`: the same from a sentence satisfied by
  `PMod.ofBodies`.

New.
-/

@[expose] public section

namespace Silmaril.Wasm.FnInst.Models

variable {L : FnSyntax}

namespace Sen

theorem map_id {n : ℕ} (φ : Sen L n) : map id φ = φ := by
  induction φ with
  | eq b b' => simp only [map, L.rename_id]
  | and φ ψ ihφ ihψ => simp only [map, ihφ, ihψ]

theorem map_comp {n m k : ℕ} (f : Fin n → Fin m) (g : Fin m → Fin k) (φ : Sen L n) :
    map (g ∘ f) φ = map g (map f φ) := by
  induction φ with
  | eq b b' => simp only [map, L.rename_comp]
  | and φ ψ ihφ ihψ => simp only [map, ihφ, ihψ]

/-- A translated sentence holds iff the original holds in the restricted environment. -/
theorem holds_map (S : FnSem L) {n m : ℕ} (f : Fin n → Fin m) (env : Env S m) (φ : Sen L n) :
    Holds S env (map f φ) ↔ Holds S (env ∘ f) φ := by
  induction φ with
  | eq b b' => simp only [map, Holds, S.eval_rename]
  | and φ ψ ihφ ihψ => simp only [map, Holds, ihφ, ihψ]

end Sen

/-- The satisfaction condition of the semantic models. -/
theorem semSat_reduct_iff (S : FnSem L) {n m : ℕ} (f : Fin n → Fin m) (E : Set (Env S m))
    (φ : Sen L n) : SemSat S E (Sen.map f φ) ↔ SemSat S (semReduct S f E) φ := by
  constructor
  · rintro h _ ⟨env, henv, rfl⟩
    exact (Sen.holds_map S f env φ).1 (h env henv)
  · intro h env henv
    exact (Sen.holds_map S f env φ).2 (h _ ⟨env, henv, rfl⟩)

theorem semReduct_id (S : FnSem L) {n : ℕ} (E : Set (Env S n)) :
    semReduct S (fun i => i) E = E := by
  simp only [semReduct]
  exact Set.image_id E

theorem semReduct_comp (S : FnSem L) {n m k : ℕ} (f : Fin n → Fin m) (g : Fin m → Fin k)
    (E : Set (Env S k)) : semReduct S (fun i => g (f i)) E = semReduct S f (semReduct S g E) := by
  simp only [semReduct, Set.image_image]
  rfl

/-- Satisfaction of semantic models is antitone: fewer environments satisfy more. -/
theorem semSat_mono (S : FnSem L) {n : ℕ} {E E' : Set (Env S n)} (h : E' ⊆ E) {φ : Sen L n}
    (hφ : SemSat S E φ) : SemSat S E' φ :=
  fun env henv => hφ env (h henv)

namespace PMod

variable {T U : Sig L}

/-- The denotation commutes with reducts. -/
theorem den_reduct (S : FnSem L) (σ : Sig.Hom T U) (M : PMod U) :
    (M.reduct σ).den S = semReduct S σ.c.f (M.den S) := by
  have hx : (σ.c.comp M.emb).f T.focus = M.emb.f U.focus := by
    show M.emb.f (σ.c.f T.focus) = M.emb.f U.focus
    rw [σ.focus]
  simp only [den, reduct, hx, semReduct, Set.image_image]
  rfl

/-- The least informative model denotes every environment. -/
theorem den_bot (S : FnSem L) (T : Sig L) : (bot T).den S = Set.univ := by
  refine Set.eq_univ_of_forall fun env => ⟨env, ?_, rfl⟩
  intro j _ b hb
  exact absurd hb (by simp [bot])

theorem le_refl (M : PMod T) : M.Le M :=
  ⟨Ctx.Hom.id _, fun _ => rfl, fun j b hb => by
    show M.bodies j = some (L.rename id b)
    rw [L.rename_id]
    exact hb⟩

theorem le_trans {M M' M'' : PMod T} (h : M.Le M') (h' : M'.Le M'') : M.Le M'' := by
  obtain ⟨κ, hκe, hκb⟩ := h
  obtain ⟨κ', hκe', hκb'⟩ := h'
  refine ⟨κ.comp κ', fun i => ?_, fun j b hb => ?_⟩
  · show κ'.f (κ.f (M.emb.f i)) = M''.emb.f i
    rw [hκe, hκe']
  · show M''.bodies (κ'.f (κ.f j)) = some (L.rename (κ'.f ∘ κ.f) b)
    rw [L.rename_comp]
    exact hκb' _ _ (hκb j b hb)

/-- The least informative model is below every model. -/
theorem bot_le (M : PMod T) : (bot T).Le M :=
  ⟨M.emb, fun _ => rfl, fun _ _ hb => absurd hb (by simp [bot])⟩

/-- **Monotonicity in information**: a model with more information denotes fewer
environments. -/
theorem den_anti (S : FnSem L) {M M' : PMod T} (h : M.Le M') : M'.den S ⊆ M.den S := by
  obtain ⟨κ, hκe, hκb⟩ := h
  rintro _ ⟨env, hsol, rfl⟩
  refine ⟨env ∘ κ.f, fun j hj b hb => ?_, ?_⟩
  · have hj' : κ.f j ∉ ({M'.emb.f T.focus} : Set _) := by
      intro hmem
      have heq : κ.f j = κ.f (M.emb.f T.focus) := by
        rw [Set.mem_singleton_iff.1 hmem, hκe]
      exact hj (Set.mem_singleton_iff.2 (κ.inj heq))
    have hbody : env (κ.f j) = S.eval env (L.rename κ.f b) := hsol _ hj' _ (hκb j b hb)
    rw [S.eval_rename] at hbody
    exact hbody
  · funext i
    show env (κ.f (M.emb.f i)) = env (M'.emb.f i)
    rw [hκe]

end PMod

/-! ### Replacing one body -/

section Replace

variable (S : FnSem L) {n : ℕ}

/-- A solution of the module with body `b` at `i` is a solution of the other bodies in which
`i` behaves as `b`. -/
theorem mem_sol_update (B : Fin n → Option (L.Body n)) (i : Fin n) (b : L.Body n)
    (env : Env S n) :
    env ∈ Sol S (Function.update B i (some b)) ∅ ↔ env ∈ Sol S B {i} ∧ env i = S.eval env b := by
  constructor
  · intro h
    refine ⟨fun j hj b' hb' => ?_, h i (Set.notMem_empty i) b (by simp)⟩
    have hji : j ≠ i := fun e => hj (Set.mem_singleton_iff.2 e)
    exact h j (Set.notMem_empty j) b' (by rw [Function.update_of_ne hji]; exact hb')
  · rintro ⟨h, hi⟩ j _ b' hb'
    by_cases hji : j = i
    · subst hji
      have hbb : b = b' := by simpa using hb'
      rw [← hbb]
      exact hi
    · exact h j (fun e => hji (Set.mem_singleton_iff.1 e)) b'
        (by rw [Function.update_of_ne hji] at hb'; exact hb')

/-- **Replacement**: candidates for the body of `i` that behave the same in every solution of
the other bodies give modules with the same solutions. -/
theorem sol_update_eq (B : Fin n → Option (L.Body n)) (i : Fin n) (b b' : L.Body n)
    (h : ∀ env ∈ Sol S B {i}, S.eval env b = S.eval env b') :
    Sol S (Function.update B i (some b)) ∅ = Sol S (Function.update B i (some b')) ∅ := by
  ext env
  rw [mem_sol_update, mem_sol_update]
  constructor
  · rintro ⟨hs, hi⟩
    exact ⟨hs, hi.trans (h env hs)⟩
  · rintro ⟨hs, hi⟩
    exact ⟨hs, hi.trans (h env hs).symm⟩

/-- The replacement theorem from a satisfied sentence: if `ofBodies B ⊨ b ≐ b'` over `T` (in the
semantic reading), then the module with `b` at the focus and the one with `b'` have the same
solutions. -/
theorem sol_replace_of_sat {T : Sig L} (B : PBodies T.toCtx) (b b' : L.Body T.n)
    (h : SemSat S ((PMod.ofBodies B).den S) (.eq b b')) :
    Sol S (Function.update B T.focus (some b)) ∅ =
      Sol S (Function.update B T.focus (some b')) ∅ :=
  sol_update_eq S B T.focus b b' fun env henv => h env ⟨env, henv, rfl⟩

end Replace

end Silmaril.Wasm.FnInst.Models
