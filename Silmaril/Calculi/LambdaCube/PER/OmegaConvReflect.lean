module

public import Silmaril.Calculi.LambdaCube.PER.OmegaChurchRosser

@[expose] public section

set_option autoImplicit true

/-! # Conversion reflection for βη-typed Fω

`conv_reflectB` (`PER/Cube.lean`) shows that β-convertible encodings of two
β-only typed (`TypedB`) Fω terms are `TmEq`. Here the same holds for the βη
typing `Typed`, whose conversion rule uses the βη-theory `ConEq`.

The generation lemmas for `Typed` need injectivity of `→` and `∀` (and their
disjointness) under `ConEq`. `Pseudo.Conv` has no η, so these do not follow from
the cube's Church–Rosser theorem. Instead (steps 1–4 are in
`PER/OmegaChurchRosser.lean`):

1. `Con.Step` is untyped one-step βη-reduction on constructors (de Bruijn; the
   η-redex is `λk. (A↑) 0`).
2. `ConEq.join` (Church–Rosser for βη): `ConEq`-equal constructors have a
   common `Con.Step`-reduct. The proof uses parallel βη-reduction `Con.Par` with
   maximal parallel reducts on kinded constructors (`Con.Par.triangle`, Selinger
   §4.4; kinding is needed for the η/β overlap), then `Relation.church_rosser`
   (`Con.confluent`).
3. `Con.Step.toConEq` (subject reduction): a `Con.Step` from a kinded
   constructor is a `ConEq` at the same kind. The η case needs strengthening
   (`Kinded.unrename_succ`).
4. `ConEq.arr_inj`, `ConEq.all_inj`, `ConEq.arr_ne_all` follow from 2 and 3,
   since `→` and `∀` are never redexes.
5. The `Typed` metatheory (`Typed.subst`, `Typed.tySubst`, `Typed.ctxConv`) and
   generation lemmas mirror the `TypedB` ones in `PER/Cube.lean`, and
   `Tm.par_reflect_typed` mirrors `Tm.par_reflect`.

Nothing in the PER soundness or parametricity results depends on this module:
`SystemFOmega.sat_sound` uses `conv_reflectB`.

Source: Selinger [selinger-2008-lecture-notes-lambda-calculus], Theorem 4.2
(p. 27) and its proof in §4.4 (pp. 31–35): parallel reduction with an η rule
(Lemma 4.6), substitution (Lemma 4.7), maximal parallel reducts (Lemma 4.8) and the
diamond property (Lemma 4.9).
-/

namespace Silmaril.Calculi.LambdaCube.PERModel.SystemFOmega

/-! ## Substitution for `ConEq` and `Typed` -/

theorem ConEq.subst (h : ConEq Δ A B k) {Δ' : KCtx} {σ : ℕ → Con}
    (hσ : ∀ n k', Δ[n]? = some k' → Kinded Δ' (σ n) k') :
    ConEq Δ' (A.subst σ) (B.subst σ) k := by
  induction h generalizing Δ' σ with
  | refl h => exact .refl (h.subst hσ)
  | symm _ ih => exact .symm (ih hσ)
  | trans _ _ ih1 ih2 => exact .trans (ih1 hσ) (ih2 hσ)
  | beta hA hB =>
    rw [Con.subst_substOne]
    exact .beta (hA.subst (ksub_lift hσ _)) (hB.subst hσ)
  | eta hA =>
    simp only [Con.subst, Con.rename_succ_subst_liftSub]
    exact .eta (hA.subst hσ)
  | arr _ _ ih1 ih2 => exact .arr (ih1 hσ) (ih2 hσ)
  | all _ ih => exact .all (ih (ksub_lift hσ _))
  | lam _ ih => exact .lam (ih (ksub_lift hσ _))
  | app _ _ ih1 ih2 => exact .app (ih1 hσ) (ih2 hσ)

/-- Pointwise `ConEq`-equal substitutions lift under a binder. -/
theorem ConEq.sub_lift {Δ Δ' : KCtx} {σ σ' : ℕ → Con}
    (hσ : ∀ n k', Δ[n]? = some k' → ConEq Δ' (σ n) (σ' n) k') (k : Kind) :
    ∀ n k', (k :: Δ)[n]? = some k' →
      ConEq (k :: Δ') (Con.liftSub σ n) (Con.liftSub σ' n) k' := by
  intro n k' h
  cases n with
  | zero => exact .refl (.var (by simpa using h))
  | succ n => exact (hσ n k' (by simpa using h)).rename (kren_succ k)

/-- Substituting pointwise `ConEq`-equal constructors into a kinded constructor. -/
theorem Kinded.subst_congr (h : Kinded Δ A k) {Δ' : KCtx} {σ σ' : ℕ → Con}
    (hσ : ∀ n k', Δ[n]? = some k' → ConEq Δ' (σ n) (σ' n) k') :
    ConEq Δ' (A.subst σ) (A.subst σ') k := by
  induction h generalizing Δ' σ σ' with
  | var h => exact hσ _ _ h
  | arr _ _ ih1 ih2 => exact .arr (ih1 hσ) (ih2 hσ)
  | all _ ih => exact .all (ih (ConEq.sub_lift hσ _))
  | lam _ ih => exact .lam (ih (ConEq.sub_lift hσ _))
  | app _ _ ih1 ih2 => exact .app (ih1 hσ) (ih2 hσ)

/-- `ConEq` is a congruence for instantiation. -/
theorem ConEq.substOne_congr (hB : ConEq (k :: Δ) B B' l) (hC : ConEq Δ C C' k) :
    ConEq Δ (B.substOne C) (B'.substOne C') l := by
  have h₁ : ConEq Δ (B.substOne C) (B'.substOne C) l :=
    hB.subst fun n k' hn => by
      cases n with
      | zero => simp at hn; subst hn; exact hC.kinded_left
      | succ n => exact .var (by simpa using hn)
  have h₂ : ConEq Δ (B'.substOne C) (B'.substOne C') l :=
    hB.kinded_right.subst_congr fun n k' hn => by
      cases n with
      | zero => simp at hn; subst hn; exact hC
      | succ n => exact .refl (.var (by simpa using hn))
  exact h₁.trans h₂

theorem Typed.subst (h : Typed Δ Γ t A) {Γ' : Ctx} {σ : ℕ → Tm}
    (hσ : ∀ n B, Γ[n]? = some B → Typed Δ Γ' (σ n) B) : Typed Δ Γ' (t.subst σ) A := by
  induction h generalizing Γ' σ with
  | var hn => exact hσ _ _ hn
  | app _ _ ih1 ih2 => exact .app (ih1 hσ) (ih2 hσ)
  | lam hA _ ih =>
    refine .lam hA (ih ?_)
    intro n B hn
    cases n with
    | zero => exact .var (by simpa using hn)
    | succ n =>
      exact (hσ n B (by simpa using hn)).rename (fun m C hm => by simpa using hm)
  | tlam _ ih =>
    refine .tlam (ih ?_)
    intro n B hn
    simp only [List.getElem?_map, Option.map_eq_some_iff] at hn
    obtain ⟨B0, hB0, rfl⟩ := hn
    exact (hσ n B0 hB0).tyRename (kren_succ _)
  | tapp _ hC ih => exact .tapp (ih hσ) hC
  | conv _ hc ih => exact .conv (ih hσ) hc

theorem Typed.substOne (ht : Typed Δ (A :: Γ) t B) (hu : Typed Δ Γ u A) :
    Typed Δ Γ (t.substOne u) B :=
  ht.subst fun n C hn => by
    cases n with
    | zero => simp at hn; subst hn; exact hu
    | succ n => exact .var (by simpa using hn)

theorem Typed.tySubst (h : Typed Δ Γ t A) {Δ' : KCtx} {σ : ℕ → Con}
    (hσ : ∀ n k', Δ[n]? = some k' → Kinded Δ' (σ n) k') :
    Typed Δ' (Γ.map (Con.subst σ)) (t.tySubst σ) (A.subst σ) := by
  induction h generalizing Δ' σ with
  | var hn => exact .var (by rw [List.getElem?_map, hn]; rfl)
  | app _ _ ih1 ih2 => exact .app (ih1 hσ) (ih2 hσ)
  | lam hA _ ih => exact .lam (hA.subst hσ) (ih hσ)
  | tlam _ ih =>
    refine .tlam ?_
    have e : ∀ Γ₀ : Ctx, (Γ₀.map (Con.rename Nat.succ)).map (Con.subst (Con.liftSub σ)) =
        (Γ₀.map (Con.subst σ)).map (Con.rename Nat.succ) := by
      intro Γ₀
      simp only [List.map_map]
      congr 1
      funext B
      exact Con.rename_succ_subst_liftSub B σ
    rw [← e]
    exact ih (ksub_lift hσ _)
  | tapp _ hC ih =>
    rw [Con.subst_substOne]
    exact .tapp (ih hσ) (hC.subst hσ)
  | conv _ hc ih => exact .conv (ih hσ) (hc.subst hσ)

theorem Typed.tySubstOne (h : Typed (k :: Δ) (Γ.map (Con.rename Nat.succ)) t A)
    (hC : Kinded Δ C k) : Typed Δ Γ (t.tySubstOne C) (A.substOne C) := by
  have := h.tySubst (σ := scons C Con.var) (Δ' := Δ) (fun n k' hn => by
    cases n with
    | zero => simp at hn; subst hn; exact hC
    | succ n => exact .var (by simpa using hn))
  rwa [List.map_map, show (Con.subst (scons C Con.var) ∘ Con.rename Nat.succ) = id from
    funext fun B => Con.rename_succ_substOne B C, List.map_id] at this

/-- Context conversion for `Typed`. -/
theorem Typed.ctxConv (h : Typed Δ Γ t A) {Γ' : Ctx}
    (hΓ : ∀ (n : ℕ) (B : Con), Γ[n]? = some B →
      ∃ B', Γ'[n]? = some B' ∧ ConEq Δ B' B .star) :
    Typed Δ Γ' t A := by
  induction h generalizing Γ' with
  | var hn =>
    obtain ⟨B', hB', q⟩ := hΓ _ _ hn
    exact .conv (.var hB') q
  | app _ _ ih1 ih2 => exact .app (ih1 hΓ) (ih2 hΓ)
  | lam hA _ ih =>
    refine .lam hA (ih ?_)
    intro n B hn
    cases n with
    | zero =>
      simp at hn
      subst hn
      exact ⟨_, rfl, .refl hA⟩
    | succ n => simpa using hΓ n B (by simpa using hn)
  | tlam _ ih =>
    refine .tlam (ih ?_)
    intro n B hn
    simp only [List.getElem?_map, Option.map_eq_some_iff] at hn
    obtain ⟨B0, hB0, rfl⟩ := hn
    obtain ⟨B', hB', q⟩ := hΓ n B0 hB0
    exact ⟨B'.rename Nat.succ, by simp [List.getElem?_map, hB'], q.rename (kren_succ _)⟩
  | tapp _ hC ih => exact .tapp (ih hΓ) hC
  | conv _ hc ih => exact .conv (ih hΓ) hc

/-! ## Generation for `Typed` -/

theorem Typed.inv_app (h : Typed Δ Γ s A) : ∀ {t u : Tm}, s = .app t u →
    (∀ B ∈ Γ, Kinded Δ B .star) →
    ∃ X Y, Typed Δ Γ t (.arr X Y) ∧ Typed Δ Γ u X ∧ ConEq Δ Y A .star := by
  induction h with
  | app h₁ h₂ _ _ =>
    intro t u e hΓ
    cases e
    cases h₁.kinded hΓ with
    | arr _ hY => exact ⟨_, _, h₁, h₂, .refl hY⟩
  | conv _ hc ih =>
    intro t u e hΓ
    obtain ⟨X, Y, h₁, h₂, q⟩ := ih e hΓ
    exact ⟨X, Y, h₁, h₂, q.trans hc⟩
  | var _ | lam _ _ _ | tlam _ _ | tapp _ _ _ => intro _ _ e; cases e

theorem Typed.inv_lam (h : Typed Δ Γ s T) : ∀ {A₀ : Con} {b : Tm}, s = .lam A₀ b →
    (∀ B ∈ Γ, Kinded Δ B .star) →
    Kinded Δ A₀ .star ∧ ∃ B, Typed Δ (A₀ :: Γ) b B ∧ ConEq Δ (.arr A₀ B) T .star := by
  induction h with
  | lam hA hb _ =>
    intro A₀ b e hΓ
    cases e
    exact ⟨hA, _, hb, .refl (.arr hA (hb.kinded (ctx_cons_kinded hA hΓ)))⟩
  | conv _ hc ih =>
    intro A₀ b e hΓ
    obtain ⟨hA, B, hb, q⟩ := ih e hΓ
    exact ⟨hA, B, hb, q.trans hc⟩
  | var _ | app _ _ _ _ | tlam _ _ | tapp _ _ _ => intro _ _ e; cases e

theorem Typed.inv_tlam (h : Typed Δ Γ s T) : ∀ {k : Kind} {b : Tm}, s = .tlam k b →
    (∀ B ∈ Γ, Kinded Δ B .star) →
    ∃ B, Typed (k :: Δ) (Γ.map (Con.rename Nat.succ)) b B ∧ ConEq Δ (.all k B) T .star := by
  induction h with
  | tlam hb _ =>
    intro k b e hΓ
    cases e
    exact ⟨_, hb, .refl (.all (hb.kinded (ctx_shift_kinded hΓ)))⟩
  | conv _ hc ih =>
    intro k b e hΓ
    obtain ⟨B, hb, q⟩ := ih e hΓ
    exact ⟨B, hb, q.trans hc⟩
  | var _ | app _ _ _ _ | lam _ _ _ | tapp _ _ _ => intro _ _ e; cases e

theorem Typed.inv_tapp (h : Typed Δ Γ s T) : ∀ {t : Tm} {C : Con}, s = .tapp t C →
    (∀ B ∈ Γ, Kinded Δ B .star) →
    ∃ k B, Typed Δ Γ t (.all k B) ∧ Kinded Δ C k ∧ ConEq Δ (B.substOne C) T .star := by
  induction h with
  | tapp ht hC _ =>
    intro t C e hΓ
    cases e
    cases ht.kinded hΓ with
    | all hB => exact ⟨_, _, ht, hC, .refl (hB.substOne hC)⟩
  | conv _ hc ih =>
    intro t C e hΓ
    obtain ⟨k, B, h₁, h₂, q⟩ := ih e hΓ
    exact ⟨k, B, h₁, h₂, q.trans hc⟩
  | var _ | app _ _ _ _ | lam _ _ _ | tlam _ _ => intro _ _ e; cases e

/-! ## Reduction of term encodings -/

/-- Parallel reduction of the encoding of a `Typed` term is typed equality and
preserves `Typed` (the βη analogue of `Tm.par_reflect`). -/
theorem Tm.par_reflect_typed {p v : Pseudo CubeSort} (h : Pseudo.Par p v) :
    ∀ (t : Tm) (L : Layout) (Δ : KCtx) (Γ : Ctx) (A : Con), t.toPseudo L = p →
    Typed Δ Γ t A → (∀ B ∈ Γ, Kinded Δ B .star) →
    ∃ t' : Tm, t'.toPseudo L = v ∧ TmEq Δ Γ t t' A ∧ Typed Δ Γ t' A := by
  induction h with
  | sort s => intro t L Δ Γ A e _ _; exact absurd e (Tm.toPseudo_ne_sort t L s)
  | var n => intro t L Δ Γ A e ht _; exact ⟨t, e, .refl ht, ht⟩
  | pi _ _ _ _ => intro t L Δ Γ A e _ _; cases t <;> simp [Tm.toPseudo] at e
  | app _ ha ih₁ ih₂ =>
    intro t L Δ Γ A e ht hΓ
    cases t with
    | app t₁ t₂ =>
      injection e with e₁ e₂
      obtain ⟨X, Y, h₁, h₂, q⟩ := ht.inv_app rfl hΓ
      obtain ⟨t₁', r₁, q₁, k₁⟩ := ih₁ t₁ L Δ Γ _ e₁ h₁ hΓ
      obtain ⟨t₂', r₂, q₂, k₂⟩ := ih₂ t₂ L Δ Γ _ e₂ h₂ hΓ
      exact ⟨.app t₁' t₂', by subst r₁ r₂; rfl, .conv (.app q₁ q₂) q,
        .conv (.app k₁ k₂) q⟩
    | tapp t₁ C =>
      injection e with e₁ e₂
      obtain ⟨k, B, h₁, hC, q⟩ := ht.inv_tapp rfl hΓ
      have hB : Kinded (k :: Δ) B .star := by
        cases h₁.kinded hΓ with
        | all hB => exact hB
      obtain ⟨t₁', r₁, q₁, k₁⟩ := ih₁ t₁ L Δ Γ _ e₁ h₁ hΓ
      obtain ⟨C', r₂, qC⟩ := Con.par_reflect ha C L Δ k e₂ hC
      refine ⟨.tapp t₁' C', by subst r₁ r₂; rfl, ?_, ?_⟩
      · exact .conv ((TmEq.tapp q₁ hC).trans (.tappConv k₁ qC.toConEq)) q
      · exact .conv (.tapp k₁ qC.kinded_right)
          ((ConEq.substOne_congr (.refl hB) qC.toConEq.symm).trans q)
    | var _ | lam _ _ | tlam _ _ => simp [Tm.toPseudo] at e
  | lam hX _ _ ihb =>
    intro t L Δ Γ A e ht hΓ
    cases t with
    | lam A₀ b₀ =>
      injection e with e₁ e₂
      obtain ⟨hA₀, B, hb₀, q⟩ := ht.inv_lam rfl hΓ
      obtain ⟨A₀', r₁, qA⟩ := Con.par_reflect hX A₀ L Δ .star e₁ hA₀
      obtain ⟨b₀', r₂, qb, kb⟩ :=
        ihb b₀ (false :: L) Δ (A₀ :: Γ) B e₂ hb₀ (ctx_cons_kinded hA₀ hΓ)
      have hB : Kinded Δ B .star := hb₀.kinded (ctx_cons_kinded hA₀ hΓ)
      have kb' : Typed Δ (A₀' :: Γ) b₀' B := kb.ctxConv (fun n C hn => by
        cases n with
        | zero =>
          simp at hn
          subst hn
          exact ⟨A₀', rfl, qA.toConEq.symm⟩
        | succ n =>
          exact ⟨C, by simpa using hn,
            .refl (hΓ C (List.mem_iff_getElem?.mpr ⟨n, by simpa using hn⟩))⟩)
      refine ⟨.lam A₀' b₀', by subst r₁ r₂; rfl, ?_, ?_⟩
      · exact .conv ((TmEq.lam hA₀ qb).trans
          (TmEq.lamConv hA₀ qA.kinded_right qA.toConEq kb' hB)) q
      · exact .conv (.conv (.lam qA.kinded_right kb') (.arr qA.toConEq.symm (.refl hB))) q
    | tlam k b₀ =>
      injection e with e₁ e₂
      subst e₁
      have e₃ := hX.eq_of_noRedex (Kind.noRedex_toPseudo k)
      subst e₃
      obtain ⟨B, hb₀, q⟩ := ht.inv_tlam rfl hΓ
      obtain ⟨b₀', r₂, qb, kb⟩ :=
        ihb b₀ (true :: L) (k :: Δ) _ B e₂ hb₀ (ctx_shift_kinded hΓ)
      exact ⟨.tlam k b₀', by subst r₂; rfl, .conv (.tlam qb) q, .conv (.tlam kb) q⟩
    | var _ | app _ _ | tapp _ _ => simp [Tm.toPseudo] at e
  | beta _ _ ha ihb iha =>
    intro t L Δ Γ A e ht hΓ
    cases t with
    | app t₁ t₂ =>
      injection e with e₁ e₂
      obtain ⟨X₁, Y₁, h₁, h₂, q⟩ := ht.inv_app rfl hΓ
      cases t₁ with
      | lam A₀ b₀ =>
        injection e₁ with e₃ e₄
        obtain ⟨hA₀, B, hb₀, q₁⟩ := h₁.inv_lam rfl hΓ
        obtain ⟨qX, qY⟩ := q₁.arr_inj
        obtain ⟨b₀', r₁, qb, kb⟩ :=
          ihb b₀ (false :: L) Δ (A₀ :: Γ) B e₄ hb₀ (ctx_cons_kinded hA₀ hΓ)
        obtain ⟨t₂', r₂, q₂, k₂⟩ := iha t₂ L Δ Γ X₁ e₂ h₂ hΓ
        subst r₁ r₂
        refine ⟨b₀'.substOne t₂', Tm.toPseudo_substOne _ _ _, ?_, ?_⟩
        · exact .conv ((TmEq.app (.conv (.lam hA₀ qb) q₁) q₂).trans
            (.conv (.beta hA₀ kb (.conv k₂ qX.symm)) qY)) q
        · exact .conv (.conv (kb.substOne (.conv k₂ qX.symm)) qY) q
      | tlam k b₀ =>
        obtain ⟨B, _, q₁⟩ := h₁.inv_tlam rfl hΓ
        exact q₁.symm.arr_ne_all.elim
      | var _ | app _ _ | tapp _ _ => simp [Tm.toPseudo] at e₁
    | tapp t₁ C =>
      injection e with e₁ e₂
      obtain ⟨k, B, h₁, hC, q⟩ := ht.inv_tapp rfl hΓ
      cases t₁ with
      | tlam k₀ b₀ =>
        injection e₁ with e₃ e₄
        obtain ⟨B', hb₀, q₁⟩ := h₁.inv_tlam rfl hΓ
        obtain ⟨rfl, qB⟩ := q₁.all_inj
        obtain ⟨b₀', r₁, qb, kb⟩ := ihb b₀ (true :: L) _ _ B' e₄ hb₀ (ctx_shift_kinded hΓ)
        obtain ⟨C', r₂, qC⟩ := Con.par_reflect ha C L Δ _ e₂ hC
        subst r₁ r₂
        refine ⟨b₀'.tySubstOne C', Tm.toPseudo_tySubstOne _ _ _, ?_, ?_⟩
        · exact .conv ((((TmEq.tapp (.conv (.tlam qb) (ConEq.all qB)) hC).trans
            (.tappConv (.conv (.tlam kb) (ConEq.all qB)) qC.toConEq)).trans
            (.conv (.tbeta kb qC.kinded_right)
              (ConEq.substOne_congr qB qC.toConEq.symm)))) q
        · exact .conv (.conv (kb.tySubstOne qC.kinded_right)
            (ConEq.substOne_congr qB qC.toConEq.symm)) q
      | lam A₀ b₀ =>
        obtain ⟨_, B', _, q₁⟩ := h₁.inv_lam rfl hΓ
        exact q₁.arr_ne_all.elim
      | var _ | app _ _ | tapp _ _ => simp [Tm.toPseudo] at e₁
    | var _ | lam _ _ | tlam _ _ => simp [Tm.toPseudo] at e

theorem Tm.reflTransGen_par_reflect_typed {L : Layout} {t : Tm} {v : Pseudo CubeSort}
    {Δ : KCtx} {Γ : Ctx} {A : Con} (h : Relation.ReflTransGen Pseudo.Par (t.toPseudo L) v)
    (ht : Typed Δ Γ t A) (hΓ : ∀ B ∈ Γ, Kinded Δ B .star) :
    ∃ t' : Tm, t'.toPseudo L = v ∧ TmEq Δ Γ t t' A ∧ Typed Δ Γ t' A := by
  induction h with
  | refl => exact ⟨t, rfl, .refl ht, ht⟩
  | tail _ hp ih =>
    obtain ⟨t', rfl, q, kt⟩ := ih
    obtain ⟨t'', r, q', kt'⟩ := Tm.par_reflect_typed hp t' L Δ Γ A rfl kt hΓ
    exact ⟨t'', r, q.trans q', kt'⟩

/-- Untyped β-conversion between encodings of typed Fω terms is typed equality.
This relies on `TmEq.tappConv`: `Pseudo.Conv` reduces inside type arguments,
e.g. `x C` and `x ((λα. α) C)`. -/
theorem conv_reflect {T : Tele} (hT : T.WF) (ht : Typed T.kctx T.ctx t A)
    (hu : Typed T.kctx T.ctx u A)
    (h : Pseudo.Conv (t.toPseudo T.layout) (u.toPseudo T.layout)) :
    TmEq T.kctx T.ctx t u A := by
  obtain ⟨v, h₁, h₂⟩ := h.join
  obtain ⟨t', r₁, q₁, k₁⟩ := Tm.reflTransGen_par_reflect_typed h₁ ht hT.ctx_kinded
  obtain ⟨u', r₂, q₂, k₂⟩ := Tm.reflTransGen_par_reflect_typed h₂ hu hT.ctx_kinded
  have e : t' = u' := Tm.toPseudo_inj_bnd t' u' _
    (fun m hm => by rw [← Tele.kctx_length]; exact k₁.bounded m hm)
    (fun m hm => by rw [← Tele.kctx_length]; exact k₂.bounded m hm) (r₁.trans r₂.symm)
  subst e
  exact q₁.trans q₂.symm

end Silmaril.Calculi.LambdaCube.PERModel.SystemFOmega
