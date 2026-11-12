module

public import Silmaril.SSA.LambdaRTL.CFG.Defs
import Silmaril.Proofs.SSA.LambdaRTL.Agreement

/-!
# Flat CFG for λRTL: correctness of `toRegion`, `flatten`, relabelling and the validator (proofs)

Restated in `Silmaril.SSA.LambdaRTL.CFG.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.CFG

open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.CFG

universe v w

section Upd

variable {V : Type w} {α : Type w} [DecidableEq V]

theorem upd_self (σ : V → α) (x : V) (a : α) : upd σ x a x = a := by
  simp [upd]

theorem upd_upd_same (σ : V → α) (x : V) (a b : α) : upd (upd σ x a) x b = upd σ x b := by
  funext y; by_cases h : y = x <;> simp [upd, h]

end Upd

/-! ## Execution as region evaluation, generic in the continuation -/

section Exec

variable {V K K' : Type w} {F : Type v} {M : Type w → Type w} {α : Type w} [Monad M]
  [DecidableEq V]

theorem Term.exec_relabel (m : Model F M α) {R : Type w} (π : K → K')
    (j : K' → α → (V → α) → M R) :
    ∀ (τ : Term V K F) (σ : V → α), (τ.relabel π).exec m j σ = τ.exec m (fun k => j (π k)) σ
  | .br _ _, _ => rfl
  | .case o x t y u, σ => by
      simp only [Term.relabel, Term.exec]
      congr 1; funext s
      cases s with
      | inl a => exact Term.exec_relabel m π j t _
      | inr b => exact Term.exec_relabel m π j u _

theorem Body.exec_relabel (m : Model F M α) {R : Type w} (π : K → K')
    (j : K' → α → (V → α) → M R) :
    ∀ (β : Body V K F) (σ : V → α), (β.relabel π).exec m j σ = β.exec m (fun k => j (π k)) σ
  | .let1 x o β, σ => by
      simp only [Body.relabel, Body.exec]
      congr 1; funext a; exact Body.exec_relabel m π j β _
  | .let2 x y o β, σ => by
      simp only [Body.relabel, Body.exec]
      congr 1; funext p; exact Body.exec_relabel m π j β _
  | .term τ, σ => Term.exec_relabel m π j τ σ

theorem Term.exec_congr (m : Model F M α) {R : Type w} {j₁ j₂ : K → α → (V → α) → M R} :
    ∀ (τ : Term V K F) (σ : V → α), (∀ k ∈ τ.targets, j₁ k = j₂ k) →
      τ.exec m j₁ σ = τ.exec m j₂ σ
  | .br k a, σ, h => by
      simp only [Term.exec, h k (by simp [Term.targets])]
  | .case o x t y u, σ, h => by
      simp only [Term.exec]
      congr 1; funext s
      cases s with
      | inl a => exact Term.exec_congr m t _ fun k hk => h k (by simp [Term.targets, hk])
      | inr b => exact Term.exec_congr m u _ fun k hk => h k (by simp [Term.targets, hk])

theorem Body.exec_congr (m : Model F M α) {R : Type w} {j₁ j₂ : K → α → (V → α) → M R} :
    ∀ (β : Body V K F) (σ : V → α), (∀ k ∈ β.targets, j₁ k = j₂ k) →
      β.exec m j₁ σ = β.exec m j₂ σ
  | .let1 x o β, σ, h => by
      simp only [Body.exec]
      congr 1; funext a; exact Body.exec_congr m β _ fun k hk => h k (by simpa [Body.targets])
  | .let2 x y o β, σ, h => by
      simp only [Body.exec]
      congr 1; funext p; exact Body.exec_congr m β _ fun k hk => h k (by simpa [Body.targets])
  | .term τ, σ, h => Term.exec_congr m τ σ fun k hk => h k (by simpa [Body.targets])

variable [LawfulMonad M]

theorem Term.exec_map (m : Model F M α) {R R' : Type w} (f : R → R')
    (j : K → α → (V → α) → M R) :
    ∀ (τ : Term V K F) (σ : V → α),
      τ.exec m (fun k a σ' => f <$> j k a σ') σ = f <$> τ.exec m j σ
  | .br _ _, _ => rfl
  | .case o x t y u, σ => by
      simp only [Term.exec, map_bind]
      congr 1; funext s
      cases s with
      | inl a => exact Term.exec_map m f j t _
      | inr b => exact Term.exec_map m f j u _

theorem Body.exec_map (m : Model F M α) {R R' : Type w} (f : R → R')
    (j : K → α → (V → α) → M R) :
    ∀ (β : Body V K F) (σ : V → α),
      β.exec m (fun k a σ' => f <$> j k a σ') σ = f <$> β.exec m j σ
  | .let1 x o β, σ => by
      simp only [Body.exec, map_bind]
      congr 1; funext a; exact Body.exec_map m f j β _
  | .let2 x y o β, σ => by
      simp only [Body.exec, map_bind]
      congr 1; funext p; exact Body.exec_map m f j β _
  | .term τ, σ => Term.exec_map m f j τ σ

variable [DecidableEq K]

/-- A terminator executes as its region, followed by the continuation on the exit. -/
theorem Term.exec_eq (m : Model F M α) {R : Type w} (j : K → α → (V → α) → M R) :
    ∀ (τ : Term V K F) (σ : V → α),
      τ.exec m j σ = τ.toRegion.evalRTL m σ >>= fun e => j e.1 e.2.1 e.2.2
  | .br k a, σ => by simp [Term.exec, Term.toRegion, Region.evalRTL]
  | .case o x t y u, σ => by
      simp only [Term.exec, Term.toRegion, Region.evalRTL, bind_assoc]
      congr 1; funext v; congr 1; funext s
      cases s with
      | inl a => exact Term.exec_eq m j t _
      | inr b => exact Term.exec_eq m j u _

/-- A body executes as its region, followed by the continuation on the exit. -/
theorem Body.exec_eq (m : Model F M α) {R : Type w} (j : K → α → (V → α) → M R) :
    ∀ (β : Body V K F) (σ : V → α),
      β.exec m j σ = β.toRegion.evalRTL m σ >>= fun e => j e.1 e.2.1 e.2.2
  | .let1 x o β, σ => by
      simp only [Body.exec, Body.toRegion, Region.evalRTL, bind_assoc]
      congr 1; funext a; exact Body.exec_eq m j β _
  | .let2 x y o β, σ => by
      simp only [Body.exec, Body.toRegion, Region.evalRTL, bind_assoc]
      congr 1; funext v; congr 1; funext p; exact Body.exec_eq m j β _
  | .term τ, σ => Term.exec_eq m j τ σ

end Exec

/-! ## `jump` -/

section Jump

variable {V K K' : Type w} {F : Type v} {M : Type w → Type w} {α : Type w} [Monad M]
  [DecidableEq V] [DecidableEq K]

theorem jump_nil (m : Model F M α) (k : K) (a : α) (σ : V → α) :
    jump m ([] : List (K × Block V K F)) k a σ = pure (k, a, σ) := rfl

theorem jump_cons_self (m : Model F M α) (k : K) (b : Block V K F) (bs : List (K × Block V K F))
    (a : α) (σ : V → α) :
    jump m ((k, b) :: bs) k a σ = b.body.exec m (jump m bs) (upd σ b.param a) := by
  simp [jump]

theorem jump_cons_ne (m : Model F M α) {k k' : K} (h : k ≠ k') (b : Block V K F)
    (bs : List (K × Block V K F)) (a : α) (σ : V → α) :
    jump m ((k', b) :: bs) k a σ = jump m bs k a σ := by
  simp [jump, h]

theorem jump_append_of_ne (m : Model F M α) {k : K} :
    ∀ (bs : List (K × Block V K F)), (∀ kb ∈ bs, kb.1 ≠ k) →
      ∀ (rest : List (K × Block V K F)) (a : α) (σ : V → α),
        jump m (bs ++ rest) k a σ = jump m rest k a σ
  | [], _, _, _, _ => rfl
  | kb :: bs, h, rest, a, σ => by
      rw [List.cons_append, ← Prod.mk.eta (p := kb),
        jump_cons_ne m (fun he => h kb (by simp) he.symm)]
      exact jump_append_of_ne m bs (fun kb' hkb' => h kb' (by simp [hkb'])) rest a σ

variable [LawfulMonad M]

/-- **Relabelling** commutes with `jump`, given injectivity on the labels in play. -/
theorem jump_relabel (m : Model F M α) (π : K → K') [DecidableEq K'] (S : List K)
    (hinj : ∀ a ∈ S, ∀ b ∈ S, π a = π b → a = b) :
    ∀ (bs : List (K × Block V K F)), (∀ k ∈ blockLabels bs, k ∈ S) →
      ∀ (k : K) (a : α) (σ : V → α), k ∈ S →
        jump m (bs.map fun kb => (π kb.1, kb.2.relabel π)) (π k) a σ =
          (fun e => (π e.1, e.2)) <$> jump m bs k a σ
  | [], _, k, a, σ, _ => by simp [jump]
  | kb :: bs, hS, k, a, σ, hk => by
      have hS' : ∀ k ∈ blockLabels bs, k ∈ S := fun k hk' => hS k (by
        simp only [blockLabels, List.flatMap_cons, List.mem_append] at hk' ⊢
        exact Or.inr hk')
      have hkb : kb.1 ∈ S := hS kb.1 (by simp [blockLabels])
      have ht : ∀ t ∈ kb.2.body.targets, t ∈ S := fun t ht => hS t (by
        simp only [blockLabels, List.flatMap_cons, List.mem_append, List.mem_cons]
        exact Or.inl (Or.inr ht))
      by_cases h : k = kb.1
      · subst h
        rw [List.map_cons, ← Prod.mk.eta (p := kb), jump_cons_self, jump_cons_self]
        simp only [Block.relabel]
        rw [Body.exec_relabel, ← Body.exec_map]
        apply Body.exec_congr
        intro t htt
        funext a' σ'
        exact jump_relabel m π S hinj bs hS' t a' σ' (ht t htt)
      · rw [List.map_cons, ← Prod.mk.eta (p := kb), jump_cons_ne m h,
          jump_cons_ne m (fun h' => h (hinj _ hk _ hkb h'))]
        exact jump_relabel m π S hinj bs hS' k a σ hk

end Jump

/-! ## `toRegion` -/

section ToRegion

variable {V K : Type w} {F : Type v} {M : Type w → Type w} {α : Type w} [Monad M]
  [LawfulMonad M] [DecidableEq V] [DecidableEq K]

theorem joinAll_evalRTL (m : Model F M α) :
    ∀ (bs : List (K × Block V K F)) (r : Region V K F) (σ : V → α),
      (joinAll r bs).evalRTL m σ = r.evalRTL m σ >>= fun e => jump m bs e.1 e.2.1 e.2.2
  | [], r, σ => by simp [joinAll, jump]
  | kb :: bs, r, σ => by
      simp only [joinAll]
      rw [joinAll_evalRTL m bs]
      simp only [Region.evalRTL, bind_assoc]
      congr 1; funext e
      simp only [jump]
      split_ifs with h
      · rw [Body.exec_eq]
      · rw [pure_bind]

/-- A forward CFG runs as its reading as a λRTL region. -/
theorem run_eq_toRegion (m : Model F M α) (g : CFG V K F) (σ : V → α) :
    g.run m σ = g.toRegion.evalRTL m σ := by
  simp only [CFG.run, CFG.toRegion]
  rw [joinAll_evalRTL, Body.exec_eq]

theorem run_relabel {K' : Type w} [DecidableEq K'] (m : Model F M α) (π : K → K')
    (g : CFG V K F) (hinj : ∀ a ∈ g.labels, ∀ b ∈ g.labels, π a = π b → a = b)
    (σ : V → α) :
    (g.relabel π).run m σ = (fun e => (π e.1, e.2)) <$> g.run m σ := by
  simp only [CFG.run, CFG.relabel]
  rw [Body.exec_relabel, ← Body.exec_map]
  apply Body.exec_congr
  intro t ht
  funext a σ'
  exact jump_relabel m π g.labels hinj g.blocks
    (fun k hk => by simp [CFG.labels, hk]) t a σ' (by simp [CFG.labels, ht])

end ToRegion

/-! ## Flattening -/

section Flatten

variable {V L : Type w} {F : Type v}

/-- `q` strictly extends the path `p`. -/
def SE (p q : Path) : Prop := ∃ (c : Bool) (s : Path), q = p ++ c :: s

theorem SE.length_lt {p q : Path} : SE p q → p.length < q.length := by
  rintro ⟨c, s, rfl⟩; simp

theorem SE.snoc (p : Path) (c : Bool) : SE p (p ++ [c]) := ⟨c, [], rfl⟩

theorem SE.of_snoc {p q : Path} {c : Bool} : SE (p ++ [c]) q → SE p q := by
  rintro ⟨d, s, rfl⟩; exact ⟨c, d :: s, by simp⟩

/-- All block labels of `bs` are paths strictly extending `p`. -/
def LabelsSE (p : Path) (bs : List ((L ⊕ Path) × Block V (L ⊕ Path) F)) : Prop :=
  ∀ kb ∈ bs, ∃ q, kb.1 = .inr q ∧ SE p q

theorem LabelsSE.of_snoc {p : Path} {c : Bool} {bs : List ((L ⊕ Path) × Block V (L ⊕ Path) F)}
    (h : LabelsSE (p ++ [c]) bs) : LabelsSE p bs := fun kb hkb => by
  obtain ⟨q, hq, hse⟩ := h kb hkb; exact ⟨q, hq, hse.of_snoc⟩

theorem LabelsSE.cons_snoc {p : Path} {c : Bool} (b : Block V (L ⊕ Path) F)
    {bs : List ((L ⊕ Path) × Block V (L ⊕ Path) F)} (h : LabelsSE (p ++ [c]) bs) :
    LabelsSE p ((.inr (p ++ [c]), b) :: bs) := by
  intro kb hkb
  rcases List.mem_cons.1 hkb with rfl | hkb
  · exact ⟨_, rfl, SE.snoc p c⟩
  · exact h.of_snoc kb hkb

variable [DecidableEq L]

theorem blocks_labelsSE : ∀ (r : Region V L F) (env : L → Option Path) (p : Path),
    LabelsSE p (r.blocks env p)
  | .br _ _, _, _ => by simp [LabelsSE, Region.blocks]
  | .let1 _ _ r, env, p => blocks_labelsSE r env p
  | .let2 _ _ _ r, env, p => blocks_labelsSE r env p
  | .case _ x r y s, env, p => by
      intro kb hkb
      simp only [Region.blocks, List.mem_cons, List.mem_append] at hkb
      rcases hkb with (rfl | hkb) | rfl | hkb
      · exact ⟨_, rfl, SE.snoc p false⟩
      · exact (blocks_labelsSE r env _).of_snoc kb hkb
      · exact ⟨_, rfl, SE.snoc p true⟩
      · exact (blocks_labelsSE s env _).of_snoc kb hkb
  | .join r ℓ x t, env, p => by
      intro kb hkb
      simp only [Region.blocks, List.mem_cons, List.mem_append] at hkb
      rcases hkb with hkb | rfl | hkb
      · exact (blocks_labelsSE r _ _).of_snoc kb hkb
      · exact ⟨_, rfl, SE.snoc p true⟩
      · exact (blocks_labelsSE t env _).of_snoc kb hkb

/-- The environment of a subtree at `p` only points outside the subtree. -/
def EnvOK (env : L → Option Path) (p : Path) : Prop := ∀ ℓ q, env ℓ = some q → ¬ SE p q

omit [DecidableEq L] in
theorem EnvOK.snoc {env : L → Option Path} {p : Path} (h : EnvOK env p) (c : Bool) :
    EnvOK env (p ++ [c]) := fun ℓ q he hse => h ℓ q he hse.of_snoc

theorem EnvOK.bindLabel {env : L → Option Path} {p : Path} (h : EnvOK env p) (ℓ : L) :
    EnvOK (bindLabel env ℓ (p ++ [true])) (p ++ [false]) := by
  intro l q he hse
  simp only [CFG.bindLabel] at he
  split_ifs at he with hl
  · cases he
    have := hse.length_lt
    simp at this
  · exact h l q he hse.of_snoc

omit [DecidableEq L] in
theorem res_ne {env : L → Option Path} {p : Path} (h : EnvOK env p)
    {bs : List ((L ⊕ Path) × Block V (L ⊕ Path) F)} (hbs : LabelsSE p bs) (ℓ : L) :
    ∀ kb ∈ bs, kb.1 ≠ res env ℓ := by
  intro kb hkb heq
  obtain ⟨q, hq, hse⟩ := hbs kb hkb
  rw [hq] at heq
  cases he : env ℓ with
  | none => simp [res, he] at heq
  | some q' =>
      simp only [res, he, Sum.inr.injEq] at heq
      subst heq
      exact h ℓ q he hse

variable {M : Type w → Type w} {α : Type w} [Monad M] [LawfulMonad M] [DecidableEq V]

/-- **Flattening is correct**, relative to any tail of blocks `rest` that the subtree's exits
are resolved in. -/
theorem exec_flat (m : Model F M α) :
    ∀ (r : Region V L F) (env : L → Option Path) (p : Path)
      (rest : List ((L ⊕ Path) × Block V (L ⊕ Path) F)) (σ : V → α), EnvOK env p →
      (r.entryBody env p).exec m (jump m (r.blocks env p ++ rest)) σ =
        r.evalRTL m σ >>= fun e => jump m rest (res env e.1) e.2.1 e.2.2
  | .br ℓ a, env, p, rest, σ, _ => by
      simp [Region.entryBody, Region.blocks, Body.exec, Term.exec, Region.evalRTL]
  | .let1 x o r, env, p, rest, σ, henv => by
      simp only [Region.entryBody, Region.blocks, Body.exec, Region.evalRTL, bind_assoc]
      congr 1; funext a; exact exec_flat m r env p rest _ henv
  | .let2 x y o r, env, p, rest, σ, henv => by
      simp only [Region.entryBody, Region.blocks, Body.exec, Region.evalRTL, bind_assoc]
      congr 1; funext v; congr 1; funext q; exact exec_flat m r env p rest _ henv
  | .case o x r y s, env, p, rest, σ, henv => by
      have hL0 := blocks_labelsSE r env (p ++ [false])
      have hL1 := blocks_labelsSE s env (p ++ [true])
      simp only [Region.entryBody, Region.blocks, Body.exec, Term.exec, Region.evalRTL, bind_assoc,
        List.cons_append, List.append_assoc]
      congr 1; funext v; congr 1; funext sm
      cases sm with
      | inl a =>
          change jump m _ (Sum.inr (p ++ [false]) : L ⊕ Path) ((Val.var x).eval m (upd σ x a)) (upd σ x a) =
            r.evalRTL m (upd σ x a) >>= _
          rw [jump_cons_self]
          simp only [Val.eval, upd_self, upd_upd_same]
          rw [exec_flat m r env (p ++ [false]) _ _ (henv.snoc false)]
          congr 1; funext e
          rw [← List.cons_append]
          exact jump_append_of_ne m _ (res_ne henv (hL1.cons_snoc _) e.1) rest _ _
      | inr b =>
          change jump m _ (Sum.inr (p ++ [true]) : L ⊕ Path) ((Val.var y).eval m (upd σ y b)) (upd σ y b) =
            s.evalRTL m (upd σ y b) >>= _
          rw [jump_cons_ne m (by simp), jump_append_of_ne m _ ?_, jump_cons_self]
          · simp only [Val.eval, upd_self, upd_upd_same]
            exact exec_flat m s env (p ++ [true]) rest _ (henv.snoc true)
          · intro kb hkb heq
            obtain ⟨q, hq, hse⟩ := hL0 kb hkb
            rw [hq, Sum.inr.injEq] at heq
            subst heq
            have := hse.length_lt
            simp at this
  | .join r ℓ x t, env, p, rest, σ, henv => by
      have hL1 := blocks_labelsSE t env (p ++ [true])
      simp only [Region.entryBody, Region.blocks, Region.evalRTL, bind_assoc, List.cons_append,
        List.append_assoc]
      rw [exec_flat m r _ (p ++ [false]) _ σ (henv.bindLabel ℓ)]
      congr 1; funext e
      by_cases he : e.1 = ℓ
      · have hres : res (bindLabel env ℓ (p ++ [true])) e.1 = Sum.inr (p ++ [true]) := by
          simp [res, CFG.bindLabel, he]
        rw [hres, jump_cons_self]
        simp only [he, ↓reduceIte]
        exact exec_flat m t env (p ++ [true]) rest _ (henv.snoc true)
      · have hres : res (bindLabel env ℓ (p ++ [true])) e.1 = res env e.1 := by
          simp [res, CFG.bindLabel, he]
        simp only [hres, he, ↓reduceIte, pure_bind]
        rw [← List.cons_append]
        exact jump_append_of_ne m _ (res_ne henv (hL1.cons_snoc _) e.1) rest _ _

/-- **Flattening theorem**: the flat CFG runs exactly as the λRTL region, with free labels
embedded as exits. -/
theorem run_flatten (m : Model F M α) (r : Region V L F) (σ : V → α) :
    (flatten r).run m σ = (fun e => (Sum.inl e.1, e.2)) <$> r.evalRTL m σ := by
  have h := exec_flat m r (fun _ => none) [] [] σ (fun _ _ he => by cases he)
  simp only [List.append_nil] at h
  simp only [CFG.run, flatten, h, jump, res, bind_pure_comp]

end Flatten

/-! ## Region label renaming -/

section MapLabel

variable {V L K : Type w} {F : Type v} {M : Type w → Type w} {α : Type w} [Monad M]
  [LawfulMonad M] [DecidableEq V] [DecidableEq L] [DecidableEq K]

theorem evalRTL_mapLabel (m : Model F M α) {f : L → K} (hf : Function.Injective f) :
    ∀ (r : Region V L F) (σ : V → α),
      (r.mapLabel f).evalRTL m σ = (fun e => (f e.1, e.2)) <$> r.evalRTL m σ
  | .br ℓ a, σ => by simp [Region.mapLabel, Region.evalRTL]
  | .let1 x o r, σ => by
      simp only [Region.mapLabel, Region.evalRTL, map_bind]
      congr 1; funext a; exact evalRTL_mapLabel m hf r _
  | .let2 x y o r, σ => by
      simp only [Region.mapLabel, Region.evalRTL, map_bind]
      congr 1; funext p; exact evalRTL_mapLabel m hf r _
  | .case o x r y s, σ => by
      simp only [Region.mapLabel, Region.evalRTL, map_bind]
      congr 1; funext sm
      cases sm with
      | inl a => exact evalRTL_mapLabel m hf r _
      | inr b => exact evalRTL_mapLabel m hf s _
  | .join r ℓ x t, σ => by
      simp only [Region.mapLabel, Region.evalRTL, map_bind]
      rw [evalRTL_mapLabel m hf r, bind_map_left]
      congr 1; funext e
      simp only [hf.eq_iff]
      split_ifs
      · exact evalRTL_mapLabel m hf t _
      · simp

end MapLabel

/-! ## The validator -/

section Validate

variable {V L K : Type w} {F : Type v} {M : Type w → Type w} {α : Type w} [Monad M]
  [LawfulMonad M] [DecidableEq V] [DecidableEq L] [DecidableEq K] [DecidableEq F] [Inhabited K]

/-- **Soundness of the validator.** -/
theorem run_of_validate (m : Model F M α) (exit : L → K) (r : Region V L F) (g : CFG V K F)
    (h : validate exit r g = true) (σ : V → α) :
    g.run m σ = (fun e => (exit e.1, e.2)) <$> r.evalRTL m σ := by
  simp only [validate, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at h
  obtain ⟨hg, hinj⟩ := h
  rw [hg, run_relabel m _ _ hinj, run_flatten, Functor.map_map]
  rfl

end Validate

/-! ## Instruction renaming -/

section MapOp

variable {V K : Type w} {F F' F'' : Type v}

theorem Term.toRegion_mapOp (h : F → F') :
    ∀ (τ : Term V K F), (τ.mapOp h).toRegion = τ.toRegion.mapOp h
  | .br _ _ => rfl
  | .case o x t y u => by
      simp only [Term.mapOp, Term.toRegion, Region.mapOp, Term.toRegion_mapOp h t,
        Term.toRegion_mapOp h u]

theorem Body.toRegion_mapOp (h : F → F') :
    ∀ (β : Body V K F), (β.mapOp h).toRegion = β.toRegion.mapOp h
  | .let1 x o β => by simp only [Body.mapOp, Body.toRegion, Region.mapOp, Body.toRegion_mapOp h β]
  | .let2 x y o β => by
      simp only [Body.mapOp, Body.toRegion, Region.mapOp, Body.toRegion_mapOp h β]
  | .term τ => Term.toRegion_mapOp h τ

theorem joinAll_mapOp (h : F → F') :
    ∀ (bs : List (K × Block V K F)) (r : Region V K F),
      joinAll (r.mapOp h) (bs.map fun kb => (kb.1, kb.2.mapOp h)) = (joinAll r bs).mapOp h
  | [], _ => rfl
  | kb :: bs, r => by
      simp only [List.map_cons, joinAll, Block.mapOp, Body.toRegion_mapOp]
      exact joinAll_mapOp h bs (.join r kb.1 kb.2.param kb.2.body.toRegion)

theorem toRegion_mapOp (h : F → F') (g : CFG V K F) :
    (g.mapOp h).toRegion = g.toRegion.mapOp h := by
  simp only [CFG.toRegion, CFG.mapOp, Body.toRegion_mapOp, joinAll_mapOp]

theorem Term.mapOp_id : ∀ (τ : Term V K F), τ.mapOp id = τ
  | .br _ _ => rfl
  | .case o x t y u => by
      simp only [Term.mapOp, Op.mapOp_id, Term.mapOp_id t, Term.mapOp_id u]

theorem Body.mapOp_id : ∀ (β : Body V K F), β.mapOp id = β
  | .let1 x o β => by simp only [Body.mapOp, Op.mapOp_id, Body.mapOp_id β]
  | .let2 x y o β => by simp only [Body.mapOp, Op.mapOp_id, Body.mapOp_id β]
  | .term τ => by simp only [Body.mapOp, Term.mapOp_id τ]

theorem mapOp_id (g : CFG V K F) : g.mapOp id = g := by
  cases g with
  | mk entry blocks =>
      simp only [CFG.mapOp, Block.mapOp, Body.mapOp_id, CFG.mk.injEq, true_and]
      conv_rhs => rw [← List.map_id blocks]
      rfl

theorem Term.mapOp_comp (h : F → F') (k : F' → F'') :
    ∀ (τ : Term V K F), τ.mapOp (k ∘ h) = (τ.mapOp h).mapOp k
  | .br _ _ => rfl
  | .case o x t y u => by
      simp only [Term.mapOp, Op.mapOp_comp, Term.mapOp_comp h k t,
        Term.mapOp_comp h k u]

theorem Body.mapOp_comp (h : F → F') (k : F' → F'') :
    ∀ (β : Body V K F), β.mapOp (k ∘ h) = (β.mapOp h).mapOp k
  | .let1 x o β => by
      simp only [Body.mapOp, Op.mapOp_comp, Body.mapOp_comp h k β]
  | .let2 x y o β => by
      simp only [Body.mapOp, Op.mapOp_comp, Body.mapOp_comp h k β]
  | .term τ => by simp only [Body.mapOp, Term.mapOp_comp h k τ]

theorem mapOp_comp (h : F → F') (k : F' → F'') (g : CFG V K F) :
    g.mapOp (k ∘ h) = (g.mapOp h).mapOp k := by
  simp only [CFG.mapOp, Block.mapOp, Body.mapOp_comp, List.map_map]
  rfl

end MapOp

end Silmaril.Proofs.SSA.LambdaRTL.CFG
