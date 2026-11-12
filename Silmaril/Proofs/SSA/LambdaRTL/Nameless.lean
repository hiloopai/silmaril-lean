module

public import Silmaril.SSA.LambdaRTL.Nameless.Defs
public import Silmaril.SSA.LambdaRTL.Thms

/-!
# Nameless presentation of acyclic λSSA: proofs

Restated in `Silmaril.SSA.LambdaRTL.Nameless.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.Nameless

open Silmaril.SSA.LambdaRTL

universe v w

variable {V W L : Type w} {F F' : Type v} {M : Type w → Type w} {α : Type w}

/-! ## Context lookup -/

section Idx

variable [DecidableEq V]

theorem idx_cons_self (x : V) (Γ : List V) : idx x (x :: Γ) = 0 := by
  simp [idx]

theorem idx_cons_of_ne {x y : V} (Γ : List V) (h : x ≠ y) : idx x (y :: Γ) = idx x Γ + 1 := by
  simp [idx, h]

theorem idx_lt_length_iff (x : V) : ∀ Γ : List V, idx x Γ < Γ.length ↔ x ∈ Γ
  | [] => by simp [idx]
  | y :: Γ => by
      by_cases h : x = y
      · subst h; simp [idx]
      · rw [idx_cons_of_ne _ h, List.length_cons, Nat.add_lt_add_iff_right,
          idx_lt_length_iff x Γ, List.mem_cons]
        exact ⟨Or.inr, fun h' => h'.resolve_left h⟩

theorem getElem?_idx (x : V) : ∀ Γ : List V, x ∈ Γ → Γ[idx x Γ]? = some x
  | [], h => by simp at h
  | y :: Γ, h => by
      by_cases hxy : x = y
      · subst hxy; simp [idx]
      · rw [idx_cons_of_ne _ hxy, List.getElem?_cons_succ]
        exact getElem?_idx x Γ ((List.mem_cons.1 h).resolve_left hxy)

omit [DecidableEq V] in
theorem getD_mem (d : V) : ∀ (Γ : List V) (i : ℕ), i < Γ.length → Γ.getD i d ∈ Γ
  | [], i, h => by simp at h
  | y :: Γ, 0, _ => by simp
  | y :: Γ, i + 1, h => by
      rw [List.getD_cons_succ]
      exact List.mem_cons_of_mem y (getD_mem d Γ i (by simpa using h))

theorem idx_getD (d : V) :
    ∀ (Γ : List V) (i : ℕ), Γ.Nodup → i < Γ.length → idx (Γ.getD i d) Γ = i
  | [], i, _, h => by simp at h
  | y :: Γ, 0, _, _ => by simp [idx]
  | y :: Γ, i + 1, hn, hi => by
      have hn' := List.nodup_cons.1 hn
      have hi' : i < Γ.length := by simpa using hi
      have hmem : Γ.getD i d ∈ Γ := getD_mem d Γ i hi'
      have hne : Γ.getD i d ≠ y := fun e => hn'.1 (by rw [← e]; exact hmem)
      rw [List.getD_cons_succ, idx_cons_of_ne _ hne, idx_getD d Γ i hn'.2 hi']

theorem idx_map [DecidableEq W] {f : V → W} (z : V) :
    ∀ Γ : List V, Set.InjOn f {w | w = z ∨ w ∈ Γ} → idx (f z) (Γ.map f) = idx z Γ
  | [], _ => rfl
  | y :: Γ, h => by
      have h' : Set.InjOn f {w | w = z ∨ w ∈ Γ} := h.mono (fun w hw => by
        rcases hw with hw | hw
        · exact Or.inl hw
        · exact Or.inr (List.mem_cons_of_mem y hw))
      by_cases hzy : z = y
      · subst hzy; simp [idx]
      · have hf : f z ≠ f y := fun e =>
          hzy (h (Or.inl rfl) (Or.inr (List.mem_cons.2 (Or.inl rfl))) e)
        rw [List.map_cons, idx_cons_of_ne _ hf, idx_cons_of_ne _ hzy, idx_map z Γ h']

end Idx

/-! ## Environments -/

section Env

variable [DecidableEq V]

theorem agree_cons {Γ : List V} {η : ℕ → α} {ρ : V → α} (h : Agree Γ η ρ) (x : V) (a : α) :
    Agree (x :: Γ) (DB.cons a η) (upd ρ x a) := by
  intro z hz
  by_cases hzx : z = x
  · subst hzx; simp [idx, DB.cons, upd]
  · have hzΓ : z ∈ Γ := (List.mem_cons.1 hz).resolve_left hzx
    rw [idx_cons_of_ne _ hzx]
    show η (idx z Γ) = (if z = x then a else ρ z)
    simp only [hzx, ↓reduceIte]
    exact h z hzΓ

theorem agree_env (Γ : List V) (ρ : V → α) (d : α) : Agree Γ (env Γ ρ d) ρ := by
  intro x hx
  simp only [env, getElem?_idx x Γ hx]

theorem agree_comp (Γ : List V) (η : ℕ → α) : Agree Γ η (fun x => η (idx x Γ)) :=
  fun _ _ => rfl

theorem subset_cons {s : Finset V} {x : V} {Γ : List V} (h : s.erase x ⊆ Γ.toFinset) :
    s ⊆ (x :: Γ).toFinset := by
  rw [List.toFinset_cons]
  intro z hz
  rw [Finset.mem_insert]
  by_cases hzx : z = x
  · exact Or.inl hzx
  · exact Or.inr (h (Finset.mem_erase.2 ⟨hzx, hz⟩))

end Env

/-! ## Adequacy of `toDB` -/

section Adequacy

variable [DecidableEq V]

theorem Val.eval_toDB (m : Model F M α) {Γ : List V} {η : ℕ → α} {ρ : V → α}
    (h : Agree Γ η ρ) : ∀ a : Val V, a.fv ⊆ Γ.toFinset → (a.toDB Γ).eval m η = a.eval m ρ
  | .var x, hs => h x (by simpa [Val.fv] using hs)
  | .unit, _ => rfl
  | .pair a b, hs => by
      simp only [Val.fv, Finset.union_subset_iff] at hs
      simp only [Val.toDB, DB.Val.eval, Val.eval, Val.eval_toDB m h a hs.1,
        Val.eval_toDB m h b hs.2]

variable [Monad M]

theorem Op.eval_toDB (m : Model F M α) {Γ : List V} {η : ℕ → α} {ρ : V → α}
    (h : Agree Γ η ρ) (o : Op V F) (hs : o.fv ⊆ Γ.toFinset) :
    (o.toDB Γ).eval m η = o.eval m ρ := by
  cases o <;> simp only [Op.fv] at hs <;>
    simp only [Op.toDB, DB.Op.eval, Op.eval, Val.eval_toDB m h _ hs]

variable [DecidableEq L]

theorem Region.eval_toDB (m : Model F M α) :
    ∀ (r : Region V L F) {Γ : List V} {η : ℕ → α} {ρ : V → α}, Agree Γ η ρ →
      r.fv ⊆ Γ.toFinset → (r.toDB Γ).eval m η = r.evalSSA m ρ
  | .br ℓ a, Γ, η, ρ, h, hs => by
      simp only [Region.fv] at hs
      simp only [Region.toDB, DB.Region.eval, Region.evalSSA, Val.eval_toDB m h a hs]
  | .let1 x o r, Γ, η, ρ, h, hs => by
      simp only [Region.fv, Finset.union_subset_iff] at hs
      simp only [Region.toDB, DB.Region.eval, Region.evalSSA, Op.eval_toDB m h o hs.1]
      congr 1; funext a
      exact Region.eval_toDB m r (agree_cons h x a) (subset_cons hs.2)
  | .let2 x y o r, Γ, η, ρ, h, hs => by
      simp only [Region.fv, Finset.union_subset_iff] at hs
      simp only [Region.toDB, DB.Region.eval, Region.evalSSA, Op.eval_toDB m h o hs.1]
      congr 1; funext p
      exact Region.eval_toDB m r (agree_cons (agree_cons h x p.1) y p.2)
        (subset_cons (subset_cons hs.2))
  | .case o x r y s, Γ, η, ρ, h, hs => by
      simp only [Region.fv, Finset.union_subset_iff, and_assoc] at hs
      obtain ⟨ho, hr, hs'⟩ := hs
      simp only [Region.toDB, DB.Region.eval, Region.evalSSA, Op.eval_toDB m h o ho]
      congr 1; funext c
      cases c with
      | inl a => exact Region.eval_toDB m r (agree_cons h x a) (subset_cons hr)
      | inr b => exact Region.eval_toDB m s (agree_cons h y b) (subset_cons hs')
  | .join r ℓ x t, Γ, η, ρ, h, hs => by
      simp only [Region.fv, Finset.union_subset_iff] at hs
      simp only [Region.toDB, DB.Region.eval, Region.evalSSA, Region.eval_toDB m r h hs.1]
      congr 1; funext e
      split
      · exact Region.eval_toDB m t (agree_cons h x e.2) (subset_cons hs.2)
      · rfl

end Adequacy

/-! ## Well-scopedness of `toDB` -/

section Scope

variable [DecidableEq V]

theorem Val.ws_toDB (Γ : List V) : ∀ a : Val V, a.fv ⊆ Γ.toFinset → (a.toDB Γ).WS Γ.length
  | .var x, hs => (idx_lt_length_iff x Γ).2 (by simpa [Val.fv] using hs)
  | .unit, _ => trivial
  | .pair a b, hs => by
      simp only [Val.fv, Finset.union_subset_iff] at hs
      exact ⟨Val.ws_toDB Γ a hs.1, Val.ws_toDB Γ b hs.2⟩

theorem Op.ws_toDB (Γ : List V) (o : Op V F) (hs : o.fv ⊆ Γ.toFinset) :
    (o.toDB Γ).WS Γ.length := by
  cases o <;> simp only [Op.fv] at hs <;> exact Val.ws_toDB Γ _ hs

theorem Region.ws_toDB :
    ∀ (r : Region V L F) (Γ : List V), r.fv ⊆ Γ.toFinset → (r.toDB Γ).WS Γ.length
  | .br ℓ a, Γ, hs => Val.ws_toDB Γ a hs
  | .let1 x o r, Γ, hs => by
      simp only [Region.fv, Finset.union_subset_iff] at hs
      exact ⟨Op.ws_toDB Γ o hs.1, Region.ws_toDB r (x :: Γ) (subset_cons hs.2)⟩
  | .let2 x y o r, Γ, hs => by
      simp only [Region.fv, Finset.union_subset_iff] at hs
      exact ⟨Op.ws_toDB Γ o hs.1,
        Region.ws_toDB r (y :: x :: Γ) (subset_cons (subset_cons hs.2))⟩
  | .case o x r y s, Γ, hs => by
      simp only [Region.fv, Finset.union_subset_iff, and_assoc] at hs
      exact ⟨Op.ws_toDB Γ o hs.1, Region.ws_toDB r (x :: Γ) (subset_cons hs.2.1),
        Region.ws_toDB s (y :: Γ) (subset_cons hs.2.2)⟩
  | .join r ℓ x t, Γ, hs => by
      simp only [Region.fv, Finset.union_subset_iff] at hs
      exact ⟨Region.ws_toDB r Γ hs.1, Region.ws_toDB t (x :: Γ) (subset_cons hs.2)⟩

end Scope

/-! ## Back translation -/

section OfDB

variable [DecidableEq V] (S : Supply V)

theorem nodup_cons_fresh {Γ : List V} (hΓ : Γ.Nodup) : (S.fresh Γ.toFinset :: Γ).Nodup :=
  List.nodup_cons.2 ⟨fun hx => S.fresh_not_mem _ (List.mem_toFinset.2 hx), hΓ⟩

theorem nodup_cons_fresh₂ {Γ : List V} (hΓ : Γ.Nodup) :
    (S.fresh (insert (S.fresh Γ.toFinset) Γ.toFinset) :: S.fresh Γ.toFinset :: Γ).Nodup := by
  rw [← List.toFinset_cons]
  exact nodup_cons_fresh S (nodup_cons_fresh S hΓ)

theorem Val.toDB_ofDB (d : V) {Γ : List V} (hΓ : Γ.Nodup) :
    ∀ a : DB.Val, a.WS Γ.length → (a.ofDB d Γ).toDB Γ = a
  | .var i, h => by
      simp only [DB.Val.ofDB, Val.toDB]
      rw [idx_getD d Γ i hΓ h]
  | .unit, _ => rfl
  | .pair a b, h => by
      simp only [DB.Val.ofDB, Val.toDB, Val.toDB_ofDB d hΓ a h.1, Val.toDB_ofDB d hΓ b h.2]

theorem Op.toDB_ofDB (d : V) {Γ : List V} (hΓ : Γ.Nodup) (o : DB.Op F)
    (h : o.WS Γ.length) : (o.ofDB d Γ).toDB Γ = o := by
  cases o <;> simp only [DB.Op.WS, DB.Op.arg] at h <;>
    simp only [DB.Op.ofDB, Op.toDB, Val.toDB_ofDB d hΓ _ h]

/-- **Round trip** `toDB ∘ ofDB = id` on well-scoped terms in a duplicate-free context. -/
theorem Region.toDB_ofDB :
    ∀ (Γ : List V) (d : DB.Region L F), Γ.Nodup → d.WS Γ.length → (d.ofDB S Γ).toDB Γ = d
  | Γ, .br ℓ a, hΓ, h => by
      simp only [DB.Region.ofDB, Region.toDB, Val.toDB_ofDB _ hΓ a h]
  | Γ, .let1 o r, hΓ, h => by
      simp only [DB.Region.ofDB, Region.toDB, Op.toDB_ofDB _ hΓ o h.1,
        Region.toDB_ofDB _ r (nodup_cons_fresh S hΓ) h.2]
  | Γ, .let2 o r, hΓ, h => by
      simp only [DB.Region.ofDB, Region.toDB, Op.toDB_ofDB _ hΓ o h.1,
        Region.toDB_ofDB _ r (nodup_cons_fresh₂ S hΓ) h.2]
  | Γ, .case o r s, hΓ, h => by
      simp only [DB.Region.ofDB, Region.toDB, Op.toDB_ofDB _ hΓ o h.1,
        Region.toDB_ofDB _ r (nodup_cons_fresh S hΓ) h.2.1,
        Region.toDB_ofDB _ s (nodup_cons_fresh S hΓ) h.2.2]
  | Γ, .join r ℓ t, hΓ, h => by
      simp only [DB.Region.ofDB, Region.toDB, Region.toDB_ofDB _ r hΓ h.1,
        Region.toDB_ofDB _ t (nodup_cons_fresh S hΓ) h.2]

theorem Val.fv_ofDB (d : V) (Γ : List V) :
    ∀ a : DB.Val, a.WS Γ.length → (a.ofDB d Γ).fv ⊆ Γ.toFinset
  | .var i, h => by
      simp only [DB.Val.ofDB, Val.fv, Finset.singleton_subset_iff, List.mem_toFinset]
      exact getD_mem d Γ i h
  | .unit, _ => by simp [DB.Val.ofDB, Val.fv]
  | .pair a b, h => by
      simp only [DB.Val.ofDB, Val.fv]
      exact Finset.union_subset (Val.fv_ofDB d Γ a h.1) (Val.fv_ofDB d Γ b h.2)

theorem Op.fv_ofDB (d : V) (Γ : List V) (o : DB.Op F) (h : o.WS Γ.length) :
    (o.ofDB d Γ).fv ⊆ Γ.toFinset := by
  cases o <;> simp only [DB.Op.WS, DB.Op.arg] at h <;>
    simp only [DB.Op.ofDB, Op.fv] <;> exact Val.fv_ofDB d Γ _ h

/-- The back translation produces dominance-scoped SSA. -/
theorem Region.isSSA_ofDB :
    ∀ (Γ : List V) (d : DB.Region L F), d.WS Γ.length → (d.ofDB S Γ).IsSSA Γ.toFinset
  | Γ, .br ℓ a, h => Val.fv_ofDB _ Γ a h
  | Γ, .let1 o r, h => by
      have ih := Region.isSSA_ofDB (S.fresh Γ.toFinset :: Γ) r h.2
      rw [List.toFinset_cons] at ih
      exact ⟨Op.fv_ofDB _ Γ o h.1, S.fresh_not_mem _, ih⟩
  | Γ, .let2 o r, h => by
      have ih := Region.isSSA_ofDB
        (S.fresh (insert (S.fresh Γ.toFinset) Γ.toFinset) :: S.fresh Γ.toFinset :: Γ) r h.2
      rw [List.toFinset_cons, List.toFinset_cons] at ih
      have hy := S.fresh_not_mem (insert (S.fresh Γ.toFinset) Γ.toFinset)
      rw [Finset.mem_insert, not_or] at hy
      exact ⟨Op.fv_ofDB _ Γ o h.1, S.fresh_not_mem _, hy.2, fun e => hy.1 e.symm, ih⟩
  | Γ, .case o r s, h => by
      have ihr := Region.isSSA_ofDB (S.fresh Γ.toFinset :: Γ) r h.2.1
      have ihs := Region.isSSA_ofDB (S.fresh Γ.toFinset :: Γ) s h.2.2
      rw [List.toFinset_cons] at ihr ihs
      exact ⟨Op.fv_ofDB _ Γ o h.1, S.fresh_not_mem _, S.fresh_not_mem _, ihr, ihs⟩
  | Γ, .join r ℓ t, h => by
      have iht := Region.isSSA_ofDB (S.fresh Γ.toFinset :: Γ) t h.2
      rw [List.toFinset_cons] at iht
      exact ⟨Region.isSSA_ofDB Γ r h.1, S.fresh_not_mem _, iht⟩

theorem Supply.length_ctx : ∀ n, (S.ctx n).length = n
  | 0 => rfl
  | n + 1 => by rw [Supply.ctx, List.length_cons, Supply.length_ctx n]

theorem Supply.nodup_ctx : ∀ n, (S.ctx n).Nodup
  | 0 => List.nodup_nil
  | n + 1 => nodup_cons_fresh S (Supply.nodup_ctx n)

end OfDB

/-! ## Renaming of names -/

section Rename

variable [DecidableEq V] [DecidableEq W] (f : V → W)

theorem Val.toDB_rename :
    ∀ (a : Val V) (Γ : List V), Set.InjOn f {w | w ∈ Γ ∨ w ∈ a.fv} →
      (a.rename f).toDB (Γ.map f) = a.toDB Γ
  | .var x, Γ, h => by
      simp only [Val.rename, Val.toDB]
      rw [idx_map x Γ (h.mono fun w hw => hw.elim (fun e => Or.inr (by simp [Val.fv, e]))
        Or.inl)]
  | .unit, _, _ => rfl
  | .pair a b, Γ, h => by
      simp only [Val.rename, Val.toDB]
      rw [Val.toDB_rename a Γ (h.mono fun w hw =>
          hw.elim Or.inl (fun hw => Or.inr (by simp [Val.fv, hw]))),
        Val.toDB_rename b Γ (h.mono fun w hw =>
          hw.elim Or.inl (fun hw => Or.inr (by simp [Val.fv, hw])))]

theorem Op.toDB_rename (o : Op V F) (Γ : List V) (h : Set.InjOn f {w | w ∈ Γ ∨ w ∈ o.fv}) :
    (o.rename f).toDB (Γ.map f) = o.toDB Γ := by
  cases o <;> simp only [Op.fv] at h <;>
    simp only [Op.rename, Op.toDB, Val.toDB_rename f _ Γ h]

/-- **Renaming invariance of `toDB`**: renaming names (binders included) along `f` and the
context along `f` gives the same de Bruijn term, provided `f` is injective on the context names
together with all names occurring in `r`. -/
theorem Region.toDB_rename :
    ∀ (r : Region V L F) (Γ : List V), Set.InjOn f {w | w ∈ Γ ∨ w ∈ r.vars} →
      (r.rename f).toDB (Γ.map f) = r.toDB Γ
  | .br ℓ a, Γ, h => by
      simp only [Region.rename, Region.toDB]
      rw [Val.toDB_rename f a Γ h]
  | .let1 x o r, Γ, h => by
      have ih := Region.toDB_rename r (x :: Γ) (h.mono fun w hw => by
        simp only [Set.mem_ofPred_eq, List.mem_cons, Region.vars, Finset.mem_insert,
          Finset.mem_union] at hw ⊢
        tauto)
      rw [List.map_cons] at ih
      simp only [Region.rename, Region.toDB, ih]
      rw [Op.toDB_rename f o Γ (h.mono fun w hw => by
        simp only [Set.mem_ofPred_eq, Region.vars, Finset.mem_insert, Finset.mem_union] at hw ⊢
        tauto)]
  | .let2 x y o r, Γ, h => by
      have ih := Region.toDB_rename r (y :: x :: Γ) (h.mono fun w hw => by
        simp only [Set.mem_ofPred_eq, List.mem_cons, Region.vars, Finset.mem_insert,
          Finset.mem_union] at hw ⊢
        tauto)
      simp only [List.map_cons] at ih
      simp only [Region.rename, Region.toDB, ih]
      rw [Op.toDB_rename f o Γ (h.mono fun w hw => by
        simp only [Set.mem_ofPred_eq, Region.vars, Finset.mem_insert, Finset.mem_union] at hw ⊢
        tauto)]
  | .case o x r y s, Γ, h => by
      have ihr := Region.toDB_rename r (x :: Γ) (h.mono fun w hw => by
        simp only [Set.mem_ofPred_eq, List.mem_cons, Region.vars, Finset.mem_insert,
          Finset.mem_union] at hw ⊢
        tauto)
      have ihs := Region.toDB_rename s (y :: Γ) (h.mono fun w hw => by
        simp only [Set.mem_ofPred_eq, List.mem_cons, Region.vars, Finset.mem_insert,
          Finset.mem_union] at hw ⊢
        tauto)
      rw [List.map_cons] at ihr ihs
      simp only [Region.rename, Region.toDB, ihr, ihs]
      rw [Op.toDB_rename f o Γ (h.mono fun w hw => by
        simp only [Set.mem_ofPred_eq, Region.vars, Finset.mem_insert, Finset.mem_union] at hw ⊢
        tauto)]
  | .join r ℓ x t, Γ, h => by
      have ihr := Region.toDB_rename r Γ (h.mono fun w hw => by
        simp only [Set.mem_ofPred_eq, Region.vars, Finset.mem_insert,
          Finset.mem_union] at hw ⊢
        tauto)
      have iht := Region.toDB_rename t (x :: Γ) (h.mono fun w hw => by
        simp only [Set.mem_ofPred_eq, List.mem_cons, Region.vars, Finset.mem_insert,
          Finset.mem_union] at hw ⊢
        tauto)
      rw [List.map_cons] at iht
      simp only [Region.rename, Region.toDB, ihr, iht]

end Rename

/-! ## de Bruijn renaming and weakening -/

section DBRename

theorem cons_comp_lift (a : α) (η : ℕ → α) (ξ : ℕ → ℕ) :
    DB.cons a η ∘ DB.lift ξ = DB.cons a (η ∘ ξ) := by
  funext n; cases n <;> rfl

theorem lift_lt {ξ : ℕ → ℕ} {n k : ℕ} (h : ∀ i < n, ξ i < k) :
    ∀ i < n + 1, DB.lift ξ i < k + 1
  | 0, _ => Nat.succ_pos _
  | i + 1, hi => Nat.succ_lt_succ (h i (Nat.lt_of_succ_lt_succ hi))

theorem DB.Val.eval_rename (m : Model F M α) (η : ℕ → α) (ξ : ℕ → ℕ) :
    ∀ a : DB.Val, (a.rename ξ).eval m η = a.eval m (η ∘ ξ)
  | .var _ => rfl
  | .unit => rfl
  | .pair a b => by
      simp only [DB.Val.rename, DB.Val.eval, DB.Val.eval_rename m η ξ a,
        DB.Val.eval_rename m η ξ b]

theorem DB.Val.ws_rename {ξ : ℕ → ℕ} {n k : ℕ} (hξ : ∀ i < n, ξ i < k) :
    ∀ a : DB.Val, a.WS n → (a.rename ξ).WS k
  | .var i, h => hξ i h
  | .unit, _ => trivial
  | .pair a b, h => ⟨DB.Val.ws_rename hξ a h.1, DB.Val.ws_rename hξ b h.2⟩

theorem DB.Val.eval_congr (m : Model F M α) {n : ℕ} {η₁ η₂ : ℕ → α}
    (hη : ∀ i < n, η₁ i = η₂ i) : ∀ a : DB.Val, a.WS n → a.eval m η₁ = a.eval m η₂
  | .var i, h => hη i h
  | .unit, _ => rfl
  | .pair a b, h => by
      simp only [DB.Val.eval, DB.Val.eval_congr m hη a h.1, DB.Val.eval_congr m hη b h.2]

theorem cons_agree {n : ℕ} {η₁ η₂ : ℕ → α} (hη : ∀ i < n, η₁ i = η₂ i) (a : α) :
    ∀ i < n + 1, DB.cons a η₁ i = DB.cons a η₂ i
  | 0, _ => rfl
  | i + 1, hi => hη i (Nat.lt_of_succ_lt_succ hi)

theorem DB.Op.ws_rename {ξ : ℕ → ℕ} {n k : ℕ} (hξ : ∀ i < n, ξ i < k) (o : DB.Op F)
    (h : o.WS n) : (o.rename ξ).WS k := by
  cases o <;> exact DB.Val.ws_rename hξ _ h

theorem DB.Region.ws_rename :
    ∀ (r : DB.Region L F) {ξ : ℕ → ℕ} {n k : ℕ}, (∀ i < n, ξ i < k) → r.WS n →
      (r.rename ξ).WS k
  | .br _ a, _, _, _, hξ, h => DB.Val.ws_rename hξ a h
  | .let1 o r, _, _, _, hξ, h => ⟨DB.Op.ws_rename hξ o h.1, DB.Region.ws_rename r (lift_lt hξ) h.2⟩
  | .let2 o r, _, _, _, hξ, h =>
      ⟨DB.Op.ws_rename hξ o h.1, DB.Region.ws_rename r (lift_lt (lift_lt hξ)) h.2⟩
  | .case o r s, _, _, _, hξ, h =>
      ⟨DB.Op.ws_rename hξ o h.1, DB.Region.ws_rename r (lift_lt hξ) h.2.1,
        DB.Region.ws_rename s (lift_lt hξ) h.2.2⟩
  | .join r _ t, _, _, _, hξ, h =>
      ⟨DB.Region.ws_rename r hξ h.1, DB.Region.ws_rename t (lift_lt hξ) h.2⟩

variable [Monad M]

theorem DB.Op.eval_rename (m : Model F M α) (η : ℕ → α) (ξ : ℕ → ℕ) (o : DB.Op F) :
    (o.rename ξ).eval m η = o.eval m (η ∘ ξ) := by
  cases o <;> simp only [DB.Op.rename, DB.Op.eval, DB.Val.eval_rename]

theorem DB.Op.eval_congr (m : Model F M α) {n : ℕ} {η₁ η₂ : ℕ → α}
    (hη : ∀ i < n, η₁ i = η₂ i) (o : DB.Op F) (h : o.WS n) : o.eval m η₁ = o.eval m η₂ := by
  cases o <;> simp only [DB.Op.WS, DB.Op.arg] at h <;>
    simp only [DB.Op.eval, DB.Val.eval_congr m hη _ h]

variable [DecidableEq L]

theorem DB.Region.eval_rename (m : Model F M α) :
    ∀ (r : DB.Region L F) (ξ : ℕ → ℕ) (η : ℕ → α), (r.rename ξ).eval m η = r.eval m (η ∘ ξ)
  | .br ℓ a, ξ, η => by
      simp only [DB.Region.rename, DB.Region.eval, DB.Val.eval_rename]
  | .let1 o r, ξ, η => by
      simp only [DB.Region.rename, DB.Region.eval, DB.Op.eval_rename]
      congr 1; funext a
      rw [DB.Region.eval_rename m r, cons_comp_lift]
  | .let2 o r, ξ, η => by
      simp only [DB.Region.rename, DB.Region.eval, DB.Op.eval_rename]
      congr 1; funext p
      rw [DB.Region.eval_rename m r, cons_comp_lift, cons_comp_lift]
  | .case o r s, ξ, η => by
      simp only [DB.Region.rename, DB.Region.eval, DB.Op.eval_rename]
      congr 1; funext c
      cases c with
      | inl a => dsimp only; rw [DB.Region.eval_rename m r, cons_comp_lift]
      | inr b => dsimp only; rw [DB.Region.eval_rename m s, cons_comp_lift]
  | .join r ℓ t, ξ, η => by
      simp only [DB.Region.rename, DB.Region.eval, DB.Region.eval_rename m r]
      congr 1; funext e
      split
      · rw [DB.Region.eval_rename m t, cons_comp_lift]
      · rfl

theorem DB.Region.eval_wk (m : Model F M α) (r : DB.Region L F) (a : α) (η : ℕ → α) :
    r.wk.eval m (DB.cons a η) = r.eval m η := by
  rw [DB.Region.wk, DB.Region.eval_rename]
  rfl

/-- Well-scoped terms only read the first `n` entries of the environment. -/
theorem DB.Region.eval_congr (m : Model F M α) :
    ∀ (r : DB.Region L F) {n : ℕ} {η₁ η₂ : ℕ → α}, (∀ i < n, η₁ i = η₂ i) → r.WS n →
      r.eval m η₁ = r.eval m η₂
  | .br ℓ a, _, _, _, hη, h => by
      simp only [DB.Region.eval, DB.Val.eval_congr m hη a h]
  | .let1 o r, _, _, _, hη, h => by
      simp only [DB.Region.eval, DB.Op.eval_congr m hη o h.1]
      congr 1; funext a
      exact DB.Region.eval_congr m r (cons_agree hη a) h.2
  | .let2 o r, _, _, _, hη, h => by
      simp only [DB.Region.eval, DB.Op.eval_congr m hη o h.1]
      congr 1; funext p
      exact DB.Region.eval_congr m r (cons_agree (cons_agree hη p.1) p.2) h.2
  | .case o r s, _, _, _, hη, h => by
      simp only [DB.Region.eval, DB.Op.eval_congr m hη o h.1]
      congr 1; funext c
      cases c with
      | inl a => exact DB.Region.eval_congr m r (cons_agree hη a) h.2.1
      | inr b => exact DB.Region.eval_congr m s (cons_agree hη b) h.2.2
  | .join r ℓ t, _, _, _, hη, h => by
      simp only [DB.Region.eval, DB.Region.eval_congr m r hη h.1]
      congr 1; funext e
      split
      · exact DB.Region.eval_congr m t (cons_agree hη e.2) h.2
      · rfl

end DBRename

/-! ## Instruction renaming -/

section MapOp

variable [DecidableEq V] (h : F → F')

theorem Op.toDB_mapOp (Γ : List V) (o : Op V F) : (o.mapOp h).toDB Γ = (o.toDB Γ).mapOp h := by
  cases o <;> rfl

theorem Region.toDB_mapOp :
    ∀ (Γ : List V) (r : Region V L F), (r.mapOp h).toDB Γ = (r.toDB Γ).mapOp h
  | _, .br _ _ => rfl
  | Γ, .let1 x o r => by
      simp only [Region.mapOp, Region.toDB, DB.Region.mapOp, Op.toDB_mapOp,
        Region.toDB_mapOp _ r]
  | Γ, .let2 x y o r => by
      simp only [Region.mapOp, Region.toDB, DB.Region.mapOp, Op.toDB_mapOp,
        Region.toDB_mapOp _ r]
  | Γ, .case o x r y s => by
      simp only [Region.mapOp, Region.toDB, DB.Region.mapOp, Op.toDB_mapOp,
        Region.toDB_mapOp _ r, Region.toDB_mapOp _ s]
  | Γ, .join r ℓ x t => by
      simp only [Region.mapOp, Region.toDB, DB.Region.mapOp, Region.toDB_mapOp _ r,
        Region.toDB_mapOp _ t]

omit [DecidableEq V] in
theorem Op.ofDB_mapOp (d : V) (Γ : List V) (o : DB.Op F) :
    (o.mapOp h).ofDB d Γ = (o.ofDB d Γ).mapOp h := by
  cases o <;> rfl

theorem Region.ofDB_mapOp (S : Supply V) :
    ∀ (Γ : List V) (r : DB.Region L F), (r.mapOp h).ofDB S Γ = (r.ofDB S Γ).mapOp h
  | _, .br _ _ => rfl
  | Γ, .let1 o r => by
      simp only [DB.Region.mapOp, DB.Region.ofDB, Region.mapOp, Op.ofDB_mapOp,
        Region.ofDB_mapOp S _ r]
  | Γ, .let2 o r => by
      simp only [DB.Region.mapOp, DB.Region.ofDB, Region.mapOp, Op.ofDB_mapOp,
        Region.ofDB_mapOp S _ r]
  | Γ, .case o r s => by
      simp only [DB.Region.mapOp, DB.Region.ofDB, Region.mapOp, Op.ofDB_mapOp,
        Region.ofDB_mapOp S _ r, Region.ofDB_mapOp S _ s]
  | Γ, .join r ℓ t => by
      simp only [DB.Region.mapOp, DB.Region.ofDB, Region.mapOp, Region.ofDB_mapOp S _ r,
        Region.ofDB_mapOp S _ t]

theorem DB.Op.ws_mapOp (n : ℕ) (o : DB.Op F) : (o.mapOp h).WS n ↔ o.WS n := by
  cases o <;> rfl

theorem DB.Region.ws_mapOp : ∀ (n : ℕ) (r : DB.Region L F), (r.mapOp h).WS n ↔ r.WS n
  | _, .br _ _ => Iff.rfl
  | n, .let1 o r => and_congr (DB.Op.ws_mapOp h n o) (DB.Region.ws_mapOp _ r)
  | n, .let2 o r => and_congr (DB.Op.ws_mapOp h n o) (DB.Region.ws_mapOp _ r)
  | n, .case o r s => and_congr (DB.Op.ws_mapOp h n o)
      (and_congr (DB.Region.ws_mapOp _ r) (DB.Region.ws_mapOp _ s))
  | _, .join r _ t => and_congr (DB.Region.ws_mapOp _ r) (DB.Region.ws_mapOp _ t)

theorem DB.Val.eval_reduct {F₁ F₂ : Type v} (k : F₁ → F₂) {M' : Type w → Type w}
    (m : Model F₂ M' α) (η : ℕ → α) : ∀ a : DB.Val, a.eval (m.reduct k) η = a.eval m η
  | .var _ => rfl
  | .unit => rfl
  | .pair a b => by
      simp only [DB.Val.eval, DB.Val.eval_reduct k m η a, DB.Val.eval_reduct k m η b]
      rfl

variable [Monad M] [DecidableEq L]

theorem DB.Op.eval_mapOp (m : Model F' M α) (η : ℕ → α) (o : DB.Op F) :
    (o.mapOp h).eval m η = o.eval (m.reduct h) η := by
  cases o <;> simp only [DB.Op.mapOp, DB.Op.eval, DB.Val.eval_reduct] <;> rfl

theorem DB.Region.eval_mapOp (m : Model F' M α) :
    ∀ (r : DB.Region L F) (η : ℕ → α), (r.mapOp h).eval m η = r.eval (m.reduct h) η
  | .br ℓ a, η => by
      simp only [DB.Region.mapOp, DB.Region.eval, DB.Val.eval_reduct]
  | .let1 o r, η => by
      simp only [DB.Region.mapOp, DB.Region.eval, DB.Op.eval_mapOp,
        DB.Region.eval_mapOp m r]
  | .let2 o r, η => by
      simp only [DB.Region.mapOp, DB.Region.eval, DB.Op.eval_mapOp,
        DB.Region.eval_mapOp m r]
      rfl
  | .case o r s, η => by
      simp only [DB.Region.mapOp, DB.Region.eval, DB.Op.eval_mapOp]
      congr 1
      funext c
      cases c with
      | inl a => exact DB.Region.eval_mapOp m r _
      | inr b => exact DB.Region.eval_mapOp m s _
  | .join r ℓ t, η => by
      simp only [DB.Region.mapOp, DB.Region.eval, DB.Region.eval_mapOp m r,
        DB.Region.eval_mapOp m t]

end MapOp

end Silmaril.Proofs.SSA.LambdaRTL.Nameless
