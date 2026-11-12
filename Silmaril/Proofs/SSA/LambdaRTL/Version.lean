module

public import Silmaril.SSA.LambdaRTL.Version.Defs

/-!
# Versioning λRTL into λSSA: scoping and semantic correctness (proofs)

Restated in `Silmaril.SSA.LambdaRTL.Version.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.Version

open Silmaril.SSA.LambdaRTL Silmaril.SSA.LambdaRTL.Version

universe v w

variable {V L : Type w} {F : Type v} {M : Type w → Type w} {α : Type w}

/-! ## Bookkeeping -/

section Book

variable [DecidableEq V]

theorem setv_self (cur : V → ℕ) (x : V) (n : ℕ) : setv cur x n x = n := by simp [setv]

theorem setv_of_ne (cur : V → ℕ) {x y : V} (n : ℕ) (h : y ≠ x) : setv cur x n y = cur y := by
  simp [setv, h]

theorem unpackCur_of_not_mem : ∀ (ys : List V) (cur : V → ℕ) (d : ℕ) (y : V), y ∉ ys →
    unpackCur ys cur d y = cur y
  | [], _, _, _, _ => rfl
  | z :: ys, cur, d, y, h => by
      simp only [List.mem_cons, not_or] at h
      simp only [unpackCur]
      rw [unpackCur_of_not_mem ys _ _ y h.2, setv_of_ne _ _ h.1]

theorem mem_liveIns {L : Type w} {F : Type v} (t : Region V L F) (x : V) (live : List V)
    (z : V) : z ∈ liveIns t x live ↔ (z ∈ t.fvList ∨ z ∈ live) ∧ z ≠ x := by
  simp [liveIns, List.mem_dedup, List.mem_filter, or_and_right]

end Book

/-! ## Values -/

theorem Val.eval_rn (m : Model F M α) (cur : V → ℕ) (ρ : V × ℕ → α) :
    ∀ a : Val V, (rn cur a).eval m ρ = a.eval m (fun y => ρ (y, cur y))
  | .var _ => rfl
  | .unit => rfl
  | .pair a b => by simp only [rn, Val.eval, Val.eval_rn m cur ρ a, Val.eval_rn m cur ρ b]

theorem Val.eval_congrL (m : Model F M α) {σ₁ σ₂ : V → α} :
    ∀ a : Val V, (∀ y ∈ a.fvList, σ₁ y = σ₂ y) → a.eval m σ₁ = a.eval m σ₂
  | .var x, h => h x (by simp [Val.fvList])
  | .unit, _ => rfl
  | .pair a b, h => by
      simp only [Val.eval]
      rw [Val.eval_congrL m a (fun y hy => h y (by simp [Val.fvList, hy])),
        Val.eval_congrL m b (fun y hy => h y (by simp [Val.fvList, hy]))]

theorem Op.eval_rn [Monad M] (m : Model F M α) (cur : V → ℕ) (ρ : V × ℕ → α) (o : Op V F) :
    (rnOp cur o).eval m ρ = o.eval m (fun y => ρ (y, cur y)) := by
  cases o <;> simp only [rnOp, Op.eval, Val.eval_rn]

theorem Op.eval_congrL [Monad M] (m : Model F M α) {σ₁ σ₂ : V → α} (o : Op V F)
    (h : ∀ y ∈ o.fvList, σ₁ y = σ₂ y) : o.eval m σ₁ = o.eval m σ₂ := by
  cases o <;> simp only [Op.eval, Op.fvList] at h ⊢ <;> rw [Val.eval_congrL m _ h]

theorem pack_eval (m : Model F M α) (cur : V → ℕ) (ρ : V × ℕ → α) :
    ∀ ys : List V, (pack cur ys).eval m ρ = packVal m (fun y => ρ (y, cur y)) ys
  | [] => rfl
  | y :: ys => by simp only [pack, Val.eval, packVal, pack_eval m cur ρ ys]

theorem packVal_congr (m : Model F M α) {σ₁ σ₂ : V → α} :
    ∀ ys : List V, (∀ y ∈ ys, σ₁ y = σ₂ y) → packVal m σ₁ ys = packVal m σ₂ ys
  | [], _ => rfl
  | y :: ys, h => by
      simp only [packVal]
      rw [h y (by simp), packVal_congr m ys (fun z hz => h z (by simp [hz]))]

theorem enc_fst (m : Model F M α) (lenv : L → Option (List V)) (e : L × α × (V → α)) :
    (enc m lenv e).1 = e.1 := by
  unfold enc; cases lenv e.1 <;> rfl

theorem enc_setl_self [DecidableEq L] (m : Model F M α) (lenv : L → Option (List V)) (ℓ : L)
    (ys : List V) (a : α) (σ : V → α) :
    enc m (setl lenv ℓ ys) (ℓ, a, σ) = (ℓ, m.pair a (packVal m σ ys)) := by
  simp [enc, setl]

theorem enc_setl_ne [DecidableEq L] (m : Model F M α) (lenv : L → Option (List V)) {ℓ l : L}
    (ys : List V) (a : α) (σ : V → α) (h : ¬ l = ℓ) :
    enc m (setl lenv ℓ ys) (l, a, σ) = enc m lenv (l, a, σ) := by
  simp [enc, setl, h]

/-! ## Scoping: the translation is dominance-scoped SSA -/

section Scope

variable [DecidableEq V]

theorem rn_fv_subset (cur : V → ℕ) {Γ : Finset (V × ℕ)} :
    ∀ a : Val V, (∀ y ∈ a.fvList, (y, cur y) ∈ Γ) → (rn cur a).fv ⊆ Γ
  | .var x, h => by simpa [rn, Val.fv, Val.fvList] using h
  | .unit, _ => by simp [rn, Val.fv]
  | .pair a b, h => by
      simp only [rn, Val.fv, Finset.union_subset_iff]
      exact ⟨rn_fv_subset cur a (fun y hy => h y (by simp [Val.fvList, hy])),
        rn_fv_subset cur b (fun y hy => h y (by simp [Val.fvList, hy]))⟩

theorem rnOp_fv_subset (cur : V → ℕ) {Γ : Finset (V × ℕ)} (o : Op V F)
    (h : ∀ y ∈ o.fvList, (y, cur y) ∈ Γ) : (rnOp cur o).fv ⊆ Γ := by
  cases o <;> simp only [rnOp, Op.fv, Op.fvList] at h ⊢ <;> exact rn_fv_subset cur _ h

theorem pack_fv_subset (cur : V → ℕ) {Γ : Finset (V × ℕ)} :
    ∀ ys : List V, (∀ y ∈ ys, (y, cur y) ∈ Γ) → (pack cur ys).fv ⊆ Γ
  | [], _ => by simp [pack, Val.fv]
  | y :: ys, h => by
      simp only [pack, Val.fv, Finset.union_subset_iff, Finset.singleton_subset_iff]
      exact ⟨h y (by simp), pack_fv_subset cur ys (fun z hz => h z (by simp [hz]))⟩

/-- The context after `unpack`. -/
def unpackCtx : List V → ℕ → Finset (V × ℕ) → Finset (V × ℕ)
  | [], _, Γ => Γ
  | y :: ys, d, Γ => unpackCtx ys (d + 2) (insert (y, d + 2) (insert (y, d + 1) Γ))

theorem subset_unpackCtx : ∀ (ys : List V) (d : ℕ) (Γ : Finset (V × ℕ)), Γ ⊆ unpackCtx ys d Γ
  | [], _, _ => fun _ h => h
  | y :: ys, d, Γ => fun p hp => subset_unpackCtx ys (d + 2) _ (by simp [hp])

theorem unpackCtx_bound : ∀ (ys : List V) (d : ℕ) (Γ : Finset (V × ℕ)),
    (∀ p ∈ Γ, p.2 ≤ d) → ∀ p ∈ unpackCtx ys d Γ, p.2 ≤ d + 2 * ys.length
  | [], d, Γ, h => by simpa [unpackCtx] using h
  | y :: ys, d, Γ, h => by
      intro p hp
      have := unpackCtx_bound ys (d + 2) _ (by
        intro q hq
        simp only [Finset.mem_insert] at hq
        rcases hq with rfl | rfl | hq
        · simp
        · simp
        · have := h q hq; omega) p hp
      simp only [List.length_cons]; omega

theorem unpackCur_mem : ∀ (ys : List V) (cur : V → ℕ) (d : ℕ) (Γ : Finset (V × ℕ)) (y : V),
    y ∈ ys → (y, unpackCur ys cur d y) ∈ unpackCtx ys d Γ
  | [], _, _, _, _, h => absurd h (by simp)
  | z :: ys, cur, d, Γ, y, h => by
      simp only [unpackCur, unpackCtx]
      by_cases hy : y ∈ ys
      · exact unpackCur_mem ys _ _ _ y hy
      · have hyz : y = z := by simpa [hy] using h
        subst hyz
        rw [unpackCur_of_not_mem ys _ _ y hy, setv_self]
        exact subset_unpackCtx ys _ _ (by simp)

theorem unpack_isSSA {L : Type w} : ∀ (ys : List V) (src : V × ℕ) (d : ℕ) (Γ : Finset (V × ℕ))
    (b : Region (V × ℕ) L F), src ∈ Γ → (∀ p ∈ Γ, p.2 ≤ d) →
    b.IsSSA (unpackCtx ys d Γ) → (unpack ys src d b).IsSSA Γ
  | [], _, _, _, _, _, _, hb => hb
  | y :: ys, src, d, Γ, b, hs, hΓ, hb => by
      simp only [unpack, Region.IsSSA]
      refine ⟨by simpa [Op.fv, Val.fv] using hs, fun h => by have : d + 1 ≤ d := hΓ _ h; omega,
        fun h => by have : d + 2 ≤ d := hΓ _ h; omega, by simp, ?_⟩
      apply unpack_isSSA ys (y, d + 2) (d + 2) _ b (by simp)
      · intro q hq
        simp only [Finset.mem_insert] at hq
        rcases hq with rfl | rfl | hq
        · simp
        · simp
        · have := hΓ q hq; omega
      · exact hb

theorem version_isSSA [DecidableEq L] : ∀ (r : Region V L F) (lenv : L → Option (List V))
    (live : List V) (cur : V → ℕ) (d : ℕ) (Γ : Finset (V × ℕ)),
    (∀ ℓ ys, lenv ℓ = some ys → ∀ y ∈ ys, y ∈ live) →
    (∀ p ∈ Γ, p.2 ≤ d) →
    (∀ y, y ∈ r.fvList ∨ y ∈ live → (y, cur y) ∈ Γ) →
    (version lenv live cur d r).IsSSA Γ
  | .br ℓ a, lenv, live, cur, d, Γ, hl, _, hΓ => by
      cases h : lenv ℓ with
      | none =>
          simp only [version, h, Region.IsSSA]
          exact rn_fv_subset cur a (fun y hy => hΓ y (Or.inl hy))
      | some ys =>
          simp only [version, h, Region.IsSSA, Val.fv, Finset.union_subset_iff]
          exact ⟨rn_fv_subset cur a (fun y hy => hΓ y (Or.inl hy)),
            pack_fv_subset cur ys (fun y hy => hΓ y (Or.inr (hl ℓ ys h y hy)))⟩
  | .let1 x o r, lenv, live, cur, d, Γ, hl, hd, hΓ => by
      simp only [version, Region.IsSSA]
      refine ⟨rnOp_fv_subset cur o (fun y hy => hΓ y (Or.inl (by simp [Region.fvList, hy]))),
        fun h => by have : d + 1 ≤ d := hd _ h; omega, ?_⟩
      apply version_isSSA r lenv live _ (d + 1) _ hl
      · intro p hp
        simp only [Finset.mem_insert] at hp
        rcases hp with rfl | hp
        · simp
        · have := hd p hp; omega
      · intro y hy
        by_cases hyx : y = x
        · subst hyx; simp [setv]
        · rw [setv_of_ne _ _ hyx]
          refine Finset.mem_insert_of_mem (hΓ y ?_)
          rcases hy with hy | hy
          · exact Or.inl (by simp [Region.fvList, hy, hyx])
          · exact Or.inr hy
  | .let2 x y o r, lenv, live, cur, d, Γ, hl, hd, hΓ => by
      simp only [version, Region.IsSSA]
      refine ⟨rnOp_fv_subset cur o (fun z hz => hΓ z (Or.inl (by simp [Region.fvList, hz]))),
        fun h => by have : d + 1 ≤ d := hd _ h; omega,
        fun h => by have : d + 2 ≤ d := hd _ h; omega, by simp, ?_⟩
      apply version_isSSA r lenv live _ (d + 2) _ hl
      · intro p hp
        simp only [Finset.mem_insert] at hp
        rcases hp with rfl | rfl | hp
        · simp
        · simp
        · have := hd p hp; omega
      · intro z hz
        by_cases hzy : z = y
        · subst hzy; simp [setv]
        · by_cases hzx : z = x
          · subst hzx; simp [setv, hzy]
          · rw [setv_of_ne _ _ hzy, setv_of_ne _ _ hzx]
            refine Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hΓ z ?_))
            rcases hz with hz | hz
            · exact Or.inl (by simp [Region.fvList, hz, hzx, hzy])
            · exact Or.inr hz
  | .case o x r y s, lenv, live, cur, d, Γ, hl, hd, hΓ => by
      simp only [version, Region.IsSSA]
      refine ⟨rnOp_fv_subset cur o (fun z hz => hΓ z (Or.inl (by simp [Region.fvList, hz]))),
        fun h => by have : d + 1 ≤ d := hd _ h; omega,
        fun h => by have : d + 1 ≤ d := hd _ h; omega, ?_, ?_⟩
      · apply version_isSSA r lenv live _ (d + 1) _ hl
        · intro p hp
          simp only [Finset.mem_insert] at hp
          rcases hp with rfl | hp
          · simp
          · have := hd p hp; omega
        · intro z hz
          by_cases hzx : z = x
          · subst hzx; simp [setv]
          · rw [setv_of_ne _ _ hzx]
            refine Finset.mem_insert_of_mem (hΓ z ?_)
            rcases hz with hz | hz
            · exact Or.inl (by simp [Region.fvList, hz, hzx])
            · exact Or.inr hz
      · apply version_isSSA s lenv live _ (d + 1) _ hl
        · intro p hp
          simp only [Finset.mem_insert] at hp
          rcases hp with rfl | hp
          · simp
          · have := hd p hp; omega
        · intro z hz
          by_cases hzy : z = y
          · subst hzy; simp [setv]
          · rw [setv_of_ne _ _ hzy]
            refine Finset.mem_insert_of_mem (hΓ z ?_)
            rcases hz with hz | hz
            · exact Or.inl (by simp [Region.fvList, hz, hzy])
            · exact Or.inr hz
  | .join r ℓ x t, lenv, live, cur, d, Γ, hl, hd, hΓ => by
      have hys := mem_liveIns t x live
      simp only [version, Region.IsSSA]
      refine ⟨?_, fun h => by have : d + 1 ≤ d := hd _ h; omega, ?_⟩
      · apply version_isSSA r _ _ cur d Γ _ hd
        · intro z hz
          rcases hz with hz | hz
          · exact hΓ z (Or.inl (by simp [Region.fvList, hz]))
          · rw [List.mem_dedup, List.mem_append] at hz
            rcases hz with hz | hz
            · obtain ⟨hz | hz, hzx⟩ := (hys z).1 hz
              · exact hΓ z (Or.inl (by simp [Region.fvList, hz, hzx]))
              · exact hΓ z (Or.inr hz)
            · exact hΓ z (Or.inr hz)
        · intro l ys h y hy
          simp only [setl] at h
          split at h
          · cases h; simp [hy]
          · simp [hl l ys h y hy]
      · refine ⟨by simp [Op.fv, Val.fv], fun h => ?_, fun h => ?_, by simp, ?_⟩
        · rw [Finset.mem_insert] at h
          rcases h with h | h
          · simp at h
          · have : d + 2 ≤ d := hd _ h; omega
        · rw [Finset.mem_insert] at h
          rcases h with h | h
          · simp at h
          · have : d + 3 ≤ d := hd _ h; omega
        apply unpack_isSSA _ (x, d + 3) (d + 3) _ _ (by simp)
        · intro q hq
          simp only [Finset.mem_insert] at hq
          rcases hq with rfl | rfl | rfl | hq
          · simp
          · simp
          · simp
          · have := hd q hq; omega
        · apply version_isSSA t lenv live _ _ _ hl
          · exact unpackCtx_bound _ _ _ (by
              intro q hq
              simp only [Finset.mem_insert] at hq
              rcases hq with rfl | rfl | rfl | hq
              · simp
              · simp
              · simp
              · have := hd q hq; omega)
          · intro z hz
            by_cases hzx : z = x
            · subst hzx
              have hnot : z ∉ liveIns t z live := fun h => ((hys z).1 h).2 rfl
              rw [unpackCur_of_not_mem _ _ _ _ hnot, setv_self]
              exact subset_unpackCtx _ _ _ (by simp)
            · exact unpackCur_mem _ _ _ _ z ((hys z).2 ⟨hz, hzx⟩)

end Scope

/-! ## Semantics -/

section Sem

variable [Monad M] [LawfulMonad M] [DecidableEq V]

/-- The environment after `unpack`, given the store whose live-ins were packed. -/
def unpackEnv (m : Model F M α) (σ : V → α) : List V → ℕ → (V × ℕ → α) → V × ℕ → α
  | [], _, ρ => ρ
  | y :: ys, d, ρ => unpackEnv m σ ys (d + 2) (upd (upd ρ (y, d + 1) (σ y)) (y, d + 2) (packVal m σ ys))

omit [Monad M] [LawfulMonad M] in
theorem unpackEnv_frame (m : Model F M α) (σ : V → α) : ∀ (ys : List V) (d : ℕ)
    (ρ : V × ℕ → α) (y : V), y ∉ ys → ∀ k, unpackEnv m σ ys d ρ (y, k) = ρ (y, k)
  | [], _, _, _, _, _ => rfl
  | z :: ys, d, ρ, y, h, k => by
      simp only [List.mem_cons, not_or] at h
      simp only [unpackEnv]
      rw [unpackEnv_frame m σ ys _ _ y h.2]
      simp [upd, h.1]

omit [Monad M] [LawfulMonad M] in
theorem unpackEnv_mem (m : Model F M α) (σ : V → α) : ∀ (ys : List V) (cur : V → ℕ) (d : ℕ)
    (ρ : V × ℕ → α) (y : V), y ∈ ys → unpackEnv m σ ys d ρ (y, unpackCur ys cur d y) = σ y
  | [], _, _, _, _, h => absurd h (by simp)
  | z :: ys, cur, d, ρ, y, h => by
      simp only [unpackEnv, unpackCur]
      by_cases hy : y ∈ ys
      · exact unpackEnv_mem m σ ys _ _ _ y hy
      · have hyz : y = z := by simpa [hy] using h
        subst hyz
        rw [unpackCur_of_not_mem ys _ _ y hy, setv_self, unpackEnv_frame m σ ys _ _ y hy]
        simp [upd]

theorem unpack_evalSSA [DecidableEq L] (m : Model F M α) (hm : m.PairLawful) (σ : V → α) :
    ∀ (ys : List V) (src : V × ℕ) (d : ℕ) (b : Region (V × ℕ) L F) (ρ : V × ℕ → α),
      ρ src = packVal m σ ys →
      (unpack ys src d b).evalSSA m ρ = b.evalSSA m (unpackEnv m σ ys d ρ)
  | [], _, _, _, _, _ => rfl
  | y :: ys, src, d, b, ρ, h => by
      simp only [unpack, Region.evalSSA, Op.eval, Val.eval, h, packVal, pure_bind,
        hm.unpair_pair]
      rw [unpack_evalSSA m hm σ ys _ _ b _ (by simp [upd])]
      rfl

theorem version_evalSSA [DecidableEq L] (m : Model F M α) (hm : m.PairLawful) :
    ∀ (r : Region V L F) (lenv : L → Option (List V)) (live : List V) (cur : V → ℕ) (d : ℕ)
      (σ : V → α) (ρ : V × ℕ → α),
      (∀ ℓ ys, lenv ℓ = some ys → ∀ y ∈ ys, y ∈ live) →
      (∀ y, y ∈ r.fvList ∨ y ∈ live → ρ (y, cur y) = σ y) →
      (version lenv live cur d r).evalSSA m ρ = r.evalRTL m σ >>= fun e => pure (enc m lenv e)
  | .br ℓ a, lenv, live, cur, d, σ, ρ, hl, hrel => by
      have ha : a.eval m (fun y => ρ (y, cur y)) = a.eval m σ :=
        Val.eval_congrL m a (fun y hy => hrel y (Or.inl hy))
      cases h : lenv ℓ with
      | none =>
          simp only [version, h, Region.evalSSA, Region.evalRTL, pure_bind, enc, Val.eval_rn, ha]
      | some ys =>
          have hp : packVal m (fun y => ρ (y, cur y)) ys = packVal m σ ys :=
            packVal_congr m ys (fun y hy => hrel y (Or.inr (hl ℓ ys h y hy)))
          simp only [version, h, Region.evalSSA, Region.evalRTL, pure_bind, enc, Val.eval,
            Val.eval_rn, pack_eval, ha, hp]
  | .let1 x o r, lenv, live, cur, d, σ, ρ, hl, hrel => by
      simp only [version, Region.evalSSA, Region.evalRTL, bind_assoc, Op.eval_rn]
      rw [Op.eval_congrL m o (fun y hy => hrel y (Or.inl (by simp [Region.fvList, hy])))]
      congr 1; funext a
      refine version_evalSSA m hm r lenv live _ _ _ _ hl ?_
      intro y hy
      by_cases hyx : y = x
      · subst hyx; simp [upd, setv]
      · have := hrel y (by
          rcases hy with hy | hy
          · exact Or.inl (by simp [Region.fvList, hy, hyx])
          · exact Or.inr hy)
        simp [upd, setv, hyx, this]
  | .let2 x y o r, lenv, live, cur, d, σ, ρ, hl, hrel => by
      simp only [version, Region.evalSSA, Region.evalRTL, bind_assoc, Op.eval_rn]
      rw [Op.eval_congrL m o (fun z hz => hrel z (Or.inl (by simp [Region.fvList, hz])))]
      congr 1; funext a; congr 1; funext p
      refine version_evalSSA m hm r lenv live _ _ _ _ hl ?_
      intro z hz
      by_cases hzy : z = y
      · subst hzy; simp [upd, setv]
      · by_cases hzx : z = x
        · subst hzx; simp [upd, setv, hzy]
        · have := hrel z (by
            rcases hz with hz | hz
            · exact Or.inl (by simp [Region.fvList, hz, hzx, hzy])
            · exact Or.inr hz)
          simp [upd, setv, hzy, hzx, this]
  | .case o x r y s, lenv, live, cur, d, σ, ρ, hl, hrel => by
      simp only [version, Region.evalSSA, Region.evalRTL, bind_assoc, Op.eval_rn]
      rw [Op.eval_congrL m o (fun z hz => hrel z (Or.inl (by simp [Region.fvList, hz])))]
      congr 1; funext a; congr 1; funext c
      cases c with
      | inl b =>
          refine version_evalSSA m hm r lenv live _ _ _ _ hl ?_
          intro z hz
          by_cases hzx : z = x
          · subst hzx; simp [upd, setv]
          · have := hrel z (by
              rcases hz with hz | hz
              · exact Or.inl (by simp [Region.fvList, hz, hzx])
              · exact Or.inr hz)
            simp [upd, setv, hzx, this]
      | inr b =>
          refine version_evalSSA m hm s lenv live _ _ _ _ hl ?_
          intro z hz
          by_cases hzy : z = y
          · subst hzy; simp [upd, setv]
          · have := hrel z (by
              rcases hz with hz | hz
              · exact Or.inl (by simp [Region.fvList, hz, hzy])
              · exact Or.inr hz)
            simp [upd, setv, hzy, this]
  | .join r ℓ x t, lenv, live, cur, d, σ, ρ, hl, hrel => by
      have hys := mem_liveIns t x live
      have hxys : x ∉ liveIns t x live := fun h => ((hys x).1 h).2 rfl
      have ihr := version_evalSSA m hm r (setl lenv ℓ (liveIns t x live))
        (liveIns t x live ++ live).dedup cur d σ ρ
        (by
          intro l ys h y hy
          simp only [setl] at h
          split at h
          · cases h; simp [hy]
          · simp [hl l ys h y hy])
        (by
          intro z hz
          rcases hz with hz | hz
          · exact hrel z (Or.inl (by simp [Region.fvList, hz]))
          · rw [List.mem_dedup, List.mem_append] at hz
            rcases hz with hz | hz
            · obtain ⟨hz | hz, hzx⟩ := (hys z).1 hz
              · exact hrel z (Or.inl (by simp [Region.fvList, hz, hzx]))
              · exact hrel z (Or.inr hz)
            · exact hrel z (Or.inr hz))
      simp only [version, Region.evalSSA, Region.evalRTL, bind_assoc]
      rw [ihr, bind_assoc]
      congr 1; funext e
      obtain ⟨l, a, σ'⟩ := e
      simp only [pure_bind]
      by_cases hlℓ : l = ℓ
      · simp only [hlℓ, enc_setl_self, ↓reduceIte, Op.eval, Val.eval,
          upd, pure_bind, hm.unpair_pair]
        rw [unpack_evalSSA m hm σ' _ _ _ _ _ (by simp [upd])]
        apply version_evalSSA m hm t lenv live _ _ _ _ hl
        intro z hz
        by_cases hzx : z = x
        · subst hzx
          rw [unpackCur_of_not_mem _ _ _ _ hxys, setv_self, unpackEnv_frame m σ' _ _ _ _ hxys]
          simp [upd]
        · rw [unpackEnv_mem m σ' _ _ _ _ z ((hys z).2 ⟨hz, hzx⟩)]
          simp [upd, hzx]
      · simp only [enc_fst, hlℓ, ↓reduceIte, pure_bind, enc_setl_ne m lenv _ a σ' hlℓ]

end Sem

/-! ## Instruction renaming commutes with versioning -/

section Rename

variable {F' : Type v} (h : F → F')

theorem rnOp_mapOp (cur : V → ℕ) (o : Op V F) : rnOp cur (o.mapOp h) = (rnOp cur o).mapOp h := by
  cases o <;> rfl

theorem Op.fvList_mapOp (o : Op V F) : (o.mapOp h).fvList = o.fvList := by cases o <;> rfl

variable [DecidableEq V]

theorem Region.fvList_mapOp : ∀ r : Region V L F, (r.mapOp h).fvList = r.fvList
  | .br _ _ => rfl
  | .let1 _ o r => by simp only [Region.mapOp, Region.fvList, Op.fvList_mapOp, Region.fvList_mapOp r]
  | .let2 _ _ o r => by
      simp only [Region.mapOp, Region.fvList, Op.fvList_mapOp, Region.fvList_mapOp r]
  | .case o _ r _ s => by
      simp only [Region.mapOp, Region.fvList, Op.fvList_mapOp, Region.fvList_mapOp r,
        Region.fvList_mapOp s]
  | .join r _ _ t => by simp only [Region.mapOp, Region.fvList, Region.fvList_mapOp r,
      Region.fvList_mapOp t]

theorem liveIns_mapOp (t : Region V L F) (x : V) (live : List V) :
    liveIns (t.mapOp h) x live = liveIns t x live := by
  simp only [liveIns, Region.fvList_mapOp]

omit [DecidableEq V] in
theorem unpack_mapOp : ∀ (ys : List V) (src : V × ℕ) (d : ℕ) (b : Region (V × ℕ) L F),
    (unpack ys src d b).mapOp h = unpack ys src d (b.mapOp h)
  | [], _, _, _ => rfl
  | y :: ys, src, d, b => by
      simp only [unpack, Region.mapOp, Op.mapOp, unpack_mapOp ys]

theorem version_mapOp [DecidableEq L] : ∀ (r : Region V L F) (lenv : L → Option (List V))
    (live : List V) (cur : V → ℕ) (d : ℕ),
    version lenv live cur d (r.mapOp h) = (version lenv live cur d r).mapOp h
  | .br ℓ _, lenv, _, _, _ => by
      cases hl : lenv ℓ <;> simp only [Region.mapOp, version, hl]
  | .let1 _ o r, _, _, _, _ => by
      simp only [Region.mapOp, version, rnOp_mapOp, version_mapOp r]
  | .let2 _ _ o r, _, _, _, _ => by
      simp only [Region.mapOp, version, rnOp_mapOp, version_mapOp r]
  | .case o _ r _ s, _, _, _, _ => by
      simp only [Region.mapOp, version, rnOp_mapOp, version_mapOp r, version_mapOp s]
  | .join r _ x t, _, _, _, _ => by
      simp only [Region.mapOp, version, liveIns_mapOp, version_mapOp r, version_mapOp t,
        unpack_mapOp, Op.mapOp]

end Rename

end Silmaril.Proofs.SSA.LambdaRTL.Version
