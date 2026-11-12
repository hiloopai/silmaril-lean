module

public import Silmaril.SSA.LambdaRTL.LocallyNameless.Defs
public import Silmaril.SSA.LambdaRTL.Nameless.Thms
import Silmaril.Proofs.SSA.LambdaRTL.Nameless

/-!
# Locally nameless presentation: proofs

Restated in `Silmaril.SSA.LambdaRTL.LocallyNameless.Thms`.
-/

@[expose] public section

namespace Silmaril.Proofs.SSA.LambdaRTL.LocallyNameless

open Silmaril.SSA.LambdaRTL

universe v w

variable {V L : Type w} {F : Type v} {M : Type w → Type w} {α : Type w}

section Idx

variable [DecidableEq V]

theorem idx_append_of_mem (x : V) (Γ : List V) :
    ∀ B : List V, x ∈ B → idx x (B ++ Γ) = idx x B
  | [], h => by simp at h
  | y :: B, h => by
      by_cases hxy : x = y
      · subst hxy; simp [idx]
      · rw [List.cons_append, Silmaril.Proofs.SSA.LambdaRTL.Nameless.idx_cons_of_ne _ hxy,
          Silmaril.Proofs.SSA.LambdaRTL.Nameless.idx_cons_of_ne _ hxy,
          idx_append_of_mem x Γ B ((List.mem_cons.1 h).resolve_left hxy)]

theorem idx_append_of_not_mem (x : V) (Γ : List V) :
    ∀ B : List V, x ∉ B → idx x (B ++ Γ) = B.length + idx x Γ
  | [], _ => by simp
  | y :: B, h => by
      have hxy : x ≠ y := fun e => h (by simp [e])
      rw [List.cons_append, Silmaril.Proofs.SSA.LambdaRTL.Nameless.idx_cons_of_ne _ hxy,
        idx_append_of_not_mem x Γ B (fun h' => h (List.mem_cons_of_mem y h')), List.length_cons]
      omega

end Idx

/-! ## The triangle `close ∘ toLN = toDB` -/

section Triangle

variable [DecidableEq V]

theorem Val.close_toLN (Γ B : List V) :
    ∀ a : Val V, (a.toLN B).close Γ B.length = a.toDB (B ++ Γ)
  | .var x => by
      by_cases h : x ∈ B
      · simp [Val.toLN, h, LN.Val.close, Val.toDB, idx_append_of_mem x Γ B h]
      · simp [Val.toLN, h, LN.Val.close, Val.toDB, idx_append_of_not_mem x Γ B h]
  | .unit => rfl
  | .pair a b => by
      simp only [Val.toLN, LN.Val.close, Val.toDB, Val.close_toLN Γ B a, Val.close_toLN Γ B b]

theorem Op.close_toLN (Γ B : List V) (o : Op V F) :
    (o.toLN B).close Γ B.length = o.toDB (B ++ Γ) := by
  cases o <;> simp only [Op.toLN, LN.Op.close, Op.toDB, Val.close_toLN]

theorem Region.close_toLN (Γ : List V) :
    ∀ (r : Region V L F) (B : List V), (r.toLN B).close Γ B.length = r.toDB (B ++ Γ)
  | .br _ a, B => by simp only [Region.toLN, LN.Region.close, Region.toDB, Val.close_toLN]
  | .let1 x o r, B => by
      have := Region.close_toLN Γ r (x :: B)
      simp only [List.length_cons, List.cons_append] at this
      simp only [Region.toLN, LN.Region.close, Region.toDB, Op.close_toLN, this]
  | .let2 x y o r, B => by
      have := Region.close_toLN Γ r (y :: x :: B)
      simp only [List.length_cons, List.cons_append] at this
      simp only [Region.toLN, LN.Region.close, Region.toDB, Op.close_toLN, this]
  | .case o x r y s, B => by
      have h1 := Region.close_toLN Γ r (x :: B)
      have h2 := Region.close_toLN Γ s (y :: B)
      simp only [List.length_cons, List.cons_append] at h1 h2
      simp only [Region.toLN, LN.Region.close, Region.toDB, Op.close_toLN, h1, h2]
  | .join r ℓ x t, B => by
      have h1 := Region.close_toLN Γ r B
      have h2 := Region.close_toLN Γ t (x :: B)
      simp only [List.length_cons, List.cons_append] at h2
      simp only [Region.toLN, LN.Region.close, Region.toDB, h1, h2]

end Triangle

/-! ## Scope of `toLN` -/

section Scope

variable [DecidableEq V]

theorem Val.ws_toLN (B : List V) : ∀ a : Val V, (a.toLN B).WS B.length
  | .var x => by
      by_cases h : x ∈ B
      · simp only [Val.toLN, h, ite_true, LN.Val.WS]
        exact (Silmaril.Proofs.SSA.LambdaRTL.Nameless.idx_lt_length_iff x B).2 h
      · simp [Val.toLN, h, LN.Val.WS]
  | .unit => trivial
  | .pair a b => ⟨Val.ws_toLN B a, Val.ws_toLN B b⟩

theorem Op.ws_toLN (B : List V) (o : Op V F) : (o.toLN B).WS B.length := by
  cases o <;> exact Val.ws_toLN B _

theorem Region.ws_toLN : ∀ (r : Region V L F) (B : List V), (r.toLN B).WS B.length
  | .br _ a, B => Val.ws_toLN B a
  | .let1 x o r, B => ⟨Op.ws_toLN B o, Region.ws_toLN r (x :: B)⟩
  | .let2 x y o r, B => ⟨Op.ws_toLN B o, Region.ws_toLN r (y :: x :: B)⟩
  | .case o x r y s, B => ⟨Op.ws_toLN B o, Region.ws_toLN r (x :: B), Region.ws_toLN s (y :: B)⟩
  | .join r _ x t, B => ⟨Region.ws_toLN r B, Region.ws_toLN t (x :: B)⟩

theorem Val.fv_toLN (B : List V) :
    ∀ (a : Val V) (z : V), z ∈ (a.toLN B).fv → z ∈ a.fv ∧ z ∉ B
  | .var x, z, hz => by
      by_cases h : x ∈ B
      · simp [Val.toLN, h, LN.Val.fv] at hz
      · simp only [Val.toLN, h, ite_false, LN.Val.fv, Finset.mem_singleton] at hz
        subst hz; exact ⟨by simp [Val.fv], h⟩
  | .unit, z, hz => by simp [Val.toLN, LN.Val.fv] at hz
  | .pair a b, z, hz => by
      simp only [Val.toLN, LN.Val.fv, Finset.mem_union] at hz
      rcases hz with hz | hz
      · exact ⟨by simp [Val.fv, (Val.fv_toLN B a z hz).1], (Val.fv_toLN B a z hz).2⟩
      · exact ⟨by simp [Val.fv, (Val.fv_toLN B b z hz).1], (Val.fv_toLN B b z hz).2⟩

theorem Op.fv_toLN (B : List V) (o : Op V F) (z : V) (hz : z ∈ (o.toLN B).fv) :
    z ∈ o.fv ∧ z ∉ B := by
  cases o <;> exact Val.fv_toLN B _ z hz

theorem Region.fv_toLN :
    ∀ (r : Region V L F) (B : List V) (z : V), z ∈ (r.toLN B).fv → z ∈ r.fv ∧ z ∉ B
  | .br _ a, B, z, hz => Val.fv_toLN B a z hz
  | .let1 x o r, B, z, hz => by
      simp only [Region.toLN, LN.Region.fv, Finset.mem_union] at hz
      rcases hz with hz | hz
      · exact ⟨by simp [Region.fv, (Op.fv_toLN B o z hz).1], (Op.fv_toLN B o z hz).2⟩
      · obtain ⟨h1, h2⟩ := Region.fv_toLN r (x :: B) z hz
        simp only [List.mem_cons, not_or] at h2
        exact ⟨by simp [Region.fv, h1, h2.1], h2.2⟩
  | .let2 x y o r, B, z, hz => by
      simp only [Region.toLN, LN.Region.fv, Finset.mem_union] at hz
      rcases hz with hz | hz
      · exact ⟨by simp [Region.fv, (Op.fv_toLN B o z hz).1], (Op.fv_toLN B o z hz).2⟩
      · obtain ⟨h1, h2⟩ := Region.fv_toLN r (y :: x :: B) z hz
        simp only [List.mem_cons, not_or] at h2
        exact ⟨by simp [Region.fv, h1, h2.1, h2.2.1], h2.2.2⟩
  | .case o x r y s, B, z, hz => by
      simp only [Region.toLN, LN.Region.fv, Finset.mem_union] at hz
      rcases hz with (hz | hz) | hz
      · exact ⟨by simp [Region.fv, (Op.fv_toLN B o z hz).1], (Op.fv_toLN B o z hz).2⟩
      · obtain ⟨h1, h2⟩ := Region.fv_toLN r (x :: B) z hz
        simp only [List.mem_cons, not_or] at h2
        exact ⟨by simp [Region.fv, h1, h2.1], h2.2⟩
      · obtain ⟨h1, h2⟩ := Region.fv_toLN s (y :: B) z hz
        simp only [List.mem_cons, not_or] at h2
        exact ⟨by simp [Region.fv, h1, h2.1], h2.2⟩
  | .join r _ x t, B, z, hz => by
      simp only [Region.toLN, LN.Region.fv, Finset.mem_union] at hz
      rcases hz with hz | hz
      · obtain ⟨h1, h2⟩ := Region.fv_toLN r B z hz
        exact ⟨by simp [Region.fv, h1], h2⟩
      · obtain ⟨h1, h2⟩ := Region.fv_toLN t (x :: B) z hz
        simp only [List.mem_cons, not_or] at h2
        exact ⟨by simp [Region.fv, h1, h2.1], h2.2⟩

end Scope

/-! ## Evaluation of `close` -/

section CloseEval

variable [DecidableEq V]

/-- Environments for closing at depth `k`: indices below `k` agree with `η`, and the index of a
free name `x` reads `ρ x`. -/
def CloseAgree (Γ : List V) (S : Finset V) (k : ℕ) (η' : ℕ → α) (ρ : V → α) (η : ℕ → α) :
    Prop :=
  (∀ i < k, η' i = η i) ∧ ∀ x ∈ S, η' (k + idx x Γ) = ρ x

theorem CloseAgree.mono {Γ : List V} {S T : Finset V} {k : ℕ} {η' η : ℕ → α} {ρ : V → α}
    (h : CloseAgree Γ T k η' ρ η) (hST : S ⊆ T) : CloseAgree Γ S k η' ρ η :=
  ⟨h.1, fun x hx => h.2 x (hST hx)⟩

theorem CloseAgree.cons {Γ : List V} {S : Finset V} {k : ℕ} {η' η : ℕ → α} {ρ : V → α}
    (h : CloseAgree Γ S k η' ρ η) (a : α) :
    CloseAgree Γ S (k + 1) (DB.cons a η') ρ (DB.cons a η) := by
  refine ⟨fun i hi => ?_, fun x hx => ?_⟩
  · cases i with
    | zero => rfl
    | succ i => exact h.1 i (by omega)
  · rw [show k + 1 + idx x Γ = (k + idx x Γ) + 1 by omega]
    exact h.2 x hx

theorem Val.eval_close (m : Model F M α) {Γ : List V} {k : ℕ} {η' η : ℕ → α} {ρ : V → α} :
    ∀ a : LN.Val V, a.WS k → CloseAgree Γ a.fv k η' ρ η →
      (a.close Γ k).eval m η' = a.eval m ρ η
  | .fvar x, _, h => h.2 x (by simp [LN.Val.fv])
  | .bvar i, hw, h => h.1 i hw
  | .unit, _, _ => rfl
  | .pair a b, hw, h => by
      simp only [LN.Val.close, DB.Val.eval, LN.Val.eval]
      rw [Val.eval_close m a hw.1 (h.mono (by simp [LN.Val.fv])),
        Val.eval_close m b hw.2 (h.mono (by simp [LN.Val.fv]))]

theorem Op.eval_close [Monad M] (m : Model F M α) {Γ : List V} {k : ℕ} {η' η : ℕ → α}
    {ρ : V → α} (o : LN.Op V F) (hw : o.WS k) (h : CloseAgree Γ o.fv k η' ρ η) :
    (o.close Γ k).eval m η' = o.eval m ρ η := by
  cases o with
  | val a => exact congrArg pure (Val.eval_close m a hw h)
  | app f a => exact congrArg (m.app f) (Val.eval_close m a hw h)
  | inl a => exact congrArg (fun v => pure (m.inl v)) (Val.eval_close m a hw h)
  | inr a => exact congrArg (fun v => pure (m.inr v)) (Val.eval_close m a hw h)
  | abort a => exact congrArg m.abort (Val.eval_close m a hw h)

theorem Region.eval_close [Monad M] [DecidableEq L] (m : Model F M α) {Γ : List V} :
    ∀ (d : LN.Region V L F) {k : ℕ} {η' η : ℕ → α} {ρ : V → α}, d.WS k →
      CloseAgree Γ d.fv k η' ρ η → (d.close Γ k).eval m η' = d.eval m ρ η
  | .br _ a, _, _, _, _, hw, h => by
      simp only [LN.Region.close, DB.Region.eval, LN.Region.eval, Val.eval_close m a hw h]
  | .let1 o r, _, _, _, _, hw, h => by
      simp only [LN.Region.close, DB.Region.eval, LN.Region.eval]
      rw [Op.eval_close m o hw.1 (h.mono (by simp [LN.Region.fv]))]
      congr 1; funext a
      exact Region.eval_close m r hw.2 ((h.mono (by simp [LN.Region.fv])).cons a)
  | .let2 o r, _, _, _, _, hw, h => by
      simp only [LN.Region.close, DB.Region.eval, LN.Region.eval]
      rw [Op.eval_close m o hw.1 (h.mono (by simp [LN.Region.fv]))]
      congr 1; funext p
      exact Region.eval_close m r hw.2 (((h.mono (by simp [LN.Region.fv])).cons p.1).cons p.2)
  | .case o r s, _, _, _, _, hw, h => by
      simp only [LN.Region.close, DB.Region.eval, LN.Region.eval]
      rw [Op.eval_close m o hw.1 (h.mono (by simp [LN.Region.fv]))]
      have hr := h.mono (S := r.fv) (fun z hz => by simp [LN.Region.fv, hz])
      have hs := h.mono (S := s.fv) (fun z hz => by simp [LN.Region.fv, hz])
      congr 1; funext c
      cases c with
      | inl a => exact Region.eval_close m r hw.2.1 (hr.cons a)
      | inr b => exact Region.eval_close m s hw.2.2 (hs.cons b)
  | .join r ℓ t, _, _, _, _, hw, h => by
      simp only [LN.Region.close, DB.Region.eval, LN.Region.eval]
      rw [Region.eval_close m r hw.1 (h.mono (by simp [LN.Region.fv]))]
      congr 1; funext e
      split
      · exact Region.eval_close m t hw.2 ((h.mono (by simp [LN.Region.fv])).cons e.2)
      · rfl

/-- **Adequacy of `toLN`**: the locally nameless reading of a named region has its lexical
semantics, whatever the (unused) bound environment. -/
theorem Region.eval_toLN [Monad M] [DecidableEq L] (m : Model F M α) (r : Region V L F)
    (ρ : V → α) (η : ℕ → α) : (r.toLN []).eval m ρ η = r.evalSSA m ρ := by
  classical
  let Γ := r.fv.toList
  have hΓ : r.fv ⊆ Γ.toFinset := by intro z hz; simp [Γ, hz]
  have htri := Region.close_toLN Γ r []
  simp only [List.length_nil, List.nil_append] at htri
  rw [← Region.eval_close m (r.toLN []) (Γ := Γ) (k := 0) (η' := env Γ ρ m.unit)
    (Region.ws_toLN r []) ⟨fun i hi => absurd hi (Nat.not_lt_zero i), fun x hx => ?_⟩,
    htri, Region.eval_toDB_env m r hΓ ρ m.unit]
  rw [Nat.zero_add]
  exact Silmaril.SSA.LambdaRTL.agree_env Γ ρ m.unit x (by simpa using hΓ (Region.fv_toLN r [] x hx).1)

end CloseEval

/-! ## Round trip `toLN ∘ ofLN = id` -/

section RoundTrip

variable [DecidableEq V] (S : Supply V)

theorem Val.toLN_ofLN (d : V) {A : Finset V} {B : List V} (hB : B.Nodup)
    (hAB : ∀ x ∈ B, x ∉ A) : ∀ a : LN.Val V, a.WS B.length → a.fv ⊆ A →
      (a.ofLN d B).toLN B = a
  | .fvar x, _, hA => by
      have hx : x ∈ A := hA (by simp [LN.Val.fv])
      have : x ∉ B := fun h => hAB x h hx
      simp [LN.Val.ofLN, Val.toLN, this]
  | .bvar i, hw, _ => by
      have hmem := Silmaril.Proofs.SSA.LambdaRTL.Nameless.getD_mem d B i hw
      have hidx := Silmaril.Proofs.SSA.LambdaRTL.Nameless.idx_getD d B i hB hw
      simp only [LN.Val.ofLN, Val.toLN, hmem, ite_true, hidx]
  | .unit, _, _ => rfl
  | .pair a b, hw, hA => by
      simp only [LN.Val.ofLN, Val.toLN]
      rw [Val.toLN_ofLN d hB hAB a hw.1 (fun z hz => hA (by simp [LN.Val.fv, hz])),
        Val.toLN_ofLN d hB hAB b hw.2 (fun z hz => hA (by simp [LN.Val.fv, hz]))]

theorem Op.toLN_ofLN (d : V) {A : Finset V} {B : List V} (hB : B.Nodup)
    (hAB : ∀ x ∈ B, x ∉ A) (o : LN.Op V F) (hw : o.WS B.length) (hA : o.fv ⊆ A) :
    (o.ofLN d B).toLN B = o := by
  cases o with
  | val a => exact congrArg LN.Op.val (Val.toLN_ofLN d hB hAB a hw hA)
  | app f a => exact congrArg (LN.Op.app f) (Val.toLN_ofLN d hB hAB a hw hA)
  | inl a => exact congrArg LN.Op.inl (Val.toLN_ofLN d hB hAB a hw hA)
  | inr a => exact congrArg LN.Op.inr (Val.toLN_ofLN d hB hAB a hw hA)
  | abort a => exact congrArg LN.Op.abort (Val.toLN_ofLN d hB hAB a hw hA)

theorem fresh_inv {A : Finset V} {B : List V} (hB : B.Nodup) (hAB : ∀ x ∈ B, x ∉ A)
    (s : Finset V) (hs : A ∪ B.toFinset ⊆ s) :
    (S.fresh s :: B).Nodup ∧ ∀ x ∈ S.fresh s :: B, x ∉ A := by
  have hf := S.fresh_not_mem s
  refine ⟨List.nodup_cons.2 ⟨fun h => hf (hs (by simp [h])), hB⟩, fun x hx => ?_⟩
  rcases List.mem_cons.1 hx with rfl | hx
  · exact fun h => hf (hs (by simp [h]))
  · exact hAB x hx

theorem Region.toLN_ofLN {A : Finset V} :
    ∀ (e : LN.Region V L F) (B : List V), B.Nodup → (∀ x ∈ B, x ∉ A) →
      e.WS B.length → e.fv ⊆ A → (e.ofLN S A B).toLN B = e
  | .br _ a, B, hB, hAB, hw, hA => by
      simp only [LN.Region.ofLN, Region.toLN]; rw [Val.toLN_ofLN _ hB hAB a hw hA]
  | .let1 o r, B, hB, hAB, hw, hA => by
      obtain ⟨h1, h2⟩ := fresh_inv S hB hAB (A ∪ B.toFinset) le_rfl
      simp only [LN.Region.ofLN, Region.toLN]
      rw [Op.toLN_ofLN _ hB hAB o hw.1 (fun z hz => hA (by simp [LN.Region.fv, hz])),
        Region.toLN_ofLN r _ h1 h2 (by simpa using hw.2)
          (fun z hz => hA (by simp [LN.Region.fv, hz]))]
  | .let2 o r, B, hB, hAB, hw, hA => by
      obtain ⟨h1, h2⟩ := fresh_inv S hB hAB (A ∪ B.toFinset) le_rfl
      obtain ⟨h3, h4⟩ := fresh_inv S h1 h2 (insert (S.fresh (A ∪ B.toFinset)) (A ∪ B.toFinset))
        (by intro z hz; simp only [List.toFinset_cons, Finset.mem_union, Finset.mem_insert] at hz ⊢; tauto)
      simp only [LN.Region.ofLN, Region.toLN]
      rw [Op.toLN_ofLN _ hB hAB o hw.1 (fun z hz => hA (by simp [LN.Region.fv, hz])),
        Region.toLN_ofLN r _ h3 h4 (by simpa using hw.2)
          (fun z hz => hA (by simp [LN.Region.fv, hz]))]
  | .case o r s, B, hB, hAB, hw, hA => by
      obtain ⟨h1, h2⟩ := fresh_inv S hB hAB (A ∪ B.toFinset) le_rfl
      simp only [LN.Region.ofLN, Region.toLN]
      rw [Op.toLN_ofLN _ hB hAB o hw.1 (fun z hz => hA (by simp [LN.Region.fv, hz])),
        Region.toLN_ofLN r _ h1 h2 (by simpa using hw.2.1)
          (fun z hz => hA (by simp [LN.Region.fv, hz])),
        Region.toLN_ofLN s _ h1 h2 (by simpa using hw.2.2)
          (fun z hz => hA (by simp [LN.Region.fv, hz]))]
  | .join r ℓ t, B, hB, hAB, hw, hA => by
      obtain ⟨h1, h2⟩ := fresh_inv S hB hAB (A ∪ B.toFinset) le_rfl
      simp only [LN.Region.ofLN, Region.toLN]
      rw [Region.toLN_ofLN r B hB hAB hw.1 (fun z hz => hA (by simp [LN.Region.fv, hz])),
        Region.toLN_ofLN t _ h1 h2 (by simpa using hw.2)
          (fun z hz => hA (by simp [LN.Region.fv, hz]))]

end RoundTrip

end Silmaril.Proofs.SSA.LambdaRTL.LocallyNameless

namespace Silmaril.Proofs.SSA.LambdaRTL.LocallyNameless

open Silmaril.SSA.LambdaRTL

universe v₂ w₂

variable {V L : Type w₂} {F : Type v₂} [DecidableEq V]

/-! ## Injectivity of closing (α-converse) -/

theorem idx_inj {Γ : List V} {x y : V} (hx : x ∈ Γ) (hy : y ∈ Γ) (h : idx x Γ = idx y Γ) :
    x = y := by
  have h1 := Silmaril.Proofs.SSA.LambdaRTL.Nameless.getElem?_idx x Γ hx
  have h2 := Silmaril.Proofs.SSA.LambdaRTL.Nameless.getElem?_idx y Γ hy
  rw [h] at h1
  exact Option.some.inj (h1.symm.trans h2)

theorem Val.close_inj {Γ : List V} {k : ℕ} :
    ∀ (a b : LN.Val V), a.WS k → b.WS k → (∀ z ∈ a.fv, z ∈ Γ) → (∀ z ∈ b.fv, z ∈ Γ) →
      a.close Γ k = b.close Γ k → a = b
  | .fvar x, .fvar y, _, _, ha, hb, h => by
      simp only [LN.Val.close, DB.Val.var.injEq, Nat.add_left_cancel_iff] at h
      rw [idx_inj (ha x (by simp [LN.Val.fv])) (hb y (by simp [LN.Val.fv])) h]
  | .fvar x, .bvar j, _, wb, _, _, h => by
      simp only [LN.Val.close, DB.Val.var.injEq] at h
      simp only [LN.Val.WS] at wb; omega
  | .bvar i, .fvar y, wa, _, _, _, h => by
      simp only [LN.Val.close, DB.Val.var.injEq] at h
      simp only [LN.Val.WS] at wa; omega
  | .bvar i, .bvar j, _, _, _, _, h => by
      simp only [LN.Val.close, DB.Val.var.injEq] at h; rw [h]
  | .unit, .unit, _, _, _, _, _ => rfl
  | .pair a₁ a₂, .pair b₁ b₂, wa, wb, ha, hb, h => by
      simp only [LN.Val.close, DB.Val.pair.injEq] at h
      rw [Val.close_inj a₁ b₁ wa.1 wb.1 (fun z hz => ha z (by simp [LN.Val.fv, hz]))
          (fun z hz => hb z (by simp [LN.Val.fv, hz])) h.1,
        Val.close_inj a₂ b₂ wa.2 wb.2 (fun z hz => ha z (by simp [LN.Val.fv, hz]))
          (fun z hz => hb z (by simp [LN.Val.fv, hz])) h.2]
  | .fvar _, .unit, _, _, _, _, h | .fvar _, .pair _ _, _, _, _, _, h
  | .bvar _, .unit, _, _, _, _, h | .bvar _, .pair _ _, _, _, _, _, h
  | .unit, .fvar _, _, _, _, _, h | .unit, .bvar _, _, _, _, _, h | .unit, .pair _ _, _, _, _, _, h
  | .pair _ _, .fvar _, _, _, _, _, h | .pair _ _, .bvar _, _, _, _, _, h
  | .pair _ _, .unit, _, _, _, _, h => by simp [LN.Val.close] at h

theorem Op.close_inj {Γ : List V} {k : ℕ} (o p : LN.Op V F) (wo : o.WS k) (wp : p.WS k)
    (ho : ∀ z ∈ o.fv, z ∈ Γ) (hp : ∀ z ∈ p.fv, z ∈ Γ) (h : o.close Γ k = p.close Γ k) :
    o = p := by
  cases o <;> cases p <;> simp only [LN.Op.close, reduceCtorEq, DB.Op.val.injEq,
    DB.Op.app.injEq, DB.Op.inl.injEq, DB.Op.inr.injEq, DB.Op.abort.injEq] at h
  case val.val a b => exact congrArg LN.Op.val (Val.close_inj a b wo wp ho hp h)
  case app.app f a g b => rw [h.1, Val.close_inj a b wo wp ho hp h.2]
  case inl.inl a b => exact congrArg LN.Op.inl (Val.close_inj a b wo wp ho hp h)
  case inr.inr a b => exact congrArg LN.Op.inr (Val.close_inj a b wo wp ho hp h)
  case abort.abort a b => exact congrArg LN.Op.abort (Val.close_inj a b wo wp ho hp h)

theorem Region.close_inj {Γ : List V} :
    ∀ (d e : LN.Region V L F) {k : ℕ}, d.WS k → e.WS k → (∀ z ∈ d.fv, z ∈ Γ) →
      (∀ z ∈ e.fv, z ∈ Γ) → d.close Γ k = e.close Γ k → d = e
  | .br ℓ a, .br ℓ' b, _, wa, wb, ha, hb, h => by
      simp only [LN.Region.close, DB.Region.br.injEq] at h
      rw [h.1, Val.close_inj a b wa wb ha hb h.2]
  | .let1 o r, .let1 p s, _, wa, wb, ha, hb, h => by
      simp only [LN.Region.close, DB.Region.let1.injEq] at h
      rw [Op.close_inj o p wa.1 wb.1 (fun z hz => ha z (by simp [LN.Region.fv, hz]))
          (fun z hz => hb z (by simp [LN.Region.fv, hz])) h.1,
        Region.close_inj r s wa.2 wb.2 (fun z hz => ha z (by simp [LN.Region.fv, hz]))
          (fun z hz => hb z (by simp [LN.Region.fv, hz])) h.2]
  | .let2 o r, .let2 p s, _, wa, wb, ha, hb, h => by
      simp only [LN.Region.close, DB.Region.let2.injEq] at h
      rw [Op.close_inj o p wa.1 wb.1 (fun z hz => ha z (by simp [LN.Region.fv, hz]))
          (fun z hz => hb z (by simp [LN.Region.fv, hz])) h.1,
        Region.close_inj r s wa.2 wb.2 (fun z hz => ha z (by simp [LN.Region.fv, hz]))
          (fun z hz => hb z (by simp [LN.Region.fv, hz])) h.2]
  | .case o r r', .case p s s', _, wa, wb, ha, hb, h => by
      simp only [LN.Region.close, DB.Region.case.injEq] at h
      rw [Op.close_inj o p wa.1 wb.1 (fun z hz => ha z (by simp [LN.Region.fv, hz]))
          (fun z hz => hb z (by simp [LN.Region.fv, hz])) h.1,
        Region.close_inj r s wa.2.1 wb.2.1 (fun z hz => ha z (by simp [LN.Region.fv, hz]))
          (fun z hz => hb z (by simp [LN.Region.fv, hz])) h.2.1,
        Region.close_inj r' s' wa.2.2 wb.2.2 (fun z hz => ha z (by simp [LN.Region.fv, hz]))
          (fun z hz => hb z (by simp [LN.Region.fv, hz])) h.2.2]
  | .join r ℓ t, .join s ℓ' u, _, wa, wb, ha, hb, h => by
      simp only [LN.Region.close, DB.Region.join.injEq] at h
      rw [h.2.1, Region.close_inj r s wa.1 wb.1 (fun z hz => ha z (by simp [LN.Region.fv, hz]))
          (fun z hz => hb z (by simp [LN.Region.fv, hz])) h.1,
        Region.close_inj t u wa.2 wb.2 (fun z hz => ha z (by simp [LN.Region.fv, hz]))
          (fun z hz => hb z (by simp [LN.Region.fv, hz])) h.2.2]
  | .br .., .let1 .., _, _, _, _, _, h | .br .., .let2 .., _, _, _, _, _, h
  | .br .., .case .., _, _, _, _, _, h | .br .., .join .., _, _, _, _, _, h
  | .let1 .., .br .., _, _, _, _, _, h | .let1 .., .let2 .., _, _, _, _, _, h
  | .let1 .., .case .., _, _, _, _, _, h | .let1 .., .join .., _, _, _, _, _, h
  | .let2 .., .br .., _, _, _, _, _, h | .let2 .., .let1 .., _, _, _, _, _, h
  | .let2 .., .case .., _, _, _, _, _, h | .let2 .., .join .., _, _, _, _, _, h
  | .case .., .br .., _, _, _, _, _, h | .case .., .let1 .., _, _, _, _, _, h
  | .case .., .let2 .., _, _, _, _, _, h | .case .., .join .., _, _, _, _, _, h
  | .join .., .br .., _, _, _, _, _, h | .join .., .let1 .., _, _, _, _, _, h
  | .join .., .let2 .., _, _, _, _, _, h | .join .., .case .., _, _, _, _, _, h => by
      simp [LN.Region.close] at h

/-- **α-converse**: α-equivalent regions (free names in `Γ`) have equal locally nameless forms. -/
theorem Region.toLN_eq_of_alphaEq {Γ : List V} {r r' : Region V L F}
    (hr : r.fv ⊆ Γ.toFinset) (hr' : r'.fv ⊆ Γ.toFinset) (h : r.AlphaEq Γ r') :
    r.toLN [] = r'.toLN [] := by
  have h1 := Region.close_toLN Γ r []
  have h2 := Region.close_toLN Γ r' []
  simp only [List.length_nil, List.nil_append] at h1 h2
  have hc : (r.toLN []).close Γ 0 = (r'.toLN []).close Γ 0 := by
    rw [h1, h2]; exact h
  refine Region.close_inj _ _ (Region.ws_toLN r []) (Region.ws_toLN r' []) ?_ ?_ hc
  · intro z hz; simpa using hr (Region.fv_toLN r [] z hz).1
  · intro z hz; simpa using hr' (Region.fv_toLN r' [] z hz).1

end Silmaril.Proofs.SSA.LambdaRTL.LocallyNameless
