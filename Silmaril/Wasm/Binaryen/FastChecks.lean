module

public import Silmaril.Wasm.Binaryen.Effects

@[expose] public section

/-! # Allocation-free forms of label and effect checks

Several passes ask, for a whole body or for every block, whether its lowering has a
free branch target (`(BExpr.labelsList body).isEmpty`) or read a few flags of its
effect summary (`(effectsList body).any`). Both build lists proportional to the body
on every query. The traversals here answer the same questions with short-circuiting
Boolean recursion, and are proved equal to the original expressions, so a pass can
register a fast form of its check with `@[csimp]` without changing its outputs.
-/

namespace Silmaril.Wasm.Binaryen

/-! ## Free branch targets -/

mutual
/-- Does the lowering of a tree, seen under `k` enclosing labels, branch to a label at
depth at least `k` (a free target of the tree once the `k` labels are bound)? -/
def BExpr.escE (k : Nat) : BExpr → Bool
  | .op i args => BExpr.escL k args || (instrLabels i).any (k ≤ ·)
  | .block _ b => BExpr.escL (k + 1) b
  | .loop _ b => BExpr.escL (k + 1) b
  | .if_ _ c t e => BExpr.escL k c || (BExpr.escL (k + 1) t || BExpr.escL (k + 1) e)
  | .tryTable _ cs b => (cs.map Catch.label).any (k ≤ ·) || BExpr.escL (k + 1) b
/-- `BExpr.escE` of a sequence. -/
def BExpr.escL (k : Nat) : List BExpr → Bool
  | [] => false
  | e :: es => BExpr.escE k e || BExpr.escL k es
end

private theorem exists_unbind_iff {L : List Nat} {k : Nat} :
    (∃ l ∈ unbind L, k ≤ l) ↔ ∃ l ∈ L, k + 1 ≤ l := by
  constructor
  · rintro ⟨l, hl, hk⟩
    exact ⟨l + 1, mem_unbind.mp hl, by omega⟩
  · rintro ⟨l, hl, hk⟩
    refine ⟨l - 1, mem_unbind.mpr ?_, by omega⟩
    rwa [show l - 1 + 1 = l by omega]

private theorem exists_mem_append' {a b : List Nat} {p : Nat → Prop} :
    (∃ l ∈ a ++ b, p l) ↔ (∃ l ∈ a, p l) ∨ ∃ l ∈ b, p l := by
  simp only [List.mem_append]
  constructor
  · rintro ⟨l, hl | hl, h⟩
    · exact .inl ⟨l, hl, h⟩
    · exact .inr ⟨l, hl, h⟩
  · rintro (⟨l, hl, h⟩ | ⟨l, hl, h⟩)
    · exact ⟨l, .inl hl, h⟩
    · exact ⟨l, .inr hl, h⟩

mutual
theorem BExpr.escE_iff (k : Nat) : ∀ e : BExpr,
    BExpr.escE k e = true ↔ ∃ l ∈ BExpr.labelsFast e, k ≤ l
  | .op i args => by
      simp only [BExpr.escE, BExpr.labelsFast, Bool.or_eq_true, List.any_eq_true,
        decide_eq_true_eq, List.mem_append, BExpr.escL_iff k args]
      constructor
      · rintro (⟨l, hl, h⟩ | ⟨l, hl, h⟩)
        · exact ⟨l, .inl hl, h⟩
        · exact ⟨l, .inr hl, h⟩
      · rintro ⟨l, hl | hl, h⟩
        · exact .inl ⟨l, hl, h⟩
        · exact .inr ⟨l, hl, h⟩
  | .block _ b => by
      rw [BExpr.escE, BExpr.labelsFast, exists_unbind_iff, BExpr.escL_iff (k + 1) b]
  | .loop _ b => by
      rw [BExpr.escE, BExpr.labelsFast, exists_unbind_iff, BExpr.escL_iff (k + 1) b]
  | .if_ _ c t e => by
      simp only [BExpr.escE, BExpr.labelsFast, Bool.or_eq_true, BExpr.escL_iff k c,
        BExpr.escL_iff (k + 1) t, BExpr.escL_iff (k + 1) e]
      rw [exists_mem_append', exists_unbind_iff, exists_mem_append']
  | .tryTable _ cs b => by
      simp only [BExpr.escE, BExpr.labelsFast, Bool.or_eq_true, List.any_eq_true,
        decide_eq_true_eq, BExpr.escL_iff (k + 1) b]
      rw [exists_mem_append', exists_unbind_iff]
theorem BExpr.escL_iff (k : Nat) : ∀ es : List BExpr,
    BExpr.escL k es = true ↔ ∃ l ∈ BExpr.labelsListFast es, k ≤ l
  | [] => by simp [BExpr.escL, BExpr.labelsListFast]
  | e :: es => by
      rw [BExpr.escL, BExpr.labelsListFast, Bool.or_eq_true, BExpr.escE_iff k e,
        BExpr.escL_iff k es, exists_mem_append']
end

/-- A sequence has no free branch target exactly when nothing escapes from depth 0. -/
theorem BExpr.labelsList_isEmpty (es : List BExpr) :
    (BExpr.labelsList es).isEmpty = !BExpr.escL 0 es := by
  rw [← BExpr.labelsListFast_eq]
  cases h : BExpr.escL 0 es
  · have h' : ¬∃ l ∈ BExpr.labelsListFast es, 0 ≤ l := by
      rw [← BExpr.escL_iff]; simp [h]
    cases hl : BExpr.labelsListFast es with
    | nil => rfl
    | cons l _ => exact absurd ⟨l, by simp [hl], Nat.zero_le _⟩ h'
  · obtain ⟨l, hl, -⟩ := (BExpr.escL_iff 0 es).mp h
    cases hL : BExpr.labelsListFast es with
    | nil => simp [hL] at hl
    | cons _ _ => rfl

/-! ## Effect flags -/

/-- Componentwise disjunction of flag triples. -/
def or3 (x y : Bool × Bool × Bool) : Bool × Bool × Bool :=
  (x.1 || y.1, x.2.1 || y.2.1, x.2.2 || y.2.2)

/-- The `any`, `branchesOut` and `calls` flags of an effect summary. -/
def flagsOf (e : Effects) : Bool × Bool × Bool := (e.any, e.branchesOut, e.calls)

mutual
/-- `flagsOf (effects e)`, without the effect lists. -/
def flagsE : BExpr → Bool × Bool × Bool
  | .op i args => or3 (flagsL args) (flagsOf (instrEffects i))
  | .block _ b => flagsL b
  | .loop _ b => flagsL b
  | .if_ _ c t e => or3 (flagsL c) (or3 (flagsL t) (flagsL e))
  | .tryTable .. => (true, false, false)
/-- `flagsOf (effectsList es)`, without the effect lists. -/
def flagsL : List BExpr → Bool × Bool × Bool
  | [] => (false, false, false)
  | e :: es => or3 (flagsE e) (flagsL es)
end

theorem flagsOf_merge (a b : Effects) : flagsOf (a.merge b) = or3 (flagsOf a) (flagsOf b) := rfl

mutual
theorem flagsE_eq : ∀ e : BExpr, flagsE e = flagsOf (effects e)
  | .op i args => by rw [flagsE, effects, flagsOf_merge, flagsL_eq args]
  | .block _ b => by rw [flagsE, effects, flagsL_eq b]; rfl
  | .loop _ b => by rw [flagsE, effects, flagsL_eq b]; rfl
  | .if_ _ c t e => by
      rw [flagsE, effects, flagsOf_merge, flagsL_eq c, flagsL_eq t, flagsL_eq e]
      rfl
  | .tryTable .. => by rw [flagsE, effects]; rfl
theorem flagsL_eq : ∀ es : List BExpr, flagsL es = flagsOf (effectsList es)
  | [] => rfl
  | e :: es => by rw [flagsL, effectsList, flagsOf_merge, flagsE_eq e, flagsL_eq es]
end

end Silmaril.Wasm.Binaryen
