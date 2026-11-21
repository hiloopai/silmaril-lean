module

public import Silmaril.X86.Concurrency.Cir.Rc11.Defs

/-!
# RC11 on CIR: bitmask relations

The bitmask primitives of the RC11 decision procedure mean what they
say: `get_rel` (a relation built from a function), `get_or`/`get_and` (union, intersection),
`get_seqR` (composition, row by row), `tcN_spec` (the fixpoint iteration computes the transitive
closure), and the evaluation helpers are identities (`force_eq`, `forceL_eq`, ...).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Rc11

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Rc11 (force forceL forceRf forceCo forceLL maskK rowsK rel row joinK seqR anyLt allLt tcLoop tcN ofMask)
open Silmaril.X86.MemoryModel.Axiomatic (BRel)

/-! ## Evaluation helpers are identities -/

theorem force_eq {α : Sort _} (v : Nat) (k : Nat → α) : force v k = k v := by
  cases v <;> rfl

theorem forceL_eq {α : Sort _} : ∀ (l : List Nat) (k : List Nat → α), forceL l k = k l
  | [], _ => rfl
  | a :: l, k => by simp only [forceL, force_eq, forceL_eq l]

theorem forceRf_eq {α : Sort _} :
    ∀ (l : List (Nat × Option Nat)) (k : List (Nat × Option Nat) → α), forceRf l k = k l
  | [], _ => rfl
  | (y, none) :: l, k => by simp only [forceRf, force_eq, forceRf_eq l]
  | (y, some w) :: l, k => by simp only [forceRf, force_eq, forceRf_eq l]

theorem forceCo_eq {α : Sort _} :
    ∀ (l : List (Nat × List Nat)) (k : List (Nat × List Nat) → α), forceCo l k = k l
  | [], _ => rfl
  | (y, o) :: l, k => by simp only [forceCo, force_eq, forceL_eq, forceCo_eq l]

theorem forceLL_eq {α β : Type} {f : List α → (List α → β) → β} (hf : ∀ a k, f a k = k a) :
    ∀ (l : List (List α)) (k : List (List α) → β), forceLL f l k = k l
  | [], _ => rfl
  | a :: l, k => by simp only [forceLL, hf, forceLL_eq hf l]

/-! ## Masks -/

theorem testBit_maskK (g : Nat → Bool) (b : Nat) :
    ∀ k, (maskK g k).testBit b = (decide (b < k) && g b)
  | 0 => by simp [maskK]
  | k + 1 => by
    rw [maskK, Nat.testBit_or, testBit_maskK g b k]
    by_cases hk : g k
    · simp only [hk, ite_true, Nat.testBit_two_pow]
      by_cases hb : b = k
      · subst hb; simp [hk]
      · have : (k = b) = False := propext ⟨fun h => hb h.symm, False.elim⟩
        simp only [this, decide_false, Bool.or_false]
        by_cases hbk : b < k
        · simp [hbk, show b < k + 1 by omega]
        · simp [hbk, show ¬ b < k + 1 by omega]
    · simp only [hk, Bool.false_eq_true, ite_false, Nat.zero_testBit, Bool.or_false]
      by_cases hb : b = k
      · subst hb; simp [hk]
      · by_cases hbk : b < k
        · simp [hbk, show b < k + 1 by omega]
        · simp [hbk, show ¬ b < k + 1 by omega]

theorem testBit_rowsK (n : Nat) (g : Nat → Nat) {a b : Nat} (hb : b < n) :
    ∀ k, (rowsK n g k).testBit (a * n + b) = (decide (a < k) && (g a).testBit b)
  | 0 => by simp [rowsK]
  | k + 1 => by
    rw [rowsK, Nat.testBit_or, testBit_rowsK n g hb k, Nat.testBit_shiftLeft,
      Nat.testBit_mod_two_pow]
    rcases Nat.lt_trichotomy a k with h | h | h
    · have h1 : a * n + n ≤ k * n := by
        have := Nat.mul_le_mul_right n (show a + 1 ≤ k by omega); simpa [Nat.add_mul] using this
      simp [h, show a < k + 1 by omega, show ¬ (a * n + b ≥ k * n) by omega]
    · subst h
      simp [Nat.add_sub_cancel_left, hb]
    · have h1 : k * n + n ≤ a * n := by
        have := Nat.mul_le_mul_right n (show k + 1 ≤ a by omega); simpa [Nat.add_mul] using this
      simp [show ¬ a < k by omega, show ¬ a < k + 1 by omega, show a * n + b ≥ k * n by omega,
        show ¬ (a * n + b - k * n < n) by omega]

/-- **A relation mask means its function.** -/
theorem get_rel {n : Nat} (f : Nat → Nat → Bool) {a b : Nat} (ha : a < n) (hb : b < n) :
    Rc11.get n (rel n f) a b = f a b := by
  unfold Rc11.get rel
  rw [testBit_rowsK n _ hb, testBit_maskK]
  simp [ha, hb]

theorem get_or (n T U a b : Nat) : Rc11.get n (T ||| U) a b = (Rc11.get n T a b || Rc11.get n U a b) :=
  Nat.testBit_or _ _ _

theorem get_and (n T U a b : Nat) : Rc11.get n (T &&& U) a b = (Rc11.get n T a b && Rc11.get n U a b) :=
  Nat.testBit_and _ _ _

theorem testBit_row {n T a b : Nat} (hb : b < n) : (row n T a).testBit b = Rc11.get n T a b := by
  unfold row Rc11.get
  rw [Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
  simp [hb]

theorem testBit_joinK {n T U a b : Nat} (hb : b < n) :
    ∀ k, (joinK n T U a k).testBit b = true ↔ ∃ c < k, Rc11.get n T a c = true ∧ Rc11.get n U c b = true
  | 0 => by simp [joinK]
  | k + 1 => by
    rw [joinK, Nat.testBit_or, Bool.or_eq_true, testBit_joinK hb k]
    constructor
    · rintro (⟨c, hc, h⟩ | h)
      · exact ⟨c, by omega, h⟩
      · by_cases hk : Rc11.get n T a k = true
        · rw [ite_eq_left hk, testBit_row hb] at h; exact ⟨k, by omega, hk, h⟩
        · rw [ite_eq_right hk] at h; simp at h
    · rintro ⟨c, hc, h1, h2⟩
      by_cases hck : c < k
      · exact Or.inl ⟨c, hck, h1, h2⟩
      · have : c = k := by omega
        subst this
        exact Or.inr (by rw [ite_eq_left h1, testBit_row hb]; exact h2)

/-- **Composition is composition.** -/
theorem get_seqR {n T U a b : Nat} (ha : a < n) (hb : b < n) :
    Rc11.get n (seqR n T U) a b = true ↔ ∃ c < n, Rc11.get n T a c = true ∧ Rc11.get n U c b = true := by
  unfold seqR
  conv => lhs; unfold Rc11.get
  rw [testBit_rowsK n _ hb]
  simp only [ha, decide_true, Bool.true_and]
  exact testBit_joinK hb n

theorem anyLt_iff {n : Nat} {p : Nat → Bool} : anyLt n p = true ↔ ∃ a < n, p a = true := by
  simp [anyLt]

theorem allLt_iff {n : Nat} {p : Nat → Bool} : allLt n p = true ↔ ∀ a < n, p a = true := by
  simp [allLt]

/-! ## Transitive closure -/

/-- The relation of a mask on `Fin n`, as a proposition. -/
def G (n T : Nat) (a b : Fin n) : Prop := Rc11.get n T a.val b.val = true

theorem tcLoop_spec {n R : Nat} :
    ∀ k c d, tcLoop n k c = some d →
      (∀ a b : Fin n, G n R a b → G n c a b) →
      (∀ a b : Fin n, G n c a b → Relation.TransGen (G n R) a b) →
      (∀ a b : Fin n, G n d a b ↔ Relation.TransGen (G n R) a b)
  | 0, c, d, h, _, _ => by simp [tcLoop] at h
  | k + 1, c, d, h, hR, hc => by
    simp only [tcLoop, force_eq] at h
    split at h
    · rename_i heq
      cases h
      have hfix : (c ||| seqR n c c) = c := by simpa using heq
      intro a b
      refine ⟨hc a b, fun ht => ?_⟩
      induction ht with
      | single h => exact hR _ _ h
      | @tail b' c' _ hbc ih =>
        have : Rc11.get n (seqR n c c) a.val c'.val = true :=
          (get_seqR a.isLt c'.isLt).mpr ⟨b'.val, b'.isLt, ih, hR _ _ hbc⟩
        unfold G
        rw [← hfix, get_or, this, Bool.or_true]
    · refine tcLoop_spec k _ d h (fun a b hab => ?_) (fun a b hab => ?_)
      · unfold G; rw [get_or, hR a b hab, Bool.true_or]
      · unfold G at hab
        rw [get_or, Bool.or_eq_true] at hab
        rcases hab with hab | hab
        · exact hc a b hab
        · obtain ⟨m, hm, h1, h2⟩ := (get_seqR a.isLt b.isLt).mp hab
          exact Relation.TransGen.trans (hc a ⟨m, hm⟩ h1) (hc ⟨m, hm⟩ b h2)

/-- **The closure computed by `tcN` is the transitive closure.** -/
theorem tcN_spec {n R c : Nat} (h : tcN n R = some c) (a b : Fin n) :
    G n c a b ↔ Relation.TransGen (G n R) a b := by
  unfold tcN at h
  rw [force_eq] at h
  exact tcLoop_spec _ _ _ h (fun _ _ h => h) (fun _ _ h => Relation.TransGen.single h) a b

/-- `ofMask` and `G` agree. -/
theorem ofMask_holds (n T : Nat) (a b : Fin n) : (ofMask n T).Holds a b ↔ G n T a b := Iff.rfl

end Silmaril.Proofs.X86.Concurrency.Cir.Rc11
