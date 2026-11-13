module

public import Silmaril.Proofs.Wasm.Examples.LRAT.Rules
public import Silmaril.Logic.SAT.LRAT.Thms

@[expose] public section

/-!
# The LRAT checker's memory: literals, words and entries

* literals in range (`ValidLit`): their value addresses `litAddr x` lie in `[4, 8192)`, distinct
  literals have disjoint words, `negAddr x = litAddr (-x)`, negation keeps the range and is the
  integer negation (`toInt_neg`), and the literal is a nonzero integer;
* words: reading after writing (`wd_wr_same`, `wd_wr_ne`), the word lists `words` after writes
  outside them (`words_wr_out`), appending a word (`words_succ`);
* clause entries after writes to the arena above `cstart`, to the literal values, or to the
  tables of another id.

A Silmaril addition.
-/

namespace Silmaril.Wasm.Examples.LRAT

open Silmaril.Logic.SAT

variable {B : ByteArray}

/-! ## Literals -/

theorem ValidLit.addr {x : BitVec 32} (h : ValidLit x) : 4 ≤ litAddr x ∧ litAddr x + 4 ≤ startBase := by
  unfold ValidLit at h; unfold litAddr startBase; bv_omega

theorem ValidLit.neg {x : BitVec 32} (h : ValidLit x) : ValidLit (-x) := by
  unfold ValidLit at *; constructor <;> bv_omega

theorem negAddr_eq (x : BitVec 32) : negAddr x = litAddr (-x) := by
  unfold litAddr negAddr; bv_omega

theorem ValidLit.disj {x y : BitVec 32} (hx : ValidLit x) (hy : ValidLit y) (hne : x ≠ y) :
    litAddr x + 4 ≤ litAddr y ∨ litAddr y + 4 ≤ litAddr x := by
  unfold ValidLit at *; unfold litAddr; bv_omega

theorem ValidLit.ne_neg {x : BitVec 32} (h : ValidLit x) : x ≠ -x := by
  unfold ValidLit at h; bv_omega

theorem ValidLit.toInt_neg {x : BitVec 32} (h : ValidLit x) : (-x).toInt = - x.toInt := by
  unfold ValidLit at h
  rw [BitVec.toInt_neg_of_ne_intMin]
  intro hc; subst hc; simp at h

theorem ValidLit.toInt_ne {x : BitVec 32} (h : ValidLit x) : x.toInt ≠ 0 := by
  intro hc
  exact h.1 (BitVec.toInt_inj.1 (by simpa using hc))

/-- The value of the negation of a literal in range. -/
theorem ValidLit.eval_neg {x : BitVec 32} (h : ValidLit x) (τ : Assignment) :
    Lit.eval τ (-x).toInt = !Lit.eval τ x.toInt := by
  rw [h.toInt_neg]
  exact Lit.eval_neg τ h.toInt_ne

/-! ## Words -/

theorem words_succ (p n : Nat) : words B p (n + 1) = words B p n ++ [wd B (p + 4 * n)] := by
  simp [words, List.range_succ]

theorem words_zero (p : Nat) : words B p 0 = [] := rfl

theorem length_words (p n : Nat) : (words B p n).length = n := by simp [words]

theorem mem_words {w : BitVec 32} {p n : Nat} :
    w ∈ words B p n ↔ ∃ k < n, wd B (p + 4 * k) = w := by
  simp [words]

/-- Writing outside a word list leaves it unchanged. -/
theorem words_wr_out {a p n : Nat} (v : BitVec 32) (hs : B.size = memSize) (ha : a + 4 ≤ memSize)
    (hd : a + 4 ≤ p ∨ p + 4 * n ≤ a) : words (wr B a v) p n = words B p n := by
  unfold words
  refine List.map_congr_left fun k hk => ?_
  have hk' : k < n := List.mem_range.1 hk
  exact wd_wr_ne v (by rw [hs]; exact ha) (by omega)

end Silmaril.Wasm.Examples.LRAT
