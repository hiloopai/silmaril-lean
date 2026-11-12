module

public import Silmaril.Data.Bitmap.Defs
public import Silmaril.Data.Cells.Thms

/-!
# Bitmaps: setting or clearing one bit is one word store
-/

@[expose] public section

namespace Silmaril.Data.Bitmap

open Silmaril.Data

theorem foldl_pow_add (l : List Nat) (a : Nat) :
    l.foldl (fun acc b => acc + 2 ^ b) a = a + l.foldl (fun acc b => acc + 2 ^ b) 0 := by
  induction l generalizing a with
  | nil => simp
  | cons x xs ih => simp only [List.foldl_cons]; rw [ih, ih (0 + 2 ^ x)]; omega

theorem filter_range_sum_lt (p : Nat → Bool) : ∀ n : Nat,
    ((List.range n).filter p).foldl (fun acc b => acc + 2 ^ b) 0 < 2 ^ n
  | 0 => by simp
  | n + 1 => by
    rw [List.range_succ, List.filter_append, List.foldl_append, foldl_pow_add]
    have := filter_range_sum_lt p n
    have h2 : (List.filter p [n]).foldl (fun acc b => acc + 2 ^ b) 0 ≤ 2 ^ n := by
      simp only [List.filter_cons, List.filter_nil]; split <;> simp
    rw [Nat.pow_succ]; omega

/-- A word's value fits its bytes. -/
theorem word_lt (wbytes : Nat) (f : Nat → Bool) (k : Nat) : word wbytes f k < 256 ^ wbytes := by
  have := filter_range_sum_lt (fun b => f (8 * wbytes * k + b)) (8 * wbytes)
  rw [show (256 : Nat) = 2 ^ 8 from rfl, ← Nat.pow_mul]; exact this

/-- Words other than bit `i`'s are unchanged by setting or clearing it. -/
theorem word_update (wbytes : Nat) (f : Nat → Bool) (i k : Nat) (b : Bool)
    (hk : k ≠ i / (8 * wbytes)) (hw : 0 < wbytes) :
    word wbytes (if b then set f i else clear f i) k = word wbytes f k := by
  unfold word
  congr 1
  apply List.filter_congr
  intro x hx
  have hx' := List.mem_range.1 hx
  have hne : 8 * wbytes * k + x ≠ i := by
    intro e; apply hk; subst e
    rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right _ _ (by omega), Nat.div_eq_of_lt hx']
    simp
  cases b <;> simp [set, clear, hne]

theorem bitmapSet : Task.seplist.bitmapSet := by
  intro base wbytes nwords f v i b hw hi hf
  simp only
  intro c hc
  simp only [frag, List.mem_map, List.mem_range] at hc
  obtain ⟨j, hj, rfl⟩ := hc
  have hk : i / (8 * wbytes) < nwords := by
    rw [Nat.div_lt_iff_lt_mul (by omega)]; rw [Nat.mul_comm] at hi; exact hi
  have hold : ∀ j < nwords, (⟨base + wbytes * j, wbytes, word wbytes f j⟩ : Cell).Holds v :=
    fun j hj => hf _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, rfl⟩)
  refine Cell.holds_storeAll (st := [_]) ?_ (List.pairwise_singleton _ _) ?_
  · intro d hd
    simp only [List.mem_singleton] at hd; subst hd
    exact ⟨word_lt _ _ _, (hold _ hk).2⟩
  · by_cases hjk : j = i / (8 * wbytes)
    · subst hjk; exact .inl (List.mem_singleton_self _)
    · refine .inr ⟨?_, ?_⟩
      · rw [word_update wbytes f i j b hjk hw]; exact hold j hj
      · intro d hd
        simp only [List.mem_singleton] at hd; subst hd
        intro a h1 h2 h3 h4
        simp only at h1 h2 h3 h4
        rcases Nat.lt_or_gt_of_ne hjk with h | h
        · have := Nat.mul_le_mul_left wbytes (show j + 1 ≤ i / (8 * wbytes) by omega)
          rw [Nat.mul_add, Nat.mul_one] at this; omega
        · have := Nat.mul_le_mul_left wbytes (show i / (8 * wbytes) + 1 ≤ j by omega)
          rw [Nat.mul_add, Nat.mul_one] at this; omega

end Silmaril.Data.Bitmap
