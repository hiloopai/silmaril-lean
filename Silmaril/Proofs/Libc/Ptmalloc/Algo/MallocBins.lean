module

public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocTiles

/-!
# ptmalloc: the large-bin insertion and the bin index

* `BinsSt.insertSorted_perm`, `insertSorted_sorted`: glibc's large-bin position gives a
  permutation of `a ::` the bin, non-increasing when the bin was;
* **`Algo.binsInsertSorted`** (= `Task.algo.binsInsertSorted`): the insertion keeps `BinsWF`;
* `Config.binIndex_mono`: the bin index is monotone in the size (so a chunk of a later bin is
  larger than the request: the bin-map scan's fit).
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc

theorem takeWhile_append_drop {α : Type} (p : α → Bool) :
    ∀ L : List α, L.takeWhile p ++ L.drop (L.takeWhile p).length = L
  | [] => rfl
  | x :: xs => by
    by_cases hp : p x
    · simp [hp, takeWhile_append_drop p xs]
    · simp [hp]

theorem head_drop_takeWhile {α : Type} (p : α → Bool) :
    ∀ (L : List α) (b : α) (rest : List α), L.drop (L.takeWhile p).length = b :: rest → p b = false
  | [], _, _, h => by simp at h
  | x :: xs, b, rest, h => by
    by_cases hp : p x
    · simp only [List.takeWhile_cons, hp, ite_true, List.length_cons, List.drop_succ_cons] at h
      exact head_drop_takeWhile p xs b rest h
    · simp only [List.takeWhile_cons, hp, Bool.false_eq_true, ite_false, List.length_nil,
        List.drop_zero, List.cons.injEq] at h
      rw [← h.1]; simpa using hp

theorem mem_takeWhile_p {α : Type} (p : α → Bool) :
    ∀ (L : List α) (x : α), x ∈ L.takeWhile p → p x = true
  | [], _, h => by simp at h
  | y :: ys, x, h => by
    by_cases hp : p y
    · simp only [List.takeWhile_cons, hp, ite_true, List.mem_cons] at h
      rcases h with rfl | h
      · exact hp
      · exact mem_takeWhile_p p ys x h
    · simp [hp] at h

/-- Insert `a` before `rest` (second in `rest`'s first group when that has `a`'s size). -/
def insAt (sz : Nat → Nat) (a : Nat) (pre rest : List Nat) : List Nat :=
  match rest with
  | b :: rest' => if sz b = sz a then pre ++ b :: a :: rest' else pre ++ a :: rest
  | [] => pre ++ [a]

/-- The new large-bin list. -/
def insList (sz : Nat → Nat) (a : Nat) (L : List Nat) : List Nat :=
  insAt sz a (L.takeWhile fun b => sz a < sz b) (L.drop (L.takeWhile fun b => sz a < sz b).length)

theorem insertSorted_lists (bs : BinsSt) (sz : Nat → Nat) (a i j : Nat) :
    (bs.insertSorted sz a i).lists j = if j = i then insList sz a (bs.lists i) else bs.lists j := by
  unfold BinsSt.insertSorted insList insAt
  rfl

theorem insAt_perm (sz : Nat → Nat) (a : Nat) (pre rest : List Nat) :
    (insAt sz a pre rest).Perm (a :: (pre ++ rest)) := by
  unfold insAt
  cases rest with
  | nil => simp
  | cons b rest' =>
    simp only
    split
    · refine (List.Perm.append_left pre (List.Perm.swap a b rest')).trans ?_
      exact List.perm_middle
    · exact List.perm_middle

theorem insList_perm (sz : Nat → Nat) (a : Nat) (L : List Nat) : (insList sz a L).Perm (a :: L) := by
  have := insAt_perm sz a (L.takeWhile fun b => sz a < sz b) (L.drop (L.takeWhile fun b => sz a < sz b).length)
  rw [takeWhile_append_drop] at this
  exact this

theorem insAt_sorted (sz : Nat → Nat) (a : Nat) (pre rest : List Nat)
    (hs : (pre ++ rest).Pairwise fun x y => sz y ≤ sz x) (hpre : ∀ x ∈ pre, sz a < sz x)
    (hhead : ∀ b rest', rest = b :: rest' → ¬ sz a < sz b) :
    (insAt sz a pre rest).Pairwise fun x y => sz y ≤ sz x := by
  rw [List.pairwise_append] at hs
  obtain ⟨hs1, hs2, hs3⟩ := hs
  unfold insAt
  cases rest with
  | nil =>
    rw [List.pairwise_append]
    refine ⟨hs1, List.pairwise_singleton _ _, fun x hx y hy => ?_⟩
    rw [List.mem_singleton] at hy; subst hy; exact Nat.le_of_lt (hpre x hx)
  | cons b rest' =>
    have hb := hhead b rest' rfl
    rw [List.pairwise_cons] at hs2
    simp only
    split
    · rename_i heq
      rw [List.pairwise_append]
      refine ⟨hs1, ?_, ?_⟩
      · rw [List.pairwise_cons, List.pairwise_cons]
        refine ⟨?_, fun y hy => by rw [← heq]; exact hs2.1 y hy, hs2.2⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · omega
        · exact hs2.1 y hy
      · intro x hx y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hs3 x hx y (List.mem_cons_self ..)
        rcases List.mem_cons.mp hy with rfl | hy
        · exact Nat.le_of_lt (hpre x hx)
        · exact hs3 x hx y (List.mem_cons_of_mem _ hy)
    · rw [List.pairwise_append]
      refine ⟨hs1, ?_, ?_⟩
      · rw [List.pairwise_cons]
        refine ⟨?_, List.pairwise_cons.mpr hs2⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · omega
        · have := hs2.1 y hy; omega
      · intro x hx y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact Nat.le_of_lt (hpre x hx)
        · exact hs3 x hx y hy

theorem insList_sorted (sz : Nat → Nat) (a : Nat) (L : List Nat)
    (hs : L.Pairwise fun x y => sz y ≤ sz x) : (insList sz a L).Pairwise fun x y => sz y ≤ sz x := by
  refine insAt_sorted sz a _ _ (by rw [takeWhile_append_drop]; exact hs)
    (fun x hx => by simpa using mem_takeWhile_p _ L x hx) (fun b rest' h => ?_)
  simpa using head_drop_takeWhile (fun b => sz a < sz b) L b rest' h

namespace Algo

/-- **`Task.algo.binsInsertSorted`**: the large-bin insertion keeps `BinsWF`. -/
theorem binsInsertSorted : Task.algo.binsInsertSorted := by
  intro C bs cs sz a i d h hn hd hda hds hsza hi2 hil hbi
  have hv : ∀ j, 2 ≤ j → d.use ≠ .bin j := fun j hj he => by
    rw [he] at hds; simp [Use.isSorted, hj] at hds
  have hperm := insList_perm sz a (bs.lists i)
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun j => ?_, fun c hc k hk => ?_, fun j hj => ?_,
    fun j _ => ?_⟩
  · refine (ListExact.view_iff (p := Use.isSorted) (by simp [Use.isSorted, hj])).mpr ?_
    by_cases hji : j = i
    · subst hji; simp only [BinsSt.mark, insertSorted_lists, ite_true]
      exact ((h.exact_all hj).relabel_cons hn ⟨d, hd, hda, rfl⟩ (hv j hj)).of_mem_iff
        fun x => hperm.mem_iff
    · simp only [BinsSt.mark, insertSorted_lists, hji, ite_false]
      exact (h.exact_all hj).relabel_keep hn ⟨d, hd, hda, rfl⟩
        (fun he => hji (Use.bin.inj he).symm) (hv j hj)
  · have : j ≠ i := by omega
    simp only [BinsSt.mark, insertSorted_lists, this, ite_false]; exact h.outside j hj
  · by_cases hji : j = i
    · subst hji; simp only [BinsSt.mark, insertSorted_lists, ite_true]
      refine hperm.nodup_iff.mpr (List.nodup_cons.mpr ⟨fun ha => ?_, h.nodup j⟩)
      obtain ⟨c, hc, hca, hcu⟩ := ((h.exact_all hi2) a).mp ha
      have := chunk_unique hn hc hd (hca.trans hda.symm); subst this; exact hv j hi2 hcu
    · simp only [BinsSt.mark, insertSorted_lists, hji, ite_false]; exact h.nodup j
  · have hc' := List.mem_filter.mp hc
    rcases mem_map_relabelAt.mp hc'.1 with ⟨e, he, hea, rfl⟩ | ⟨-, hc⟩
    · have := chunk_unique hn he hd (hea.trans hda.symm); subst this
      simp only [Use.bin.injEq] at hk; subst hk; exact ⟨hi2, hil, hbi⟩
    · exact h.size c (List.mem_filter.mpr ⟨hc, hc'.2⟩) k hk
  · by_cases hji : j = i
    · subst hji; simp only [BinsSt.mark, insertSorted_lists, ite_true]
      exact insList_sorted sz a _ (h.sorted j hj)
    · simp only [BinsSt.mark, insertSorted_lists, hji, ite_false]; exact h.sorted j hj
  · by_cases hji : j = i
    · subst hji; simp [BinsSt.mark]
    · simp only [BinsSt.mark, insertSorted_lists, hji, ite_false] at *
      exact h.binmap j ‹_›

end Algo

namespace Config

theorem largeIndex_mono {a b : Nat} (h : a ≤ b) : largeIndex a ≤ largeIndex b := by
  unfold largeIndex
  have h1 : a / 64 ≤ b / 64 := Nat.div_le_div_right h
  have h2 : a / 512 ≤ b / 512 := Nat.div_le_div_right h
  have h3 : a / 4096 ≤ b / 4096 := Nat.div_le_div_right h
  have h4 : a / 32768 ≤ b / 32768 := Nat.div_le_div_right h
  have h5 : a / 262144 ≤ b / 262144 := Nat.div_le_div_right h
  repeat' split
  all_goals omega

/-- **The bin index is monotone** (for the LP64 constants of `C.Ok`). -/
theorem binIndex_mono {C : Config} (hC : C.Ok) {a b : Nat} (h : a ≤ b) :
    C.binIndex a ≤ C.binIndex b := by
  obtain ⟨hb1, hb2, hb3⟩ := hC.bins
  have h16 := hC.align
  unfold binIndex inSmallRange
  rw [hb3, hb2, h16]
  by_cases ha : a < 64 * 16 <;> by_cases hb : b < 64 * 16 <;> simp only [ha, hb, decide_true,
    decide_false, ite_true, Bool.false_eq_true, ite_false]
  · exact Nat.div_le_div_right h
  · have := largeIndex_mono (Nat.le_refl b)
    unfold largeIndex
    have : b / 64 ≥ 16 := by omega
    repeat' split
    all_goals omega
  · omega
  · exact largeIndex_mono h

end Config

end Silmaril.Libc.Ptmalloc
