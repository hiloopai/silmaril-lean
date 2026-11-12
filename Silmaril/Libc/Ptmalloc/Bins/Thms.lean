module

public import Silmaril.Libc.Ptmalloc.Bins.Defs
public import Silmaril.Libc.Ptmalloc.Chunk.Thms

/-!
# ptmalloc component: the small/large bins' lemmas

`BinsWF.pushSmall` (insert at the head of a small bin, binmap marked: `_int_malloc`'s sorting of
a small chunk), `BinsWF.remove` (`unlink_chunk` of a chunk of bin `i`, relabelled to a use
outside the small/large bins), `BinsWF.unmark` (the bin-map scan clears an empty bin's bit),
over the whole chunk list and its sorted view. The large-bin insertion (`insertSorted`) is
`Task.algo.binsInsertSorted`.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc

namespace BinsWF

variable {C : Config} {bs : BinsSt} {cs : List Chunk} {sz : Nat → Nat} {a : Nat}

theorem exact_all (h : BinsWF C bs (Chunk.view Use.isSorted cs) sz) {i : Nat} (hi : 2 ≤ i) :
    ListExact (bs.lists i) cs (.bin i) :=
  (ListExact.view_iff (p := Use.isSorted) (by simp [Use.isSorted, hi])).mp (h.exact i hi)

/-- **Small-bin push** (binmap marked). -/
theorem pushSmall (h : BinsWF C bs (Chunk.view Use.isSorted cs) sz) (hn : (cs.map (·.addr)).Nodup)
    {d : Chunk} (hd : d ∈ cs) (hda : d.addr = a) (hds : d.use.isSorted = false) {i : Nat}
    (hi : 2 ≤ i ∧ i ≤ C.lastBin ∧ C.binIndex d.size = i) (hsmall : i < C.nSmallBins) :
    BinsWF C ((bs.pushFront a i).mark i)
      (Chunk.view Use.isSorted (cs.map (Chunk.relabelAt a (.bin i)))) sz := by
  have hv : ∀ j, 2 ≤ j → d.use ≠ .bin j := fun j hj he => by
    rw [he] at hds; simp [Use.isSorted, hj] at hds
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun j => ?_, fun c hc k hk => ?_, fun j hj => ?_,
    fun j _ => ?_⟩
  · refine (ListExact.view_iff (p := Use.isSorted) (by simp [Use.isSorted, hj])).mpr ?_
    by_cases hji : j = i
    · subst hji; simp only [BinsSt.mark, BinsSt.pushFront, ite_true]
      exact (h.exact_all hj).relabel_cons hn ⟨d, hd, hda, rfl⟩ (hv j hj)
    · simp only [BinsSt.mark, BinsSt.pushFront, hji, ite_false]
      exact (h.exact_all hj).relabel_keep hn ⟨d, hd, hda, rfl⟩
        (fun he => hji (Use.bin.inj he).symm) (hv j hj)
  · have : j ≠ i := by omega
    simp only [BinsSt.mark, BinsSt.pushFront, this, ite_false]; exact h.outside j hj
  · by_cases hji : j = i
    · subst hji; simp only [BinsSt.mark, BinsSt.pushFront, ite_true]
      refine List.nodup_cons.mpr ⟨fun ha => ?_, h.nodup j⟩
      obtain ⟨c, hc, hca, hcu⟩ := ((h.exact_all hi.1) a).mp ha
      have := chunk_unique hn hc hd (hca.trans hda.symm); subst this; exact hv j hi.1 hcu
    · simp only [BinsSt.mark, BinsSt.pushFront, hji, ite_false]; exact h.nodup j
  · have hc' := List.mem_filter.mp hc
    rcases mem_map_relabelAt.mp hc'.1 with ⟨e, he, hea, rfl⟩ | ⟨-, hc⟩
    · have := chunk_unique hn he hd (hea.trans hda.symm); subst this
      simp only [Use.bin.injEq] at hk; subst hk; simpa using hi
    · exact h.size c (List.mem_filter.mpr ⟨hc, hc'.2⟩) k hk
  · have : j ≠ i := by omega
    simp only [BinsSt.mark, BinsSt.pushFront, this, ite_false]; exact h.sorted j hj
  · by_cases hji : j = i
    · subst hji; simp [BinsSt.mark]
    · simp only [BinsSt.mark, BinsSt.pushFront, hji, ite_false] at *
      exact h.binmap j ‹_›

/-- **Bin removal** of `a ∈ bin i`, relabelled `u` (not a small/large bin). -/
theorem remove (h : BinsWF C bs (Chunk.view Use.isSorted cs) sz) (hn : (cs.map (·.addr)).Nodup)
    {i : Nat} (ha : a ∈ bs.lists i) {u : Use} (hu : u.isSorted = false) :
    BinsWF C (bs.remove a i) (Chunk.view Use.isSorted (cs.map (Chunk.relabelAt a u))) sz := by
  have hi : 2 ≤ i := by
    refine Nat.le_of_not_lt fun hlt => ?_
    rw [h.outside i (.inl hlt)] at ha; cases ha
  have hne : ∀ j, 2 ≤ j → u ≠ .bin j := fun j hj he => by
    rw [he] at hu; simp [Use.isSorted, hj] at hu
  obtain ⟨d, hd, hda, hdu⟩ := ((h.exact_all hi) a).mp ha
  refine ⟨fun j hj => ?_, fun j hj => ?_, fun j => ?_, fun c hc k hk => ?_, fun j hj => ?_,
    fun j hj => ?_⟩
  · refine (ListExact.view_iff (p := Use.isSorted) (by simp [Use.isSorted, hj])).mpr ?_
    by_cases hji : j = i
    · subst hji; simp only [BinsSt.remove, ite_true]
      exact (h.exact_all hj).relabel_erase (h.nodup j) (hne j hj)
    · simp only [BinsSt.remove, hji, ite_false]
      exact (h.exact_all hj).relabel_keep hn ⟨d, hd, hda, hdu⟩ (hne j hj)
        (fun he => hji (Use.bin.inj he).symm)
  · by_cases hji : j = i
    · subst hji; simp only [BinsSt.remove, ite_true]; rw [h.outside j hj]; rfl
    · simp only [BinsSt.remove, hji, ite_false]; exact h.outside j hj
  · by_cases hji : j = i
    · subst hji; simp only [BinsSt.remove, ite_true]; exact (h.nodup j).sublist (List.erase_sublist ..)
    · simp only [BinsSt.remove, hji, ite_false]; exact h.nodup j
  · have hc' := List.mem_filter.mp hc
    rcases mem_map_relabelAt.mp hc'.1 with ⟨e, he, hea, rfl⟩ | ⟨-, hc⟩
    · have := hc'.2; simp only at this; rw [hu] at this; cases this
    · exact h.size c (List.mem_filter.mpr ⟨hc, hc'.2⟩) k hk
  · by_cases hji : j = i
    · subst hji; simp only [BinsSt.remove, ite_true]
      exact (h.sorted j hj).sublist (List.erase_sublist ..)
    · simp only [BinsSt.remove, hji, ite_false]; exact h.sorted j hj
  · apply h.binmap j
    by_cases hji : j = i
    · subst hji; intro hnil; rw [hnil] at ha; cases ha
    · simpa [BinsSt.remove, hji] using hj

/-- **Unmarking an empty bin** keeps `BinsWF`. -/
theorem unmark (h : BinsWF C bs cs sz) {j : Nat} (hj : bs.lists j = []) :
    BinsWF C (bs.unmark j) cs sz where
  exact := h.exact
  outside := h.outside
  nodup := h.nodup
  size := h.size
  sorted := h.sorted
  binmap k hk := by
    by_cases hkj : k = j
    · subst hkj; exact absurd hj hk
    · simp only [BinsSt.unmark, hkj, ite_false]; exact h.binmap k hk

end BinsWF

/-- **`Task.algo.binsInsertSorted`**: the large-bin insertion keeps `BinsWF` (glibc's position
keeps the non-increasing order; the list is a permutation of `a ::` the old one). -/
def Task.algo.binsInsertSorted : Prop :=
  ∀ (C : Config) (bs : BinsSt) (cs : List Chunk) (sz : Nat → Nat) (a i : Nat) (d : Chunk),
    BinsWF C bs (Chunk.view Use.isSorted cs) sz → (cs.map (·.addr)).Nodup →
    d ∈ cs → d.addr = a → d.use.isSorted = false → sz a = d.size →
    2 ≤ i → i ≤ C.lastBin → C.binIndex d.size = i →
    BinsWF C ((bs.insertSorted sz a i).mark i)
      (Chunk.view Use.isSorted (cs.map (Chunk.relabelAt a (.bin i)))) sz

end Silmaril.Libc.Ptmalloc
