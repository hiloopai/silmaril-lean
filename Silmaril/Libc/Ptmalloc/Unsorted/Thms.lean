module

public import Silmaril.Libc.Ptmalloc.Unsorted.Defs
public import Silmaril.Libc.Ptmalloc.Chunk.Thms

/-!
# ptmalloc component: the unsorted bin's lemmas

`UnsortedWF.push` (insert at the head, relabelled `bin 1`), `UnsortedWF.erase` (`unlink_chunk`
of an unsorted chunk, relabelled to another use) and `UnsortedWF.takeLast` (the scan's victim),
over the whole chunk list and its unsorted view.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc

/-- With distinct entries, dropping the last entry erases it. -/
theorem List.dropLast_eq_erase_of_nodup {l : List Nat} {a : Nat} (hn : l.Nodup)
    (h : l.getLast? = some a) : l.dropLast = l.erase a := by
  induction l with
  | nil => cases h
  | cons b l ih =>
    cases l with
    | nil => simp at h; subst h; simp
    | cons c l =>
      rw [List.nodup_cons] at hn
      have hlast : (c :: l).getLast? = some a := by
        rw [List.getLast?_cons] at h ⊢; simpa [List.getLast?_cons] using h
      have hba : b ≠ a := fun hb => by
        subst hb; exact hn.1 (List.mem_of_getLast? hlast)
      rw [List.dropLast_cons_cons, ih hn.2 hlast]; simp [List.erase_cons, hba]

namespace UnsortedWF

variable {C : Config} {us : UnsortedSt} {cs : List Chunk} {a : Nat}

theorem exact_all (h : UnsortedWF C us (Chunk.view Use.isUnsorted cs)) :
    ListExact us.list cs (.bin 1) :=
  (ListExact.view_iff (p := Use.isUnsorted) rfl).mp h.exact

/-- **Unsorted push.** -/
theorem push (h : UnsortedWF C us (Chunk.view Use.isUnsorted cs)) (hn : (cs.map (·.addr)).Nodup)
    (hsz : ∀ c ∈ cs, C.minSize ≤ c.size)
    {d : Chunk} (hd : d ∈ cs) (hda : d.addr = a) (hdu : d.use ≠ .bin 1) :
    UnsortedWF C (us.pushFront a) (Chunk.view Use.isUnsorted (cs.map (Chunk.relabelAt a (.bin 1)))) where
  exact := (ListExact.view_iff (p := Use.isUnsorted) rfl).mpr
    (h.exact_all.relabel_cons hn ⟨d, hd, hda, rfl⟩ hdu)
  nodup := by
    refine List.nodup_cons.mpr ⟨fun ha => ?_, h.nodup⟩
    obtain ⟨c, hc, hca, hcu⟩ := (h.exact_all a).mp ha
    have := chunk_unique hn hc hd (hca.trans hda.symm); subst this; exact hdu hcu
  size c hc := by
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp (List.mem_filter.mp hc).1
    simpa using hsz e he
  lastRemBound := h.lastRemBound

/-- **Unsorted removal** of `a`, relabelled `u`. -/
theorem erase (h : UnsortedWF C us (Chunk.view Use.isUnsorted cs)) {u : Use} (hu : u ≠ .bin 1) :
    UnsortedWF C (us.remove a) (Chunk.view Use.isUnsorted (cs.map (Chunk.relabelAt a u))) where
  exact := (ListExact.view_iff (p := Use.isUnsorted) rfl).mpr
    (h.exact_all.relabel_erase h.nodup hu)
  nodup := h.nodup.sublist (List.erase_sublist ..)
  size c hc := by
    have hc' := List.mem_filter.mp hc
    rcases mem_map_relabelAt.mp hc'.1 with ⟨e, he, hea, rfl⟩ | ⟨-, hc⟩
    · have := hc'.2; cases u <;> simp_all [Use.isUnsorted]
    · exact h.size c (List.mem_filter.mpr ⟨hc, hc'.2⟩)
  lastRemBound := h.lastRemBound

/-- **The scan's victim**: the last unsorted chunk, removed and relabelled `u`. -/
theorem takeLast (h : UnsortedWF C us (Chunk.view Use.isUnsorted cs)) {us' : UnsortedSt}
    (ht : us.takeLast = some (a, us')) {u : Use} (hu : u ≠ .bin 1) :
    UnsortedWF C us' (Chunk.view Use.isUnsorted (cs.map (Chunk.relabelAt a u))) := by
  unfold UnsortedSt.takeLast at ht
  split at ht
  · cases ht
  · rename_i b hb
    simp only [Option.some.injEq, Prod.mk.injEq] at ht
    obtain ⟨rfl, rfl⟩ := ht
    have := h.erase (a := b) hu
    rwa [UnsortedSt.remove, ← List.dropLast_eq_erase_of_nodup h.nodup hb] at this

end UnsortedWF

end Silmaril.Libc.Ptmalloc
