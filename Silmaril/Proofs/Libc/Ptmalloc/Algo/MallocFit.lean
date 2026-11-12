module

public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocArena

/-!
# ptmalloc algorithm: `takeFit`, the large-bin best fit and the bin-map scan

* `Algo.takeFit_body`: taking a chunk of at least `nb` bytes out of a small/large bin (whole, or
  split with the remainder at the unsorted head, `last_remainder` set or not) is an `MBody`;
* **`Algo.mallocLargeBody`** (= `Task.algo.mallocLargeBody`): `largeFit` picks a chunk of the
  request's bin of at least `nb` bytes;
* **`Algo.mallocBinmapBody`** (= `Task.algo.mallocBinmapBody`): the bin-map scan only unmarks
  empty bins, and a chunk of a later bin is larger than `nb` (`Config.binIndex_mono`).
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc

theorem splitRun_relabel_nodup (a s₁ : Nat) (u u₁ u₂ : Use) : ∀ (s : Nat) (cs : List (Nat × Use)),
    (runAddrs s cs).Nodup → splitRun a s₁ u₁ u₂ s (relabelRun a u s cs) = splitRun a s₁ u₁ u₂ s cs
  | _, [], _ => rfl
  | s, (sz, v) :: cs, h => by
    rw [runAddrs_cons, List.nodup_cons] at h
    by_cases hs : s = a
    · subst hs
      simp only [relabelRun, splitRun, ite_true, relabelRun_of_not_mem u h.1]
    · simp only [relabelRun, splitRun, hs, ite_false,
        splitRun_relabel_nodup a s₁ u u₁ u₂ (s + sz) cs h.2]

theorem sublist_flatMap_of_mem {α β : Type} (f : α → List β) {g : α} :
    ∀ {xs : List α}, g ∈ xs → (f g).Sublist (xs.flatMap f)
  | [], h => by cases h
  | x :: xs, h => by
    rw [List.flatMap_cons]
    rcases List.mem_cons.mp h with rfl | h
    · exact List.sublist_append_left _ _
    · exact (sublist_flatMap_of_mem f h).trans (List.sublist_append_right _ _)

theorem TopSt.split_relabel {ts : TopSt} (hn : (ts.heapChunks.map (·.addr)).Nodup) (a s₁ : Nat)
    (u u₁ u₂ : Use) : (ts.relabel a u).split a s₁ u₁ u₂ = ts.split a s₁ u₁ u₂ := by
  unfold TopSt.heapChunks at hn
  rw [List.map_append, List.nodup_append] at hn
  obtain ⟨hold, hcur, -⟩ := hn
  simp only [TopSt.relabel, TopSt.split, List.map_map, Function.comp_def]
  rw [splitRun_relabel_nodup a s₁ u u₁ u₂ _ _ hcur]
  congr 1
  apply List.map_congr_left
  intro g hg
  rw [splitRun_relabel_nodup a s₁ u u₁ u₂ _ _]
  rw [List.map_flatMap] at hold
  exact hold.sublist (by
    unfold runAddrs
    exact sublist_flatMap_of_mem (fun a : Seg => List.map (fun x : Chunk => x.addr) (layout a.start a.chunks)) hg)

namespace Algo

variable {C : Config}

theorem mem_bin_chunk {l : Local} (hw : LocalWF C l) {v i : Nat} (hv : v ∈ l.av.bins.lists i) :
    2 ≤ i ∧ ∃ d ∈ l.av.chunks, d.addr = v ∧ d.use = .bin i := by
  have hi : 2 ≤ i := by
    refine Nat.le_of_not_lt fun hlt => ?_
    rw [hw.arena.bins.outside i (.inl hlt)] at hv; cases hv
  exact ⟨hi, ((hw.arena.bins.exact_all hi) v).mp hv⟩

/-- **`takeFit`** of a chunk of bin `i` with at least `nb` bytes: an `MBody`. -/
theorem takeFit_body (hC : C.Ok) {n nb : Nat} (hnb : C.checkedRequest2size n = some nb) {l : Local}
    (hw : LocalWF C l) (hs : LocalSp C l) {v i : Nat} (hv : v ∈ l.av.bins.lists i)
    (hsz : nb ≤ l.av.tiles.sizeAt v) (lastRem : Bool) :
    MBody C n l (takeFit C l v i nb lastRem).1 (takeFit C l v i nb lastRem).2 := by
  obtain ⟨hn8, hnba, hnbm⟩ := request2size_spec hC hnb
  obtain ⟨hi, d, hd, rfl, hdu⟩ := mem_bin_chunk hw hv
  have hn' := hw.arena.tiles.nodup
  have hds : l.av.tiles.sizeAt d.addr = d.size := TopSt.sizeAt_of_mem hn' hd
  rw [hds] at hsz
  have hfree : d.use.tagFree = true := by rw [hdu]; rfl
  have hbins := hw.arena.bins.remove hn' hv (u := .internal) rfl
  have hus : UnsortedWF C l.av.unsorted
      (Chunk.view Use.isUnsorted (l.av.chunks.map (Chunk.relabelAt d.addr .internal))) := by
    have : Chunk.view Use.isUnsorted (l.av.chunks.map (Chunk.relabelAt d.addr .internal)) = l.av.unsortedView := by
      show Chunk.view _ (l.av.tiles.heapChunks.map _) = _
      rw [← TopSt.heapChunks_relabel]
      exact view_relabel_of hn' hd rfl (by rw [hdu]; exact isUnsorted_bin_of hi) rfl
    rw [this]; exact hw.arena.unsorted
  unfold takeFit
  simp only [hds]
  split
  · -- whole
    have := relabelLend (n := n) hC hw hs hd hfree (by omega) (l.av.bins.remove d.addr i) l.av.unsorted hbins hus
    have heq : (l.binRemove d.addr i .internal).relabel d.addr .client =
        { l with av := { l.av with tiles := l.av.tiles.relabel d.addr .client, bins := l.av.bins.remove d.addr i, unsorted := l.av.unsorted } } := by
      simp only [Local.relabel, Local.binRemove, TopSt.relabel_twice]
    rw [heq]; exact this
  · -- split, remainder to the unsorted head
    rename_i hge
    have hrem : nb + C.minSize ≤ d.size := by omega
    have hnotu : d.addr ∉ l.av.unsorted.list := fun hm => by
      obtain ⟨c, hc, hca, hcu⟩ := ((hw.arena.unsorted.exact_all) d.addr).mp hm
      have := chunk_unique hn' hc hd hca; subst this; rw [hdu] at hcu
      simp only [Use.bin.injEq] at hcu; omega
    have hb := hw.arena.tiles.bound d hd
    have heq : ∀ us : UnsortedSt, { (splitToUnsorted (l.binRemove d.addr i .internal) d.addr nb .client) with av := { (splitToUnsorted (l.binRemove d.addr i .internal) d.addr nb .client).av with unsorted := us } } =
        { l with av := { l.av with tiles := l.av.tiles.split d.addr nb .client (.bin 1), bins := l.av.bins.remove d.addr i, unsorted := us } } := by
      intro us
      simp only [splitToUnsorted, Local.binRemove, TopSt.split_relabel hn']
    cases lastRem
    · have := splitLend hC hw hs hd hfree hnba hnbm hrem hn8 (l.av.bins.remove d.addr i) hbins
        (l.av.unsorted.pushFront (d.addr + nb)) (by simp [UnsortedSt.pushFront, List.erase_of_not_mem hnotu])
        hw.arena.unsorted.lastRemBound
      have h2 := heq (l.av.unsorted.pushFront (d.addr + nb))
      simp only [Bool.false_eq_true, ite_false]
      have h3 : splitToUnsorted (l.binRemove d.addr i .internal) d.addr nb .client =
          { (splitToUnsorted (l.binRemove d.addr i .internal) d.addr nb .client) with av := { (splitToUnsorted (l.binRemove d.addr i .internal) d.addr nb .client).av with unsorted := l.av.unsorted.pushFront (d.addr + nb) } } := by
        simp [splitToUnsorted, Local.binRemove]
      rw [h3, h2]; exact this
    · have := splitLend hC hw hs hd hfree hnba hnbm hrem hn8 (l.av.bins.remove d.addr i) hbins
        ((l.av.unsorted.pushFront (d.addr + nb)).setLastRem (d.addr + nb))
        (by simp [UnsortedSt.pushFront, UnsortedSt.setLastRem, List.erase_of_not_mem hnotu])
        (by simp only [UnsortedSt.setLastRem]; omega)
      simp only [ite_true]
      rw [heq]
      have h4 : ((splitToUnsorted (l.binRemove d.addr i .internal) d.addr nb .client).av.unsorted.setLastRem
          (d.addr + nb)) = (l.av.unsorted.pushFront (d.addr + nb)).setLastRem (d.addr + nb) := by
        simp [splitToUnsorted, Local.binRemove]
      rw [h4]; exact this

end Algo

end Silmaril.Libc.Ptmalloc
