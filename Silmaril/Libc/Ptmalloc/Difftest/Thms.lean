module

public import Silmaril.Libc.Ptmalloc.Difftest.Defs

/-!
# ptmalloc: the difftest's checks are sound

The differential tester (`Silmaril.Libc.Ptmalloc.Difftest`) reports fragments through
`firstBad` and invariant fields through Boolean mirrors. These lemmas say that a passing check
implies the proposition it reports on, so a pass of check A on a dump is a pass of the model's
own `Frag.Holds` and `*WF` on the read-back state (the read-back itself is untrusted tooling).
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Difftest

open Silmaril.Data
open Silmaril.Data.SepList (Links SLinks dll slist)

theorem firstBad_eq_none {v : MemView} {f : Frag} (h : firstBad v f = none) : f.Holds v := by
  intro c hc
  unfold firstBad at h
  rw [Option.map_eq_none_iff, List.find?_eq_none] at h
  simpa using h c hc

theorem backsFast_sound {s : Snap} {spans : List (Nat × Nat)} (h : backsFast s spans = true) :
    s.view.Backs spans := by
  intro sp hsp i hi
  have := List.all_eq_true.1 h sp hsp
  simp only [Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, Bool.and_eq_true] at this
  rcases this with h0 | ⟨r, hr, hw, hlo, hhi⟩
  · omega
  · constructor
    · simp only [Snap.view, regionAt, Option.isSome_map]
      rw [List.find?_isSome]
      exact ⟨r, hr, by simp only [decide_eq_true_eq]; omega⟩
    · simp only [Snap.view, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨r, hr, hw, by omega, by omega⟩

theorem sizeTable_getD : ∀ (cs : List Chunk) (a : Nat),
    (sizeTable cs).getD a 0 = ((cs.find? (·.addr = a)).map (·.size)).getD 0
  | [], a => by simp [sizeTable]
  | c :: cs, a => by
    have ih := sizeTable_getD cs a
    simp only [sizeTable, List.foldr_cons] at ih ⊢
    rw [Std.HashMap.getD_insert]
    by_cases h : c.addr = a
    · simp [h]
    · simp [h, ih]

theorem sizeAtT_eq (ts : TopSt) (a : Nat) : sizeAtT ts a = ts.sizeAt a := by
  simp only [sizeAtT, szOf, TopSt.sizeAt]; exact sizeTable_getD _ a

theorem sizeAtT_fun (ts : TopSt) : sizeAtT ts = ts.sizeAt := funext (sizeAtT_eq ts)

theorem range_succ_flatMap {β : Type} (n : Nat) (g : Nat → List β) :
    (List.range (n + 1)).flatMap g = g 0 ++ (List.range n).flatMap (fun j => g (j + 1)) := by
  rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]

theorem dllNodes_eq (K : Links) (s : Nat) : ∀ (prev : Nat) (l : List Nat),
    dllNodes K s prev l = (List.range l.length).flatMap fun j =>
      [⟨l.getD j 0 + K.fd, K.ws, l.getD (j + 1) s⟩,
       ⟨l.getD j 0 + K.bk, K.ws, if j = 0 then prev else l.getD (j - 1) 0⟩]
  | _, [] => rfl
  | prev, x :: r => by
    rw [List.length_cons, range_succ_flatMap]
    simp only [dllNodes, dllNodes_eq K s x r, List.getD_cons_zero, List.getD_cons_succ,
      List.cons_append, List.nil_append, Nat.zero_add]
    congr 2
    · cases r <;> rfl
    · congr 1
      funext j
      cases j <;> simp

theorem dllNodes_eq_dseg (K : Links) (s : Nat) : ∀ (prev : Nat) (l : List Nat),
    dllNodes K s prev l = Silmaril.Data.SepList.dseg K prev l s
  | _, [] => rfl
  | prev, x :: r => by
    simp only [dllNodes, Silmaril.Data.SepList.dseg, dllNodes_eq_dseg K s x r]

theorem dll_eq_dllT (K : Links) (s : Nat) (l : List Nat) : dll K s l = dllT K s l := by
  simp only [dll, dllT, dllNodes_eq_dseg]

theorem slist_eq_slistT (K : SLinks) : ∀ l, slist K l = slistT K l
  | [] => rfl
  | x :: r => by
    simp only [slistT, slist, slist_eq_slistT K r]

theorem fastFragF_eq (C : Config) (L : Layout) (a : Nat) (fs : FastSt) :
    fastFragF C L a fs = fastFrag C L a fs := by
  simp only [fastFragF, fastFrag, slist_eq_slistT]

theorem binsFragF_eq (C : Config) (L : Layout) (a : Nat) (bs : BinsSt) (sz : Nat → Nat) :
    binsFragF C L a bs sz = binsFrag C L a bs sz := by
  simp only [binsFragF, binsFrag, dll_eq_dllT]

theorem unsortedFragF_eq (C : Config) (L : Layout) (a : Nat) (us : UnsortedSt) (sz : Nat → Nat) :
    unsortedFragF C L a us sz = unsortedFrag C L a us sz := by
  simp only [unsortedFragF, unsortedFrag, dll_eq_dllT]

theorem arenaFragT_eq (C : Config) (L : Layout) (avAddr : Nat) (av : ArenaSt) :
    arenaFragT C L avAddr av = arenaFrag C L avAddr av := by
  have h : szOf (sizeTable av.tiles.heapChunks) = av.tiles.sizeAt := sizeAtT_fun av.tiles
  simp only [arenaFragT, arenaFrag, h, fastFragF_eq, binsFragF_eq, unsortedFragF_eq]

theorem arenaRepT_eq (C : Config) (L : Layout) (init : Bool) (avAddr : Nat) (av : ArenaSt) :
    arenaRepT C L init avAddr av = arenaRep C L init avAddr av := by
  simp only [arenaRepT, arenaRep, arenaFragT_eq]

theorem nodupGo_sound : ∀ (s : Std.HashSet Nat) (l : List Nat), nodupGo s l = true →
    l.Nodup ∧ ∀ a ∈ l, s.contains a = false
  | _, [], _ => ⟨List.nodup_nil, fun _ h => nomatch h⟩
  | s, a :: l, h => by
    simp only [nodupGo, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨ha, hl⟩ := nodupGo_sound (s.insert a) l h.2
    refine ⟨List.nodup_cons.2 ⟨fun hm => ?_, ha⟩, fun b hb => ?_⟩
    · have := hl a hm
      simp [Std.HashSet.contains_insert] at this
    · rcases List.mem_cons.1 hb with rfl | hb
      · exact h.1
      · have := hl b hb
        simp only [Std.HashSet.contains_insert, Bool.or_eq_false_iff] at this
        exact this.2

theorem nodupFast_sound {l : List Nat} (h : nodupFast l = true) : l.Nodup :=
  (nodupGo_sound _ l h).1

theorem listExact_sound {l : List Nat} {cs : List Chunk} {u : Use} (h : listExact l cs u = true) :
    ListExact l cs u := by
  unfold listExact chunksWithUse at h
  simp only [Std.HashSet.contains_ofList] at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.contains_iff_mem, List.mem_map,
    List.mem_filter, decide_eq_true_eq] at h
  intro a
  constructor
  · intro ha
    obtain ⟨c, ⟨hc, hu⟩, rfl⟩ := h.1 a ha
    exact ⟨c, hc, rfl, hu⟩
  · rintro ⟨c, hc, rfl, hu⟩
    exact h.2 _ ⟨c, ⟨hc, hu⟩, rfl⟩

theorem coalescedB_sound {cs : List (Nat × Use)} (h : coalescedB cs = true) : Coalesced cs := h

theorem nodup_of_map {α β : Type} (f : α → β) {l : List α} (h : (l.map f).Nodup) : l.Nodup := by
  unfold List.Nodup at *
  rw [List.pairwise_map] at h
  exact h.imp fun hne e => hne (congrArg f e)

theorem chkTop_sound {C : Config} {ts : TopSt} (h : (chkTop C ts).all (·.2) = true) : TopWF C ts := by
  simp only [chkTop, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15⟩ := h
  refine ⟨fun c hc => ?_, fun c hc => ?_, fun c hc => ?_, fun hs => ?_, ?_, fun hs => ?_,
    coalescedB_sound h7, fun c hc => ?_, fun g hg => coalescedB_sound ?_, ?_, ?_, fun hs => ?_,
    nodupFast_sound h13, fun c hc => ?_, fun hs => ?_⟩
  · have := List.all_eq_true.1 h1 c hc; simpa using this
  · have := List.all_eq_true.1 h2 c hc; simpa using this
  · have := List.all_eq_true.1 h3 c hc; simpa using this
  · simpa [hs] using h4
  · simpa using h5
  · simpa [hs] using h6
  · simp only [Option.mem_def] at hc; simp [hc] at h8; exact h8
  · exact List.all_eq_true.1 h9 g hg
  · simpa using h10
  · simpa using h11
  · simpa [hs] using h12
  · have := List.all_eq_true.1 h14 c hc; simpa using this
  · simpa [hs] using h15

theorem chkUnsorted_sound {C : Config} {us : UnsortedSt} {cs : List Chunk}
    (h : (chkUnsorted C us cs).all (·.2) = true) : UnsortedWF C us cs := by
  simp only [chkUnsorted, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact ⟨listExact_sound h1, nodupFast_sound h2, fun c hc => by simpa using List.all_eq_true.1 h3 c hc,
    by simpa using h4⟩

theorem chkMmap_sound {C : Config} {ms : MmapSt} (h : (chkMmap C ms).all (·.2) = true) : MmapWF C ms := by
  simp only [chkMmap, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨by simpa using h1, by simpa using h2, fun c hc => ?_, fun c hc hu => ?_, fun c hc => ?_, ?_,
    by simpa using h7⟩
  · simpa using List.all_eq_true.1 h3 c hc
  · have := List.all_eq_true.1 h4 c hc; simp [hu] at this; exact this
  · simpa using List.all_eq_true.1 h5 c hc
  · exact nodup_of_map _ (nodupFast_sound h6)

theorem chkTcache_sound {C : Config} {tc : TcacheSt} (hout : ∀ i, C.tcacheBins ≤ i → tc.bins i = [])
    (h : (chkTcache C tc).all (·.2) = true) : TcacheWF C tc := by
  simp only [chkTcache, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have inr : ∀ i, ¬ C.tcacheBins ≤ i → i ∈ List.range C.tcacheBins := fun i hi => List.mem_range.2 (by omega)
  refine ⟨hout, fun i => ?_, fun i c hc => ?_, fun i c hc => ?_, by simpa using h4⟩
  · by_cases hi : C.tcacheBins ≤ i
    · simp [hout i hi]
    · have := List.all_eq_true.1 h1 i (inr i hi)
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact ⟨nodup_of_map _ (nodupFast_sound this.1), this.2⟩
  · by_cases hi : C.tcacheBins ≤ i
    · simp [hout i hi] at hc
    · have := List.all_eq_true.1 (List.all_eq_true.1 h2 i (inr i hi)) c hc
      simp only [Bool.and_eq_true, decide_eq_true_eq] at this
      exact ⟨this.1.1, this.1.2, this.2⟩
  · by_cases hi : C.tcacheBins ≤ i
    · simp [hout i hi] at hc
    · have := List.all_eq_true.1 (List.all_eq_true.1 h3 i (inr i hi)) c hc
      simpa using this

theorem chkFast_sound {C : Config} {fs : FastSt} {cs : List Chunk}
    (hout : ∀ i, C.nFast ≤ i → fs.lists i = []) (h : (chkFast C fs cs).all (·.2) = true) :
    FastWF C fs cs := by
  simp only [chkFast, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hsz : ∀ c ∈ cs, ∀ i, c.use = .fast i → C.fidx c.size = i ∧ c.size ≤ C.maxFast ∧ i < C.nFast := by
    intro c hc i hu
    have := List.all_eq_true.1 h3 c hc
    rw [hu] at this
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  refine ⟨fun i => ?_, fun i => ?_, hsz, fun ⟨i, hi⟩ => ?_⟩
  · by_cases hi : C.nFast ≤ i
    · rw [hout i hi]
      intro a
      simp only [List.not_mem_nil, false_iff, not_exists, not_and]
      intro c hc _ hu
      exact absurd (hsz c hc i hu).2.2 (by omega)
    · exact listExact_sound (List.all_eq_true.1 h1 i (List.mem_range.2 (by omega)))
  · by_cases hi : C.nFast ≤ i
    · rw [hout i hi]; exact List.nodup_nil
    · exact nodupFast_sound (List.all_eq_true.1 h2 i (List.mem_range.2 (by omega)))
  · by_cases hn : C.nFast ≤ i
    · exact absurd (hout i hn) hi
    · simp only [Bool.or_eq_true, Bool.not_eq_true', List.any_eq_false] at h4
      rcases h4 with h4 | h4
      · exact absurd (h4 i (List.mem_range.2 (by omega))) (by simpa using hi)
      · exact h4

/-- A list whose adjacent entries descend is descending (`BinsWF.sorted` from the linear check). -/
theorem pairwise_of_adj : ∀ (l : List Nat), (∀ j, j + 1 < l.length → l.getD (j + 1) 0 ≤ l.getD j 0) →
    l.Pairwise (fun a b => b ≤ a)
  | [], _ => List.Pairwise.nil
  | [_], _ => by simp
  | x :: y :: r, h => by
    have ih := pairwise_of_adj (y :: r) (fun j hj => by
      simpa using h (j + 1) (by simp only [List.length_cons] at hj ⊢; omega))
    have hxy : y ≤ x := by simpa using h 0 (by simp)
    refine List.Pairwise.cons (fun b hb => ?_) ih
    rcases List.mem_cons.1 hb with rfl | hb
    · exact hxy
    · exact Nat.le_trans ((List.pairwise_cons.1 ih).1 b hb) hxy

theorem chkBins_sound {C : Config} {bs : BinsSt} {cs : List Chunk} {sz : Nat → Nat}
    (hout : ∀ i, C.nBins ≤ i → bs.lists i = []) (h : (chkBins C bs cs sz).all (·.2) = true) :
    BinsWF C bs cs sz := by
  simp only [chkBins, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hsz : ∀ c ∈ cs, ∀ i, c.use = .bin i → 2 ≤ i ∧ i ≤ C.lastBin ∧ C.binIndex c.size = i := by
    intro c hc i hu
    have := List.all_eq_true.1 h4 c hc
    rw [hu] at this
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  have inr : ∀ i, ¬ C.nBins ≤ i → i ∈ List.range C.nBins := fun i hi => List.mem_range.2 (by omega)
  refine ⟨fun i h2i => ?_, fun i hi => ?_, fun i => ?_, hsz, fun i hi => ?_, fun i hne => ?_⟩
  · by_cases hi : C.nBins ≤ i
    · rw [hout i hi]
      intro a
      simp only [List.not_mem_nil, false_iff, not_exists, not_and]
      intro c hc _ hu
      have := hsz c hc i hu
      unfold Config.lastBin at this
      omega
    · exact listExact_sound (List.all_eq_true.1 h1 i (List.mem_filter.2 ⟨inr i hi, by simpa using h2i⟩))
  · by_cases hn : C.nBins ≤ i
    · exact hout i hn
    · have := List.all_eq_true.1 h2 i (List.mem_filter.2 ⟨inr i hn, by simpa using hi⟩)
      simpa using this
  · by_cases hn : C.nBins ≤ i
    · rw [hout i hn]; exact List.nodup_nil
    · exact nodupFast_sound (List.all_eq_true.1 h3 i (inr i hn))
  · by_cases hn : C.nBins ≤ i
    · rw [hout i hn]; exact List.Pairwise.nil
    · have h5i := List.all_eq_true.1 h5 i (List.mem_filter.2 ⟨inr i hn, by simpa using hi⟩)
      refine List.pairwise_map.1 (pairwise_of_adj _ fun j hj => ?_)
      have := List.all_eq_true.1 h5i j (List.mem_range.2 (by simp only [List.length_map] at hj ⊢; omega))
      simpa using this
  · by_cases hn : C.nBins ≤ i
    · exact absurd (hout i hn) hne
    · have := List.all_eq_true.1 h6 i (inr i hn)
      simp only [Bool.or_eq_true] at this
      rcases this with h | h
      · exact absurd (by simpa using h) hne
      · exact h


/-- **The arena's mirrors compose** (the composition of `Heap.ArenaWF` over the views): passing
the four component mirrors and the `internal` link check on the views gives `ArenaWF`, given
the read-back's out-of-range emptiness. -/
theorem chkArena_sound {C : Config} {av : ArenaSt}
    (hf : ∀ i, C.nFast ≤ i → av.fast.lists i = []) (hb : ∀ i, C.nBins ≤ i → av.bins.lists i = [])
    (ht : (chkTop C av.tiles).all (·.2) = true)
    (hfa : (chkFast C av.fast av.fastView).all (·.2) = true)
    (hbi : (chkBins C av.bins av.sortedView av.tiles.sizeAt).all (·.2) = true)
    (hu : (chkUnsorted C av.unsorted av.unsortedView).all (·.2) = true)
    (hi : (av.chunks.all fun c => c.use ≠ .internal || decide (C.minSize ≤ c.size)) = true) :
    ArenaWF C av :=
  ⟨chkTop_sound ht, chkFast_sound hf hfa, chkBins_sound hb hbi, chkUnsorted_sound hu,
    fun c hc hint => by have := List.all_eq_true.1 hi c hc; simpa [hint] using this⟩

end Silmaril.Libc.Ptmalloc.Difftest
