module

public import Silmaril.Proofs.Libc.Ptmalloc.Algo.Steps

/-!
# ptmalloc algorithm: `systrim` and `heap_trim` (`Task.algo.wfSystrim`)

Both shrink the top chunk by whole pages (`extra ≤ top_size - MINSIZE - 1`) and leave every chunk
of the tiling alone, so only `TopWF`'s top fields and, for the main arena, `MainBrk` (the break
moved by the same amount, checked to be at the top's end before) are re-proved. Components:
Top, Kernel.

* `Algo.wfSystrim : ∀ C, Task.algo.wfSystrim C`;
* `Algo.systrim_step`, `Algo.heapTrim_step`: the lent-out payloads, the thread and the shared
  part are kept (what `_int_free`'s merge path needs).
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

variable {C : Config}

theorem shrink_maps {k k' : KernelSt} {dec : Nat} {r : Option Unit} (h : k.shrink dec = (r, k')) :
    k'.maps = k.maps := by
  unfold KernelSt.shrink KernelSt.ask at h
  cases ha : k.oracle.answer k.asked with
  | refuse => rw [ha] at h; simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; rfl
  | ok v =>
    rw [ha] at h; simp only at h
    split at h
    · simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; rfl
    · simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; rfl

theorem shrink_spec {k k' : KernelSt} {dec : Nat} {r : Option Unit} (h : k.shrink dec = (r, k')) :
    k'.brkStart = k.brkStart ∧ (r = none → k'.brk = k.brk) ∧
      (r = some () → k.brkStart + dec ≤ k.brk ∧ k'.brk = k.brk - dec) := by
  unfold KernelSt.shrink KernelSt.ask at h
  cases ha : k.oracle.answer k.asked with
  | refuse =>
    rw [ha] at h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    refine ⟨rfl, fun _ => rfl, ?_⟩
    intro h0; exact absurd h0 (by simp)
  | ok v =>
    rw [ha] at h; simp only at h
    split at h
    · rename_i hc
      simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      refine ⟨rfl, ?_, fun _ => ⟨hc, rfl⟩⟩
      intro h0; exact absurd h0 (by simp)
    · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      refine ⟨rfl, fun _ => rfl, ?_⟩
      intro h0; exact absurd h0 (by simp)

theorem mprotect_spec {k k' : KernelSt} {b : Bool} (h : k.mprotect = (b, k')) :
    k'.brkStart = k.brkStart ∧ k'.brk = k.brk := by
  unfold KernelSt.mprotect KernelSt.ask at h
  cases ha : k.oracle.answer k.asked with
  | refuse =>
    rw [ha] at h; simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl⟩
  | ok v =>
    rw [ha] at h; simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; exact ⟨rfl, rfl⟩

/-- The top chunk shrunk by `extra` bytes (whole pages, leaving at least `MINSIZE + 1`). -/
theorem _root_.Silmaril.Libc.Ptmalloc.TopWF.shrinkTop (hC : C.Ok) {ts : TopSt} (h : TopWF C ts) {extra : Nat}
    (hpg : extra % C.page = 0) (hle : extra + C.minSize + 1 ≤ ts.topSize) :
    TopWF C { ts with topSize := ts.topSize - extra, systemMem := ts.systemMem - extra } := by
  have ha := hC.align; have hp := hC.page; have hm := hC.minSize
  have htA := h.topAligned
  rw [ha] at htA; rw [hp] at hpg; rw [hm] at hle
  have hsm := h.sysMem
  exact
  { sizes := h.sizes, aligned := h.aligned, nonNull := h.nonNull
    topAt := h.topAt
    topAligned := by rw [ha]; simp only; omega
    topMin := fun _ => by rw [hm]; simp only; omega
    coalesced := h.coalesced, lastUsed := h.lastUsed, coalescedOld := h.coalescedOld
    sysMem := by simp only; show (ts.heapChunks.map (·.size)).sum + _ ≤ _; omega
    sysMemBound := by simp only; have := h.sysMemBound; omega
    noHeap := h.noHeap, nodup := h.nodup, bound := h.bound
    topBound := fun hs => by simp only; have := h.topBound hs; omega }

/-- Shrinking the top keeps the view's ranges apart. -/
theorem apart_shrinkTop {l : Local} (h : Apart l.spans) {extra : Nat}
    (hle : extra < l.av.tiles.topSize) :
    Apart (l.av.tiles.heapChunks.map (fun c => (c.addr, c.size)) ++
        (if l.av.tiles.start = 0 then [] else [(l.av.tiles.top, l.av.tiles.topSize - extra)]) ++
        (l.av.heapSpans ++ l.shared.mm.chunks.map (fun c => (c.addr, c.size)))) := by
  rw [Local.spans_eq] at h
  unfold TopSt.spans at h
  split
  · rename_i h0; simp only [h0, ↓reduceIte] at h; exact h
  · rename_i h0
    simp only [h0, ↓reduceIte, List.append_assoc, List.cons_append, List.nil_append] at h ⊢
    exact Apart.shrink_mid (L := l.av.tiles.heapChunks.map (fun c => (c.addr, c.size)))
      (r := (l.av.tiles.top, l.av.tiles.topSize)) (s := l.av.tiles.topSize - extra) h (by omega)
      (by show _ ≤ l.av.tiles.topSize; omega)

theorem perm_boundary (Ch Mk R M : List (Nat × Nat)) (p : Nat × Nat) :
    ((Ch ++ [p]) ++ ((Mk ++ R) ++ M)).Perm ((Ch ++ Mk ++ M) ++ (p :: R)) :=
  List.perm_iff_count.mpr fun z => by
    simp only [List.count_append, List.count_cons, List.count_nil]; omega

/-- **Moving the boundary between top and the heap's reservation** (`grow_heap`, `shrink_heap`)
keeps the view's ranges apart: the two adjacent ranges cover the same bytes. -/
theorem apart_boundary {Ch Mk M : List (Nat × Nat)} {t a r a' r' : Nat}
    (h : Apart ((Ch ++ [(t, a)]) ++ ((Mk ++ (if r = 0 then [] else [(t + a, r)])) ++ M)))
    (ha' : 0 < a') (hsum : a' + r' = a + r) :
    Apart ((Ch ++ [(t, a')]) ++ ((Mk ++ (if r' = 0 then [] else [(t + a', r')])) ++ M)) := by
  have hin : ∀ x, t ≤ x → x < t + a + r →
      InSpans ((t, a) :: (if r = 0 then [] else [(t + a, r)])) x := by
    intro x h1 h2
    by_cases hx : x < t + a
    · exact ⟨(t, a), List.mem_cons_self .., h1, hx⟩
    · have hr : r ≠ 0 := by omega
      exact ⟨(t + a, r), List.mem_cons_of_mem _ (by simp [hr]), by simp only; omega,
        by simp only; omega⟩
  refine h.perm_cover (perm_boundary _ _ _ _ _) ?_ ?_ (perm_boundary _ _ _ _ _)
  · refine ⟨?_, ?_⟩
    · split
      · exact List.pairwise_singleton _ _
      · refine List.Pairwise.cons (fun b hb => ?_) (List.pairwise_singleton _ _)
        simp only [List.mem_singleton] at hb; subst hb; simp only; omega
    · intro s hs
      rcases List.mem_cons.mp hs with rfl | hs
      · exact ha'
      · split at hs
        · simp at hs
        · rename_i hr; simp only [List.mem_singleton] at hs; subst hs; simp only; omega
  · intro s hs x h1 h2
    rcases List.mem_cons.mp hs with rfl | hs
    · exact hin x h1 (by simp only at h2; omega)
    · split at hs
      · simp at hs
      · simp only [List.mem_singleton] at hs; subst hs; simp only at h1 h2
        exact hin x (by omega) (by omega)

/-- `shrink_heap`'s effect on a non-main arena's heaps. -/
theorem heapTrim_heapWF {av : ArenaSt} (h : HeapWF C av) {hb hs : Nat} {rest : List (Nat × Nat)}
    (hh : av.heaps = (hb, hs) :: rest) (hT : TopWF C av.tiles) {extra : Nat}
    (hle : extra < av.tiles.topSize) :
    HeapWF C { av with heaps := (hb, hs - extra) :: rest, reserve := av.reserve + extra, tiles := { av.tiles with topSize := av.tiles.topSize - extra, systemMem := av.tiles.systemMem - extra } } := by
  obtain ⟨hlt, hend, hres⟩ := h.cur_of hh
  have hst : av.tiles.start ≤ av.tiles.top := by
    rw [hT.topAt (by omega)]; omega
  have hsm := h.sysMem
  rw [hh] at hsm
  simp only [List.map_cons, List.sum_cons] at hsm
  refine ⟨⟨hb, hs - extra, rest, rfl, hlt, by simp only; omega, by simp only; omega⟩, ?_, ?_⟩
  · intro hp hm
    rcases List.mem_cons.mp hm with rfl | hm
    · obtain ⟨a1, a2, a3⟩ := h.addrs (hb, hs) (by rw [hh]; exact List.mem_cons_self ..)
      exact ⟨a1, a2, by simp only at a3 ⊢; omega⟩
    · exact h.addrs hp (by rw [hh]; exact List.mem_cons_of_mem _ hm)
  · simp only [List.map_cons, List.sum_cons]; omega

theorem alignDown_page (hC : C.Ok) (x : Nat) : alignDown x C.page % C.page = 0 ∧ alignDown x C.page ≤ x := by
  rw [hC.page]; unfold alignDown; constructor <;> omega

/-- **`systrim`**: on the main arena, any outcome keeps `LocalWF`, the chunks, the thread and the
shared part. -/
theorem systrim_step (hC : C.Ok) {l l' : Local} (hw : LocalWF C l.hf) (hmn : l.isMain = true)
    {pad : Nat} (h : systrim C l pad = .ok l') :
    LocalWF C l'.hf ∧ l' = { l with av := l'.av, kernel := l'.kernel } ∧
      l'.av = { l.av with tiles := l'.av.tiles } ∧ l'.av.tiles.heapChunks = l.av.tiles.heapChunks := by
  unfold systrim at h
  dsimp only at h
  split at h
  · cases h; exact ⟨hw, rfl, rfl, rfl⟩
  rename_i h1
  split at h
  · cases h; exact ⟨hw, rfl, rfl, rfl⟩
  rename_i h2
  obtain ⟨hpg, hle⟩ := alignDown_page hC (l.av.tiles.topSize - C.minSize - 1 - pad)
  generalize alignDown (l.av.tiles.topSize - C.minSize - 1 - pad) C.page = extra at h hpg hle
  split at h
  · cases h; exact ⟨hw, rfl, rfl, rfl⟩
  split at h
  · cases h; exact ⟨hw, rfl, rfl, rfl⟩
  rename_i h4
  have h4' : l.kernel.brk = l.av.tiles.top + l.av.tiles.topSize := by simpa using h4
  split at h
  · rename_i k hk
    cases h
    obtain ⟨hks, hkn, -⟩ := shrink_spec hk
    refine ⟨{ hw with
      main := fun hm => by
        obtain ⟨hs, b⟩ := hw.main hm
        refine ⟨hs, ?_⟩
        simp only [MainBrk, Local.hf] at b ⊢; rw [hks, hkn rfl]; exact b
      sysMain := fun hm => by
        have := hw.sysMain hm
        show _ ≤ k.total
        rw [KernelSt.total_eq hks (hkn rfl) (shrink_maps hk)]; exact this }, rfl, rfl, rfl⟩
  · rename_i k hk
    cases h
    obtain ⟨hks, -, hky⟩ := shrink_spec hk
    obtain ⟨hk1, hk2⟩ := hky rfl
    have ht : TopWF C l.av.tiles := hw.arena.tiles
    have ht' := ht.shrinkTop hC (extra := extra) hpg
      (show extra + C.minSize + 1 ≤ l.av.tiles.topSize by omega)
    have hav := hw.arena.withTilesViews _ ht' rfl rfl rfl
    have hp := hC.page
    refine ⟨{
      arena := hav
      shared := hw.shared
      tcache := hw.tcache
      init := hw.init
      apart := by
        rw [Local.spans_eq]
        exact apart_shrinkTop (l := l.hf) hw.apart (extra := extra) (by show extra < l.av.tiles.topSize; omega)
      mmSize := hw.mmSize
      heap := fun h => absurd (hmn.symm.trans h) (by decide)
      sysMain := fun hm => by
        have h0 := hw.sysMain hm
        have hsm := ht.sysMem
        have hmp := shrink_maps hk
        simp only [Local.hf, KernelSt.total] at h0 ⊢
        rw [hks, hk2, hmp]; omega
      main := fun hm => by
        obtain ⟨hs, b⟩ := hw.main hm
        refine ⟨hs, ?_⟩
        simp only [MainBrk, Local.hf] at b ⊢
        rw [hks, hk2]
        obtain ⟨b1, b2, b3, b4⟩ := b
        rw [hp] at b1 b3 b4 hpg ⊢
        refine ⟨b1, by omega, by omega, fun hs0 => ?_⟩
        obtain ⟨b5, b6⟩ := b4 hs0
        refine ⟨by omega, fun hnc => ⟨(b6 hnc).1, by omega⟩⟩ }, rfl, rfl, rfl⟩

/-- **`Algo.wfSystrim`**. -/
theorem wfSystrim (C : Config) : Task.algo.wfSystrim C := by
  intro hC l l' pad hw _ _ h
  obtain ⟨hw', he, hav, hch⟩ := systrim_step hC hw.hf ‹_› h
  refine ⟨hw'.of_hf fun hne => ?_, ?_, ?_⟩
  · rw [hav] at hne ⊢; exact hw.arena.fast.flag hne
  · rw [he]; simp [Footprint.Within]
  · rw [hav]; exact ArenaSt.out_congr (by rw [hch])

/-- **`heap_trim`** (non-main arena): any successful outcome keeps `LocalWF`, the chunks, the
thread and the shared part. -/
theorem heapTrim_step (hC : C.Ok) {l l' : Local} (hw : LocalWF C l.hf) (hnm : l.isMain = false)
    {pad : Nat} (h : heapTrim C l pad = .ok l') :
    LocalWF C l'.hf ∧ l' = { l with av := l'.av, kernel := l'.kernel } ∧
      l'.av.tiles.heapChunks = l.av.tiles.heapChunks ∧ l'.av.fast = l.av.fast := by
  have hnm' : ∀ L : Local, L.isMain = l.isMain → L.isMain = true → False := by
    intro L h1 h2; rw [h1, hnm] at h2; cases h2
  unfold heapTrim at h
  dsimp only at h
  split at h
  · cases h; exact ⟨hw, rfl, rfl, rfl⟩
  split at h
  · cases h; exact ⟨hw, rfl, rfl, rfl⟩
  rename_i h1
  split at h
  · cases h; exact ⟨hw, rfl, rfl, rfl⟩
  rename_i h2
  obtain ⟨hpg, hle⟩ := alignDown_page hC (l.av.tiles.topSize - C.minSize - 1 - pad)
  generalize alignDown (l.av.tiles.topSize - C.minSize - 1 - pad) C.page = extra at h hpg hle
  split at h
  · cases h; exact ⟨hw, rfl, rfl, rfl⟩
  split at h
  · cases h
  rename_i hb hs rest hh
  split at h
  · cases h
    exact ⟨{ hw with main := fun hm => (hnm' _ rfl hm).elim, sysMain := fun hm => (hnm' _ rfl hm).elim },
      rfl, rfl, rfl⟩
  · cases h
    have ht : TopWF C l.av.tiles := hw.arena.tiles
    have ht' := ht.shrinkTop hC (extra := extra) hpg
      (show extra + C.minSize + 1 ≤ l.av.tiles.topSize by omega)
    have hav := hw.arena.withTilesViews _ ht' rfl rfl rfl
    have hlt' : extra < l.av.tiles.topSize := by omega
    have hH : HeapWF C l.av := (hw.heap hnm).congr rfl rfl rfl rfl (Nat.le_refl _)
    have hH' := heapTrim_heapWF hH hh ht (extra := extra) hlt'
    obtain ⟨hlt, hend, hres⟩ := hH.cur_of (hb := hb) (hs := hs) (rest := rest) hh
    have hst : l.av.tiles.start ≠ 0 := by
      have : hb < l.av.tiles.start := hlt; omega
    exact ⟨{
      arena := ⟨hav.tiles, hav.fast, hav.bins, hav.unsorted, hav.internal⟩
      shared := hw.shared
      tcache := hw.tcache
      init := hw.init
      apart := by
        have hap := hw.apart
        rw [Local.spans_eq] at hap ⊢
        have hb' : hb + (hs - extra) = l.av.tiles.top + (l.av.tiles.topSize - extra) := by
          have : hb < l.av.tiles.start := hlt
          have := ht.topAt hst; omega
        show Apart ((l.av.tiles.heapChunks.map (fun c => (c.addr, c.size)) ++
            (if l.av.tiles.start = 0 then [] else [(l.av.tiles.top, l.av.tiles.topSize - extra)])) ++
          ((((hb, hs - extra) :: rest).map (fun hp => (hp.1, 1)) ++
            (if l.av.reserve + extra = 0 then [] else [(hb + (hs - extra), l.av.reserve + extra)])) ++
            l.shared.mm.chunks.map (fun c => (c.addr, c.size))))
        have hap' : Apart ((l.av.tiles.heapChunks.map (fun c => (c.addr, c.size)) ++
            (if l.av.tiles.start = 0 then [] else [(l.av.tiles.top, l.av.tiles.topSize)])) ++
          ((((hb, hs) :: rest).map (fun hp => (hp.1, 1)) ++
            (if l.av.reserve = 0 then [] else [(hb + hs, l.av.reserve)])) ++
            l.shared.mm.chunks.map (fun c => (c.addr, c.size)))) := by
          have e : l.hf.av.heaps = (hb, hs) :: rest := hh
          unfold TopSt.spans ArenaSt.heapSpans at hap; rw [e] at hap; exact hap
        simp only [hst, ↓reduceIte, List.map_cons] at hap' ⊢
        rw [hend.symm] at hap'
        rw [hb']
        exact apart_boundary hap' (by omega) (by omega)
      mmSize := hw.mmSize
      heap := fun _ => hH'.congr rfl rfl rfl rfl (Nat.le_refl _)
      main := fun hm => (hnm' _ rfl hm).elim
      sysMain := fun hm => (hnm' _ rfl hm).elim }, rfl, rfl, rfl⟩

end Silmaril.Libc.Ptmalloc.Algo
