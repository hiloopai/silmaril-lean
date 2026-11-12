module

public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocSys
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.FreeBody
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocCons

/-!
# ptmalloc algorithm: `sysmalloc` on a non-main arena

**`Algo.sysHeapBody : Task.algo.sysHeapBody C`** and **`Algo.sysHeapTotal`**: `sysmallocHeap`
(`grow_heap` of the current heap, else `new_heap` with the old top closed and freed, else the
`mmap` path as a last resort, then the final carve) on a view with its spatial facts.

The non-main facts (`HeapWF`, `ArenaSt.heapSpans`): the current heap ends at the top chunk's
end, its `HEAP_MAX_SIZE` reservation past the heap is the arena's own span (`reserve`), and heap
addresses are distinct (their first bytes are spans), so `system_mem ≤ Σ sizes ≤ 2 ^ 47`.

* `grow_step`: `grow_heap` moves the boundary between top and the reservation
  (`apart_boundary`, `cover_boundary`), an `MStep` with a `Shrink`-frame;
* `newHeap_close`: `new_heap`'s fresh mapping and `closeSegment` (a `Frame` from fresh kernel
  memory, `frame_of_fresh`), then `_int_free` of the old top (`Algo.bodyFree`, `Frame.trans_free`);
* `heapLastResort_body`: the `mmap` path or the carve.

`Algo.bodyMalloc_main`, `Algo.totalMalloc_main`: `Task.algo.bodyMalloc`/`totalMalloc` conditional
only on `sysmalloc`'s main-arena part (`Task.algo.sysMainBody`, `sysMainTotal`).
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

variable {C : Config}

/-! ## Heap addresses and `system_mem` -/

theorem nodup_lt_length {K : List Nat} {n : Nat} (hn : K.Nodup) (hk : ∀ x ∈ K, x < n) :
    K.length ≤ n := by
  have := hn.length_le_of_subset (l₂ := List.range n) (fun x hx => List.mem_range.mpr (hk x hx))
  simpa using this

/-- Distinct `M`-aligned heaps of at most `M` bytes, each reservation below `U`, hold at most `U`
bytes. -/
theorem heaps_sum_le {L : List (Nat × Nat)} {M U : Nat} (hM : 0 < M) (hn : (L.map (·.1)).Nodup)
    (ha : ∀ hp ∈ L, hp.1 % M = 0 ∧ hp.1 + M ≤ U ∧ hp.2 ≤ M) : (L.map (·.2)).sum ≤ U := by
  have h1 : ∀ L : List (Nat × Nat), (∀ hp ∈ L, hp.2 ≤ M) → (L.map (·.2)).sum ≤ L.length * M := by
    intro L hL
    induction L with
    | nil => simp
    | cons hp t ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
      have := hL hp (List.mem_cons_self ..)
      have := ih (fun q hq => hL q (List.mem_cons_of_mem _ hq))
      omega
  have h2 : L.length ≤ U / M := by
    have hK : ((L.map (·.1)).map (· / M)).Nodup := by
      refine nodup_map_on (fun x hx y hy hxy => ?_) hn
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
      have e1 := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero (ha p hp).1)
      have e2 := Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero (ha q hq).1)
      rw [← e1, ← e2, hxy]
    have := nodup_lt_length hK (n := U / M) (fun x hx => by
      obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
      have h3 : (p.1 + M) / M ≤ U / M := Nat.div_le_div_right (ha p hp).2.1
      rw [Nat.add_div_right _ hM] at h3
      omega)
    simpa using this
  have h3 := h1 L (fun hp hm => (ha hp hm).2.2)
  have h4 : L.length * M ≤ U := Nat.le_trans (Nat.mul_le_mul_right M h2) (Nat.div_mul_le_self U M)
  omega

/-- The heap addresses of a view are distinct: their first bytes are apart spans. -/
theorem heaps_nodup {l : Local} (hap : Apart l.spans) : (l.av.heaps.map (·.1)).Nodup := by
  have hs : (l.av.heaps.map (fun hp => (hp.1, 1))).Sublist l.spans := by
    rw [Local.spans_eq]
    refine List.Sublist.trans ?_ (List.sublist_append_right _ _)
    refine List.Sublist.trans ?_ (List.sublist_append_left _ _)
    unfold ArenaSt.heapSpans
    exact List.sublist_append_left _ _
  have := (hap.sublist hs).1
  rw [List.pairwise_map] at this
  unfold List.Nodup
  rw [List.pairwise_map]
  exact this.imp fun h e => by simp only at h; omega

theorem heapMax_pos (hC : C.Ok) : 0 < C.heapMaxSize := by
  have := hC.arena.2.2.2; rw [hC.page] at this; omega

/-! ## Moving the boundary between top and the reservation -/

theorem in_boundary {Ch Mk M : List (Nat × Nat)} {t a r x : Nat} (h1 : t ≤ x) (h2 : x < t + a + r) :
    InSpans ((Ch ++ [(t, a)]) ++ ((Mk ++ (if r = 0 then [] else [(t + a, r)])) ++ M)) x := by
  by_cases hx : x < t + a
  · exact ⟨(t, a), List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton_self _)), h1, hx⟩
  · have hr : r ≠ 0 := by omega
    refine ⟨(t + a, r), ?_, by simp only; omega, by simp only; omega⟩
    refine List.mem_append_right _ (List.mem_append_left _ (List.mem_append_right _ ?_))
    simp [hr]

/-- **Moving the boundary between top and the reservation gives no byte.** -/
theorem cover_boundary {Ch Mk M : List (Nat × Nat)} {t a r a' r' : Nat} (hsum : a' + r' = a + r)
    {x : Nat} (h : InSpans ((Ch ++ [(t, a')]) ++ ((Mk ++ (if r' = 0 then [] else [(t + a', r')])) ++ M)) x) :
    InSpans ((Ch ++ [(t, a)]) ++ ((Mk ++ (if r = 0 then [] else [(t + a, r)])) ++ M)) x := by
  obtain ⟨s, hs, h1, h2⟩ := h
  rcases List.mem_append.mp hs with hs | hs
  · rcases List.mem_append.mp hs with hs | hs
    · exact ⟨s, List.mem_append_left _ (List.mem_append_left _ hs), h1, h2⟩
    · rw [List.mem_singleton] at hs; subst hs; simp only at h1 h2
      exact in_boundary h1 (by omega)
  · rcases List.mem_append.mp hs with hs | hs
    · rcases List.mem_append.mp hs with hs | hs
      · exact ⟨s, List.mem_append_right _ (List.mem_append_left _ (List.mem_append_left _ hs)), h1, h2⟩
      · split at hs
        · simp at hs
        · rw [List.mem_singleton] at hs; subst hs; simp only at h1 h2
          exact in_boundary (by omega) (by omega)
    · exact ⟨s, List.mem_append_right _ (List.mem_append_right _ hs), h1, h2⟩

/-! ## `grow_heap` -/

/-- The view after a granted `grow_heap` of `diff` bytes (`sysmallocHeap`'s first branch). -/
def growHeap (l : Local) (k : KernelSt) (h hs diff : Nat) : Local :=
  withTiles { l with kernel := k, av := { l.av with heaps := (h, hs + diff) :: l.av.heaps.tail,
                                                    reserve := l.av.reserve - diff } }
    { l.av.tiles with systemMem := l.av.tiles.systemMem + diff, topSize := h + hs + diff - l.av.tiles.top }

theorem growHeap_spans (l : Local) (k : KernelSt) (h hs diff : Nat) {rest : List (Nat × Nat)}
    (hh : l.av.heaps = (h, hs) :: rest) (hst : l.av.tiles.start ≠ 0) :
    (growHeap l k h hs diff).spans =
      (l.av.tiles.heapChunks.map (fun c => (c.addr, c.size)) ++
        [(l.av.tiles.top, h + hs + diff - l.av.tiles.top)]) ++
      ((((h, hs + diff) :: rest).map (fun hp => (hp.1, 1)) ++
        (if l.av.reserve - diff = 0 then [] else [(h + (hs + diff), l.av.reserve - diff)])) ++
        l.shared.mm.chunks.map (fun c => (c.addr, c.size))) := by
  rw [Local.spans_eq]
  unfold TopSt.spans ArenaSt.heapSpans growHeap withTiles
  simp only [hst, ↓reduceIte, hh, List.tail_cons]
  rfl

theorem spans_heap (l : Local) {h hs : Nat} {rest : List (Nat × Nat)}
    (hh : l.av.heaps = (h, hs) :: rest) (hst : l.av.tiles.start ≠ 0) :
    l.spans =
      (l.av.tiles.heapChunks.map (fun c => (c.addr, c.size)) ++
        [(l.av.tiles.top, l.av.tiles.topSize)]) ++
      ((((h, hs) :: rest).map (fun hp => (hp.1, 1)) ++
        (if l.av.reserve = 0 then [] else [(h + hs, l.av.reserve)])) ++
        l.shared.mm.chunks.map (fun c => (c.addr, c.size))) := by
  rw [Local.spans_eq]
  unfold TopSt.spans ArenaSt.heapSpans
  simp only [hst, ↓reduceIte, hh]

/-- **A granted `grow_heap`** is an `MStep`: top grows into the reservation. -/
theorem grow_step (hC : C.Ok) {l : Local} (hw : LocalWF C l) (hsp : LocalSp C l)
    (hnm : l.isMain = false) {h hs diff : Nat} {rest : List (Nat × Nat)}
    (hh : l.av.heaps = (h, hs) :: rest) (hdiff : diff % C.page = 0)
    (hle : hs + diff ≤ C.heapMaxSize) {k : KernelSt} (hk : l.kernel.mprotect = (true, k)) :
    MStep C l (growHeap l k h hs diff) := by
  have hH := hw.heap hnm
  obtain ⟨hlt, hend, hres⟩ := hH.cur_of hh
  have hT := hw.arena.tiles
  have hst : l.av.tiles.start ≠ 0 := by omega
  have htop := hT.topAt hst
  have hsT : l.av.tiles.start ≤ l.av.tiles.top := by rw [htop]; omega
  have hA := hC.align; have hP := hC.page
  have htA := hT.topAligned
  have hz : h + hs + diff - l.av.tiles.top = l.av.tiles.topSize + diff := by omega
  have hdr : diff ≤ l.av.reserve := by omega
  -- the heap sum bound
  have hn : (l.av.heaps.map (·.1)).Nodup := heaps_nodup hw.apart
  have hn' : ((((h, hs + diff) :: rest) : List (Nat × Nat)).map (·.1)).Nodup := by
    rw [hh] at hn; simpa using hn
  have hsum := heaps_sum_le (heapMax_pos hC) hn' (U := KernelSt.userTop) (fun hp hm => by
    rcases List.mem_cons.mp hm with rfl | hm
    · obtain ⟨a1, a2, -⟩ := hH.addrs (h, hs) (by rw [hh]; exact List.mem_cons_self ..)
      exact ⟨a1, a2, hle⟩
    · exact hH.addrs hp (by rw [hh]; exact List.mem_cons_of_mem _ hm))
  have hsm := hH.sysMem
  rw [hh] at hsm
  simp only [List.map_cons, List.sum_cons] at hsm hsum
  obtain ⟨-, hU, -⟩ := hH.addrs (h, hs) (by rw [hh]; exact List.mem_cons_self ..)
  have hut : KernelSt.userTop = 2 ^ 47 := rfl
  -- the tiling
  have hT' : TopWF C { l.av.tiles with systemMem := l.av.tiles.systemMem + diff, topSize := h + hs + diff - l.av.tiles.top } :=
    { sizes := hT.sizes, aligned := hT.aligned, nonNull := hT.nonNull, topAt := hT.topAt
      topAligned := by
        refine ⟨htA.1, ?_⟩; simp only; rw [hz]; rw [hA] at htA ⊢; rw [hP] at hdiff; omega
      topMin := fun h0 => by simp only; have := hT.topMin h0; omega
      coalesced := hT.coalesced, lastUsed := hT.lastUsed, coalescedOld := hT.coalescedOld
      sysMem := by
        have := hT.sysMem
        show (l.av.tiles.heapChunks.map (·.size)).sum + (h + hs + diff - l.av.tiles.top) ≤
          l.av.tiles.systemMem + diff
        omega
      sysMemBound := by simp only; omega
      noHeap := fun h0 => absurd h0 hst, nodup := hT.nodup, bound := hT.bound
      topBound := fun _ => by simp only; omega }
  have hA0 := hw.arena.withTilesViews _ hT' rfl rfl rfl
  -- spans
  have hold := hw.apart
  rw [spans_heap l hh hst] at hold
  have hap' : Apart (growHeap l k h hs diff).spans := by
    rw [growHeap_spans l k h hs diff hh hst, hz,
      show h + (hs + diff) = l.av.tiles.top + (l.av.tiles.topSize + diff) by omega]
    rw [show h + hs = l.av.tiles.top + l.av.tiles.topSize by omega] at hold
    simp only [List.map_cons] at hold ⊢
    exact apart_boundary hold (by have := hT.topMin hst; have := hC.minSize; omega) (by omega)
  have hcov : SpanCover l (growHeap l k h hs diff) := by
    intro x hx
    rw [growHeap_spans l k h hs diff hh hst, hz,
      show h + (hs + diff) = l.av.tiles.top + (l.av.tiles.topSize + diff) by omega] at hx
    rw [spans_heap l hh hst, show h + hs = l.av.tiles.top + l.av.tiles.topSize by omega]
    simp only [List.map_cons] at hx ⊢
    exact cover_boundary (by omega) hx
  obtain ⟨hk1, hk2⟩ := mprotect_spec hk
  have hk3 := mprotect_maps hk
  have hwl : LocalWF C (growHeap l k h hs diff) :=
    { arena := ⟨hA0.tiles, hA0.fast, hA0.bins, hA0.unsorted, hA0.internal⟩
      shared := hw.shared
      tcache := hw.tcache
      main := fun hm => absurd (hnm.symm.trans hm) (by decide)
      init := fun h0 => absurd (hw.init h0).1 hst
      apart := hap'
      mmSize := hw.mmSize
      sysMain := fun hm => absurd (hnm.symm.trans hm) (by decide)
      heap := fun _ =>
        { cur := ⟨h, hs + diff, rest, by simp [growHeap, withTiles, hh], hlt,
            by simp only [growHeap, withTiles]; omega, by simp only [growHeap, withTiles]; omega⟩
          addrs := fun hp hm => by
            simp only [growHeap, withTiles, hh, List.tail_cons, List.mem_cons] at hm
            rcases hm with rfl | hm
            · obtain ⟨a1, a2, -⟩ := hH.addrs (h, hs) (by rw [hh]; exact List.mem_cons_self ..)
              exact ⟨a1, a2, hle⟩
            · exact hH.addrs hp (by rw [hh]; exact List.mem_cons_of_mem _ hm)
          sysMem := by
            simp only [growHeap, withTiles, hh, List.tail_cons, List.map_cons, List.sum_cons]
            omega } }
  have hS : Shrink l (growHeap l k h hs diff) :=
    ⟨rfl, hcov, fun x hx _ => (kernel_has_congr hk1 hk2 hk3).mpr hx, hk1, fun _ => hk2,
      fun _ => by simp [growHeap, withTiles], hk3⟩
  exact ⟨hwl, List.Perm.refl _,
    frame_of hsp hap' rfl rfl rfl hS (fun c hc _ _ => hc) (fun tc' i e ht he => .inl ⟨tc', i, ht, he⟩),
    fun tc _ _ ht he _ => ⟨tc, ht, he⟩, id⟩

/-! ## Closing the current segment (`new_heap`'s old top) -/

/-- The tiling after closing the current segment with `X` appended (the old top's remains) and a
new current segment at `t'` with a top of `z'` bytes. -/
def closedTiles (ts : TopSt) (t' z' : Nat) (X : List (Nat × Use)) (pd : Nat) : TopSt :=
  { ts with start := t', chunks := [], top := t', topSize := z',
            old := ts.old ++ [{ start := ts.start, chunks := ts.chunks ++ X, pad := pd }] }

/-- What `closeSegment` leaves of the old top (non-main): a client chunk the caller frees, an
`internal` stub, or only padding. -/
def CloseCase (C : Config) (ts : TopSt) (X : List (Nat × Use)) (freed : Option Nat) : Prop :=
  (X = [] ∧ freed = none) ∨
  (∃ s, X = [(s, .internal)] ∧ s % C.align = 0 ∧ C.minSize ≤ s ∧ s ≤ ts.topSize ∧ freed = none) ∨
  (∃ s, X = [(s, .client)] ∧ s % C.align = 0 ∧ C.minSize ≤ s ∧ s ≤ ts.topSize ∧ freed = some ts.top)

theorem closeSegment_cases (hC : C.Ok) (l : Local) (t' z' : Nat) (hs : l.av.tiles.start ≠ 0)
    (hz : C.minSize ≤ l.av.tiles.topSize) :
    ∃ X pd, (closeSegment C l t' z' false).2 = withTiles l (closedTiles l.av.tiles t' z' X pd) ∧
      CloseCase C l.av.tiles X (closeSegment C l t' z' false).1 := by
  have hA := hC.align; have hM := hC.minSize; have hS := hC.sizeSz
  have hhdr : C.hdr = 16 := by unfold Config.hdr; omega
  have hsz : topSz l.av.tiles = l.av.tiles.topSize := by simp [topSz, hs]
  have hos : alignDown (l.av.tiles.topSize - C.minSize) C.align ≤ l.av.tiles.topSize - C.minSize ∧
      alignDown (l.av.tiles.topSize - C.minSize) C.align % C.align = 0 := by
    unfold alignDown; rw [hA]; omega
  unfold closeSegment
  simp only [hsz, Bool.false_eq_true, ↓reduceIte]
  have hkeep : (l.av.tiles.start ≠ 0 ∧ l.av.tiles.topSize ≠ 0) := ⟨hs, by omega⟩
  simp only [hkeep, ne_eq, not_false_eq_true, and_self, ↓reduceIte]
  split
  · rename_i h1
    exact ⟨[(alignDown (l.av.tiles.topSize - C.minSize) C.align, .client)], 0, rfl,
      .inr (.inr ⟨_, rfl, hos.2, h1, by omega, rfl⟩)⟩
  · rename_i h1
    split
    · rename_i h2
      exact ⟨[(alignDown (l.av.tiles.topSize - C.minSize) C.align + C.hdr, .internal)], 0, rfl,
        .inr (.inl ⟨_, rfl, by rw [hhdr]; rw [hA] at hos ⊢; omega, h2, by omega, rfl⟩)⟩
    · exact ⟨[], alignDown (l.av.tiles.topSize - C.minSize) C.align + C.hdr,
        by simp [closedTiles], .inl ⟨rfl, rfl⟩⟩

theorem heapChunks_closed {ts : TopSt} (htop : ts.top = ts.start + runLen ts.chunks) (t' z' : Nat)
    (X : List (Nat × Use)) (pd : Nat) :
    (closedTiles ts t' z' X pd).heapChunks = ts.heapChunks ++ layout ts.top X := by
  unfold TopSt.heapChunks closedTiles
  simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil, layout,
    List.append_assoc]
  rw [layout_append, htop]

theorem closeCase_x {ts : TopSt} {X : List (Nat × Use)} {fr : Option Nat} (h : CloseCase C ts X fr) :
    X = [] ∨ ∃ s u, X = [(s, u)] ∧ s % C.align = 0 ∧ C.minSize ≤ s ∧ s ≤ ts.topSize ∧
      (u = .client ∨ u = .internal) := by
  rcases h with ⟨rfl, -⟩ | ⟨s, rfl, a, b, c, -⟩ | ⟨s, rfl, a, b, c, -⟩
  · exact .inl rfl
  · exact .inr ⟨s, .internal, rfl, a, b, c, .inr rfl⟩
  · exact .inr ⟨s, .client, rfl, a, b, c, .inl rfl⟩

/-- **The closed tiling** is well formed. -/
theorem topWF_closed {ts : TopSt} (hT : TopWF C ts) (hs : ts.start ≠ 0)
    (hfresh : ts.top ∉ ts.heapChunks.map (·.addr)) {X : List (Nat × Use)}
    (hX : X = [] ∨ ∃ s u, X = [(s, u)] ∧ s % C.align = 0 ∧ C.minSize ≤ s ∧ s ≤ ts.topSize ∧
      (u = .client ∨ u = .internal))
    (pd : Nat) {t' z' sm' : Nat} (h0 : t' ≠ 0) (hta : t' % C.align = 0) (hza : z' % C.align = 0)
    (hzm : C.minSize ≤ z') (hsm : ts.systemMem + z' ≤ sm') (hsmb : sm' < 2 ^ 64)
    (htb : t' + z' < 2 ^ 64) :
    TopWF C { closedTiles ts t' z' X pd with systemMem := sm' } := by
  have hc := heapChunks_closed (hT.topAt hs) t' z' X pd
  have hc' : ({ closedTiles ts t' z' X pd with systemMem := sm' } : TopSt).heapChunks =
      ts.heapChunks ++ layout ts.top X := hc
  have htA := hT.topAligned
  have htB := hT.topBound hs
  have hsT : ts.start ≤ ts.top := by rw [hT.topAt hs]; omega
  have hmemX : ∀ c ∈ layout ts.top X, ∃ s u, c = ⟨ts.top, s, u⟩ ∧ s % C.align = 0 ∧
      C.minSize ≤ s ∧ s ≤ ts.topSize ∧ (u = .client ∨ u = .internal) := by
    intro c hc0
    rcases hX with rfl | ⟨s, u, rfl, a, b, d, e⟩
    · simp [layout] at hc0
    · simp only [layout, List.mem_singleton] at hc0; exact ⟨s, u, hc0, a, b, d, e⟩
  have hsumX : ((layout ts.top X).map (·.size)).sum ≤ ts.topSize := by
    rcases hX with rfl | ⟨s, u, rfl, -, -, d, -⟩
    · simp [layout]
    · simp [layout]; exact d
  refine
    { sizes := ?_, aligned := ?_, nonNull := ?_, topAt := fun _ => by simp [closedTiles],
      topAligned := ⟨hta, hza⟩, topMin := fun _ => hzm, coalesced := rfl,
      lastUsed := by simp [closedTiles], coalescedOld := ?_, sysMem := ?_, sysMemBound := hsmb,
      noHeap := fun h => absurd h h0, nodup := ?_, bound := ?_, topBound := fun _ => htb }
  · intro c hcm; rw [hc'] at hcm
    rcases List.mem_append.mp hcm with hcm | hcm
    · exact hT.sizes c hcm
    · obtain ⟨s, u, rfl, a, b, -, -⟩ := hmemX c hcm; exact ⟨a, b⟩
  · intro c hcm; rw [hc'] at hcm
    rcases List.mem_append.mp hcm with hcm | hcm
    · exact hT.aligned c hcm
    · obtain ⟨s, u, rfl, -⟩ := hmemX c hcm; exact htA.1
  · intro c hcm; rw [hc'] at hcm
    rcases List.mem_append.mp hcm with hcm | hcm
    · exact hT.nonNull c hcm
    · obtain ⟨s, u, rfl, -⟩ := hmemX c hcm; show ts.top ≠ 0; omega
  · intro g hg
    simp only [closedTiles, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hT.coalescedOld g hg
    · show coalescedB (ts.chunks ++ X) = true
      rcases hX with rfl | ⟨s, u, rfl, -, -, -, hu⟩
      · rw [List.append_nil]; exact hT.coalesced
      · rw [coalescedB_mid_used _ _ _ (by rcases hu with rfl | rfl <;> rfl)]
        exact ⟨hT.coalesced, rfl⟩
  · rw [hc', List.map_append, List.sum_append]
    have := hT.sysMem
    show _ + _ + z' ≤ sm'
    omega
  · rw [hc', List.map_append, List.nodup_append]
    refine ⟨hT.nodup, ?_, ?_⟩
    · rcases hX with rfl | ⟨s, u, rfl, -⟩ <;> simp [layout]
    · intro a ha b hb hab
      obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp hb
      obtain ⟨s, u, rfl, -⟩ := hmemX c hcm
      subst hab; exact hfresh ha
  · intro c hcm; rw [hc'] at hcm
    rcases List.mem_append.mp hcm with hcm | hcm
    · exact hT.bound c hcm
    · obtain ⟨s, u, rfl, -, -, d, -⟩ := hmemX c hcm; show ts.top + s < 2 ^ 64; omega

/-! ## A frame from fresh kernel memory -/

theorem placeable_not_has {k : KernelSt} {al a n : Nat} (hp : k.Placeable al a n) {x : Nat}
    (h1 : a ≤ x) (h2 : x < a + n) : ¬ k.Has x := by
  obtain ⟨-, -, -, hfree, hbrk, -⟩ := hp
  rintro (⟨b1, b2⟩ | ⟨m, hm, m1, m2⟩)
  · omega
  · have := hfree m hm; omega

/-- **A body step whose new bytes are old bytes or fresh kernel memory** `[a, a + n)` (not the
process's before, the process's after) has a `Frame`. -/
theorem frame_of_fresh {l l' : Local} {a n : Nat} (hsp : LocalSp C l) (hap' : Apart l'.spans)
    (ha : l'.avAddr = l.avAddr) (hm : l'.isMain = l.isMain) (hsh : l'.shared = l.shared)
    (harena : l'.thread.arena = l.thread.arena) (htc : l'.thread.tcache = l.thread.tcache)
    (hk1 : l'.kernel.brkStart = l.kernel.brkStart) (hk2 : l'.kernel.brk = l.kernel.brk)
    (hk3 : ∀ m ∈ l.kernel.maps, m ∈ l'.kernel.maps) (htot : l.kernel.total ≤ l'.kernel.total)
    (hfr : ∀ x, a ≤ x → x < a + n → ¬ l.kernel.Has x)
    (hnew : ∀ x, a ≤ x → x < a + n → l'.kernel.Has x)
    (hcov : ∀ x, InSpans l'.spans x → InSpans l.spans x ∨ (a ≤ x ∧ x < a + n))
    (hheaps : l.av.heaps ≠ [] → l'.av.heaps ≠ [])
    (hcl : ∀ c ∈ l.av.chunks, c.use = .client → c ∈ l'.av.chunks) : Frame C l l' [] where
  avAddr := ha
  isMain := hm
  spatial r _ hc haw := by
    refine ⟨covers_mono hk1 hk2 hk3 hc, fun s hs' => ?_⟩
    refine Classical.byContradiction fun hne => ?_
    have hs0 := hap'.2 s hs'
    have key : ∀ x, s.1 ≤ x → x < s.1 + s.2 → r.1 ≤ x → x < r.1 + r.2 → False := by
      intro x x1 x2 x3 x4
      rcases hcov x ⟨s, hs', x1, x2⟩ with ⟨s0, h0, a1, a2⟩ | ⟨a1, a2⟩
      · have := haw s0 h0; omega
      · exact hfr x a1 a2 (hc x x3 x4)
    rcases Nat.le_total r.1 s.1 with hle | hle
    · exact key s.1 (Nat.le_refl _) (by omega) hle (by omega)
    · exact key r.1 hle (by omega) (Nat.le_refl _) (by omega)
  covered s hs' x h1 h2 := by
    rcases hcov x ⟨s, hs', h1, h2⟩ with ⟨s0, h0, a1, a2⟩ | ⟨a1, a2⟩
    · exact has_mono hk1 hk2 hk3 (hsp.covered s0 h0 x a1 a2)
    · exact hnew x a1 a2
  brkStart := hk1
  nonMain _ := ⟨hk2, by rw [hsh]⟩
  acct _ := by rw [hsh]; omega
  init := by rw [hsh]
  arenas := by rw [hsh]; exact ⟨rfl, rfl, rfl⟩
  arena := harena
  heaps := hheaps
  clients c hc hu _ := hcl c hc hu
  fresh tc' i e ht he := by rw [htc] at ht; exact .inl ⟨tc', i, ht, he⟩

/-- **Freeing a chunk that the step before made** composes with that step's frame. -/
theorem Frame.trans_free {l l₁ l₂ : Local} {x : Nat × Nat} (h₁ : Frame C l l₁ [])
    (h₂ : Frame C l₁ l₂ [x]) (hx : ∀ c ∈ l.av.chunks, c.addr + C.hdr ≠ x.1)
    (hsub : ∀ c ∈ l.av.chunks, c ∈ l₁.av.chunks) (htc₁ : l₁.thread.tcache = l.thread.tcache) :
    Frame C l l₂ [] where
  avAddr := h₂.avAddr.trans h₁.avAddr
  isMain := h₂.isMain.trans h₁.isMain
  spatial r h0 hc ha :=
    let h := h₁.spatial r h0 hc ha
    h₂.spatial r h0 h.1 h.2
  covered := h₂.covered
  brkStart := h₂.brkStart.trans h₁.brkStart
  nonMain hm := by
    have a := h₁.nonMain hm
    have b := h₂.nonMain (by rw [h₁.isMain]; exact hm)
    exact ⟨b.1.trans a.1, b.2.trans a.2⟩
  acct hm := by
    have a := h₁.acct hm
    have b := h₂.acct (by rw [h₁.isMain]; exact hm)
    omega
  init := h₂.init.trans h₁.init
  arenas := ⟨h₂.arenas.1.trans h₁.arenas.1, h₂.arenas.2.1.trans h₁.arenas.2.1,
    h₂.arenas.2.2.trans h₁.arenas.2.2⟩
  arena := h₂.arena.trans h₁.arena
  heaps h := h₂.heaps (h₁.heaps h)
  clients c hc hu _ := h₂.clients c (h₁.clients c hc hu (by simp)) hu (by
    simp only [List.mem_singleton]; intro he; exact hx c hc (by rw [← he]))
  fresh tc'' i e ht he := by
    rcases h₂.fresh tc'' i e ht he with ⟨tc', j, ht', he'⟩ | ⟨hc, hfr⟩
    · rw [htc₁] at ht'; exact .inl ⟨tc', j, ht', he'⟩
    · refine .inr ⟨hc, .inr fun c hc' hca hcu => ?_⟩
      rcases hfr with hfr | hfr
      · simp only [List.mem_singleton] at hfr
        exact hx c hc' (by rw [← hfr, hca])
      · exact hfr c (hsub c hc') hca hcu

/-! ## `new_heap` and the old top -/

/-- The view after a granted `new_heap` of `hsize` bytes at `h'`, before the old top is closed. -/
def newHeapL (C : Config) (l : Local) (k : KernelSt) (h' hsize : Nat) : Local :=
  withTiles { l with kernel := k, av := { l.av with heaps := (h', hsize) :: l.av.heaps, reserve := C.heapMaxSize - hsize } }
    { l.av.tiles with systemMem := l.av.tiles.systemMem + hsize }

theorem view_closed (p : Use → Bool) (hp : p .client = false) (hp' : p .internal = false)
    (cs : List Chunk) (a : Nat) {X : List (Nat × Use)} {z : Nat}
    (hX : X = [] ∨ ∃ s u, X = [(s, u)] ∧ s % C.align = 0 ∧ C.minSize ≤ s ∧ s ≤ z ∧
      (u = .client ∨ u = .internal)) :
    Chunk.view p (cs ++ layout a X) = Chunk.view p cs := by
  unfold Chunk.view; rw [List.filter_append]
  rcases hX with rfl | ⟨s, u, rfl, -, -, -, hu⟩
  · simp [layout]
  · rcases hu with rfl | rfl <;> simp [layout, hp, hp']

/-- `_int_free` with no tcache leaves the tcache absent. -/
theorem intFree_tc_none (hC : C.Ok) {l l' : Local} (hw : LocalWF C l) {p u : Nat}
    (hpu : (p, u) ∈ l.arenaLive C) (hn : l.thread.tcache = none)
    (h : intFree C l (p - C.hdr) = .ok l') : l'.thread.tcache = none := by
  obtain ⟨ch, hch, hcu, rfl, rfl, -, hf, h1, h2⟩ := intFree_open hC hw hpu
  have hpc : ch.addr + C.hdr - C.hdr = ch.addr := by omega
  rw [hpc, intFree_eq hf hcu h1 h2, hn] at h
  simp only [freeRest] at h
  split at h
  · split at h
    · cases h
    · cases h; exact hn
  · obtain ⟨-, -, -, ht, -⟩ := freeMerge_spec hC hw hch hcu h
    rw [ht]; exact hn

/-- **`new_heap` and the old top closed** (non-main): well formed, a `Frame` from the fresh
mapping, and the live set grown by the old top when `closeSegment` hands it to `_int_free`. -/
theorem newHeap_close (hC : C.Ok) {l : Local} (hw : LocalWF C l) (hsp : LocalSp C l)
    (hnm : l.isMain = false) {k : KernelSt} {h' hsize : Nat}
    (hk : l.kernel.mmap C.heapMaxSize C.heapMaxSize = (some h', k))
    (hhs : hsize ≤ C.heapMaxSize) (hpg : hsize % C.page = 0)
    (hmin : C.heapInfoSize + C.minSize ≤ hsize) {fr : Option Nat} {lc : Local}
    (hcs : closeSegment C (newHeapL C l k h' hsize) (h' + C.heapInfoSize) (hsize - C.heapInfoSize) false =
      (fr, lc)) :
    LocalWF C lc ∧ Frame C l lc [] ∧ lc.thread = l.thread ∧
      (∀ c ∈ l.av.chunks, c ∈ lc.av.chunks) ∧ (∀ c ∈ l.av.chunks, c.addr ≠ l.av.tiles.top) ∧
      ((fr = none ∧ (lc.live C).Perm (l.live C)) ∨
       (∃ u, fr = some l.av.tiles.top ∧ (l.av.tiles.top + C.hdr, u) ∈ lc.arenaLive C ∧
         (lc.live C).Perm ((l.av.tiles.top + C.hdr, u) :: l.live C))) := by
  have hH := hw.heap hnm
  obtain ⟨h0, hs0, rest, hh, hlt0, hend, hres⟩ := hH.cur
  have hT := hw.arena.tiles
  have hst : l.av.tiles.start ≠ 0 := by omega
  have htm := hT.topMin hst
  have htB := hT.topBound hst
  have hA := hC.align; have hM := hC.minSize; have hP := hC.page; have hS := hC.sizeSz
  have hhdr : C.hdr = 16 := by unfold Config.hdr; omega
  have hinfo := hC.heapInfoPos; have hinfoA := hC.heapInfo.1
  obtain ⟨hk1, hk2, hk3, hpl⟩ := mmap_some hk
  obtain ⟨hp0, hpal, hpu, -, -, -⟩ := id hpl
  have hut : KernelSt.userTop = 2 ^ 47 := rfl
  have hMp := heapMax_pos hC
  have h16 : h' % C.align = 0 := by
    have hd1 : C.heapMaxSize ∣ h' := Nat.dvd_of_mod_eq_zero hpal
    have hd2 : 16 ∣ C.heapMaxSize := by
      have := hC.arena.2.2.1; rw [hC.page] at this
      exact Nat.dvd_trans ⟨256, rfl⟩ (Nat.dvd_of_mod_eq_zero this)
    rw [hA]; exact Nat.mod_eq_zero_of_dvd (Nat.dvd_trans hd2 hd1)
  -- the closed segment
  obtain ⟨X, pd, hcl, hcase⟩ := closeSegment_cases hC (newHeapL C l k h' hsize) (h' + C.heapInfoSize)
    (hsize - C.heapInfoSize) hst htm
  rw [hcs] at hcl hcase
  simp only at hcl hcase
  change CloseCase C l.av.tiles X fr at hcase
  have hX := closeCase_x hcase
  have hzp := top_pos hw hst
  have hfresh : l.av.tiles.top ∉ l.av.tiles.heapChunks.map (·.addr) := by
    intro hm
    obtain ⟨c, hc', hca⟩ := List.mem_map.mp hm
    have := top_apart_chunk hw hst hc'
    have := (hT.sizes c hc').2
    omega
  have htop0 : l.av.tiles.top ≠ 0 := by have := hT.topAt hst; omega
  have hnot : ∀ c ∈ l.av.chunks, c.addr ≠ l.av.tiles.top := fun c hc hca =>
    hfresh (List.mem_map.mpr ⟨c, hc, hca⟩)
  -- the heap sum
  have hnold := heaps_nodup hw.apart
  have hnotin : h' ∉ l.av.heaps.map (·.1) := by
    intro hm
    obtain ⟨hp, hpm, hpe⟩ := List.mem_map.mp hm
    have hmk : (hp.1, 1) ∈ l.spans := by
      rw [Local.spans_eq]
      refine List.mem_append_right _ (List.mem_append_left _ ?_)
      unfold ArenaSt.heapSpans
      exact List.mem_append_left _ (List.mem_map_of_mem (f := fun hp : Nat × Nat => (hp.1, 1)) hpm)
    have hcv := hsp.covered _ hmk hp.1 (Nat.le_refl _) (by simp)
    exact placeable_not_has hpl (x := hp.1) (by omega) (by omega) hcv
  have hn' : (((h', hsize) :: l.av.heaps).map (·.1)).Nodup := by
    rw [List.map_cons, List.nodup_cons]; exact ⟨hnotin, hnold⟩
  have hsum := heaps_sum_le hMp hn' (U := KernelSt.userTop) (fun hp hm => by
    rcases List.mem_cons.mp hm with rfl | hm
    · exact ⟨hpal, hpu, hhs⟩
    · exact hH.addrs hp hm)
  simp only [List.map_cons, List.sum_cons] at hsum
  have hsm := hH.sysMem
  -- the new tiling
  have hT' := topWF_closed hT hst hfresh hX pd (t' := h' + C.heapInfoSize)
    (z' := hsize - C.heapInfoSize) (sm' := l.av.tiles.systemMem + hsize) (by omega)
    (by rw [hA] at h16 hinfoA ⊢; omega) (by rw [hA] at hinfoA ⊢; rw [hP] at hpg; omega)
    (by omega) (by omega) (by omega) (by omega)
  have hcc := heapChunks_closed (hT.topAt hst) (h' + C.heapInfoSize) (hsize - C.heapInfoSize) X pd
  have hv : ∀ p : Use → Bool, p .client = false → p .internal = false →
      Chunk.view p ({ closedTiles l.av.tiles (h' + C.heapInfoSize) (hsize - C.heapInfoSize) X pd with
        systemMem := l.av.tiles.systemMem + hsize } : TopSt).heapChunks =
        Chunk.view p l.av.tiles.heapChunks := fun p hp hp' => by
    show Chunk.view p (closedTiles l.av.tiles (h' + C.heapInfoSize) (hsize - C.heapInfoSize) X pd).heapChunks = _
    rw [hcc]; exact view_closed p hp hp' _ _ hX
  have hA0 := hw.arena.withTilesViews _ hT' (hv _ rfl rfl) (hv _ rfl rfl) (hv _ rfl rfl)
  -- facts about `lc`
  have htl : lc.av.tiles = { closedTiles l.av.tiles (h' + C.heapInfoSize) (hsize - C.heapInfoSize) X pd with
      systemMem := l.av.tiles.systemMem + hsize } := by rw [hcl]; rfl
  have hlch : lc.av.tiles.heapChunks = l.av.tiles.heapChunks ++ layout l.av.tiles.top X := by
    rw [htl]; exact hcc
  have hal : lc.av.heaps = (h', hsize) :: l.av.heaps := by rw [hcl]; rfl
  have hlr : lc.av.reserve = C.heapMaxSize - hsize := by rw [hcl]; rfl
  have hlk : lc.kernel = k := by rw [hcl]; rfl
  have hlth : lc.thread = l.thread := by rw [hcl]; rfl
  have hlsh : lc.shared = l.shared := by rw [hcl]; rfl
  have hlm : lc.isMain = l.isMain := by rw [hcl]; rfl
  have hla : lc.avAddr = l.avAddr := by rw [hcl]; rfl
  have hlA : ArenaWF C lc.av := by
    rw [hcl]; exact ⟨hA0.tiles, hA0.fast, hA0.bins, hA0.unsorted, hA0.internal⟩
  -- the spans
  generalize hCH : l.av.tiles.heapChunks.map (fun c => (c.addr, c.size)) = CH
  generalize hXL : (layout l.av.tiles.top X).map (fun c => (c.addr, c.size)) = XL
  generalize hMK : l.av.heaps.map (fun hp => (hp.1, 1)) = MK
  generalize hMM : l.shared.mm.chunks.map (fun c => (c.addr, c.size)) = MM
  generalize hR' : (if C.heapMaxSize - hsize = 0 then [] else [(h' + hsize, C.heapMaxSize - hsize)]) = R'
  have hspc : lc.spans = (CH ++ XL ++ [(h' + C.heapInfoSize, hsize - C.heapInfoSize)]) ++
      (((h', 1) :: MK ++ R') ++ MM) := by
    rw [Local.spans_eq]
    unfold TopSt.spans ArenaSt.heapSpans
    rw [hlch, hal, hlr, hlsh, htl]
    simp only [closedTiles, show h' + C.heapInfoSize ≠ 0 by omega, ↓reduceIte, List.map_append,
      List.map_cons, ← hCH, ← hXL, ← hMK, ← hMM, ← hR']
  obtain ⟨R0, hR0⟩ : ∃ R0, l.av.heapSpans = MK ++ R0 := ⟨_, by unfold ArenaSt.heapSpans; rw [hMK]⟩
  have hspl : l.spans = (CH ++ [(l.av.tiles.top, l.av.tiles.topSize)]) ++ ((MK ++ R0) ++ MM) := by
    rw [spans_eq_top hst, hR0, hCH, hMM]
  have hXLin : ∀ s ∈ XL, s.1 = l.av.tiles.top ∧ C.minSize ≤ s.2 ∧ s.2 ≤ l.av.tiles.topSize := by
    intro s hs; rw [← hXL] at hs
    rcases hX with rfl | ⟨z, u, rfl, -, a, b, -⟩
    · simp [layout] at hs
    · simp only [layout, List.map_cons, List.map_nil, List.mem_singleton] at hs; subst hs
      exact ⟨rfl, a, b⟩
  have hXLap : Apart XL := by
    rw [← hXL]
    rcases hX with rfl | ⟨z, u, rfl, -, a, b, -⟩
    · simp [layout, Apart]
    · simp only [layout, List.map_cons, List.map_nil]
      exact ⟨List.pairwise_singleton _ _, fun r hr => by
        simp only [List.mem_singleton] at hr; subst hr; simp only; omega⟩
  have hA1 : Apart ((CH ++ MK ++ MM) ++ XL) := by
    have h0 := hw.apart
    rw [hspl] at h0
    refine h0.perm_cover (perm_boundary _ _ _ _ _) hXLap ?_ (List.Perm.refl _)
    intro s hs x h1 h2
    obtain ⟨e1, -, e2⟩ := hXLin s hs
    exact ⟨_, List.mem_cons_self .., by simp only; omega, by simp only; omega⟩
  -- every old range (and the old top's remains) is the process's and not empty
  have hold : ∀ s ∈ (CH ++ MK ++ MM) ++ XL, l.kernel.Covers s ∧ 0 < s.2 := by
    intro s hs
    rcases List.mem_append.mp hs with hs | hs
    · have hs' : s ∈ l.spans := by
        rw [hspl]; simp only [List.mem_append] at hs ⊢
        rcases hs with (hs | hs) | hs
        · exact .inl (.inl hs)
        · exact .inr (.inl (.inl hs))
        · exact .inr (.inr hs)
      exact ⟨hsp.covered s hs', hw.apart.2 s hs'⟩
    · obtain ⟨e1, e2, e3⟩ := hXLin s hs
      have htm' : (l.av.tiles.top, l.av.tiles.topSize) ∈ l.spans := by rw [spans_eq_top hst]; simp
      exact ⟨fun x x1 x2 => hsp.covered _ htm' x (by simp only; omega) (by simp only; omega),
        by omega⟩
  -- the fresh ranges
  have hNin : ∀ n ∈ (h' + C.heapInfoSize, hsize - C.heapInfoSize) :: (h', 1) :: R',
      h' ≤ n.1 ∧ n.1 + n.2 ≤ h' + C.heapMaxSize ∧ 0 < n.2 := by
    intro n hn
    rcases List.mem_cons.mp hn with rfl | hn
    · simp only; omega
    rcases List.mem_cons.mp hn with rfl | hn
    · simp only; omega
    rw [← hR'] at hn
    split at hn
    · simp at hn
    · simp only [List.mem_singleton] at hn; subst hn; simp only; omega
  have hNap : Apart ((h' + C.heapInfoSize, hsize - C.heapInfoSize) :: (h', 1) :: R') := by
    refine ⟨?_, fun n hn => (hNin n hn).2.2⟩
    rw [← hR']
    split
    · simp only [List.pairwise_cons, List.mem_cons, forall_eq, List.not_mem_nil, false_imp_iff,
        implies_true, List.Pairwise.nil, and_true, or_false]
      omega
    · simp only [List.pairwise_cons, List.mem_cons, forall_eq_or_imp, forall_eq, List.not_mem_nil,
        false_imp_iff, implies_true, List.Pairwise.nil, and_true, or_false]
      omega
  have hcross : ∀ n ∈ (h' + C.heapInfoSize, hsize - C.heapInfoSize) :: (h', 1) :: R',
      ∀ s ∈ (CH ++ MK ++ MM) ++ XL, n.1 + n.2 ≤ s.1 ∨ s.1 + s.2 ≤ n.1 := by
    intro n hn s hs
    obtain ⟨c1, c2⟩ := hold s hs
    have := fresh_away hpl hMp c1 c2
    have := hNin n hn
    omega
  have hperm : (((h' + C.heapInfoSize, hsize - C.heapInfoSize) :: (h', 1) :: R') ++
      ((CH ++ MK ++ MM) ++ XL)).Perm
      ((CH ++ XL ++ [(h' + C.heapInfoSize, hsize - C.heapInfoSize)]) ++ (((h', 1) :: MK ++ R') ++ MM)) :=
    List.perm_iff_count.mpr fun z => by
      simp only [List.count_append, List.count_cons, List.cons_append, List.count_nil]; omega
  have hap' : Apart lc.spans := by
    rw [hspc]; exact (Apart.append hNap hA1 hcross).perm hperm
  -- the frame
  have hcov : ∀ x, InSpans lc.spans x → InSpans l.spans x ∨ (h' ≤ x ∧ x < h' + C.heapMaxSize) := by
    rintro x ⟨s, hs, x1, x2⟩
    rw [hspc] at hs
    rcases List.mem_append.mp (hperm.symm.subset hs) with hs | hs
    · have := hNin s hs; exact .inr ⟨by omega, by omega⟩
    · rcases List.mem_append.mp hs with hs' | hs'
      · refine .inl ⟨s, ?_, x1, x2⟩
        rw [hspl]; simp only [List.mem_append] at hs' ⊢
        rcases hs' with (hs' | hs') | hs'
        · exact .inl (.inl hs')
        · exact .inr (.inl (.inl hs'))
        · exact .inr (.inr hs')
      · obtain ⟨e1, -, e3⟩ := hXLin s hs'
        exact .inl ⟨(l.av.tiles.top, l.av.tiles.topSize), by rw [spans_eq_top hst]; simp,
          show l.av.tiles.top ≤ x by omega, show x < l.av.tiles.top + l.av.tiles.topSize by omega⟩
  have hF : Frame C l lc [] :=
    frame_of_fresh (a := h') (n := C.heapMaxSize) hsp hap' hla hlm hlsh (by rw [hlth])
      (by rw [hlth]) (by rw [hlk, hk1]) (by rw [hlk, hk2])
      (fun m hm => by rw [hlk, hk3]; exact List.mem_cons_of_mem _ hm)
      (by
        have : k.total = l.kernel.total + C.heapMaxSize := by
          unfold KernelSt.total; rw [hk1, hk2, hk3]; simp only [List.map_cons, List.sum_cons]; omega
        rw [hlk]; omega)
      (fun x x1 x2 => placeable_not_has hpl x1 x2)
      (fun x x1 x2 => by rw [hlk]; exact .inr ⟨(h', C.heapMaxSize), by rw [hk3]; exact List.mem_cons_self .., x1, x2⟩)
      hcov (fun _ => by rw [hal]; simp)
      (fun c hc _ => by show c ∈ lc.av.tiles.heapChunks; rw [hlch]; exact List.mem_append_left _ hc)
  -- well formed
  have hwl : LocalWF C lc :=
    { arena := hlA
      shared := by rw [hlsh]; exact hw.shared
      tcache := by rw [hlth]; exact hw.tcache
      main := fun hm => absurd ((hlm.symm.trans hm).symm.trans hnm) (by decide)
      init := fun h0 => absurd (hw.init (by rw [← hlsh]; exact h0)).1 hst
      apart := hap'
      mmSize := by rw [hlsh]; exact hw.mmSize
      sysMain := fun hm => absurd ((hlm.symm.trans hm).symm.trans hnm) (by decide)
      heap := fun _ =>
        { cur := ⟨h', hsize, l.av.heaps, hal, by rw [htl]; show h' < h' + C.heapInfoSize; omega,
            by rw [htl]; show h' + C.heapInfoSize + (hsize - C.heapInfoSize) = h' + hsize; omega,
            by rw [hlr]; omega⟩
          addrs := fun hp hm => by
            rw [hal] at hm
            rcases List.mem_cons.mp hm with rfl | hm
            · exact ⟨hpal, hpu, hhs⟩
            · exact hH.addrs hp hm
          sysMem := by rw [hal, htl]; simp only [List.map_cons, List.sum_cons]; omega } }
  -- the live set
  have hout : lc.av.out C = l.av.out C ++
      (Chunk.view (· = .client) (layout l.av.tiles.top X)).map
        (fun c => (c.addr + C.hdr, usable C c false)) := by
    unfold ArenaSt.out ArenaSt.chunks
    rw [hlch]; unfold Chunk.view; rw [List.filter_append, List.map_append]
  have hlive0 : ∀ ys : List (Nat × Nat), lc.av.out C = l.av.out C ++ ys →
      lc.live C = ((l.av.out C).filter fun pu => !(l.thread.parked C).contains pu) ++
        (ys.filter fun pu => !(l.thread.parked C).contains pu) ++ l.shared.live C := by
    intro ys hys
    unfold Local.live; rw [hys, List.filter_append, hlth, hlsh]
  refine ⟨hwl, hF, hlth, fun c hc => by
      show c ∈ lc.av.tiles.heapChunks; rw [hlch]; exact List.mem_append_left _ hc, hnot, ?_⟩
  rcases hcase with ⟨rfl, rfl⟩ | ⟨z, rfl, -, -, -, rfl⟩ | ⟨z, rfl, -, -, -, rfl⟩
  · refine .inl ⟨rfl, ?_⟩
    rw [hlive0 [] (by rw [hout]; simp [layout, Chunk.view])]
    simp [Local.live]
  · refine .inl ⟨rfl, ?_⟩
    rw [hlive0 [] (by rw [hout]; simp [layout, Chunk.view])]
    simp [Local.live]
  · have hnp : (l.thread.parked C).contains (l.av.tiles.top + C.hdr, z - C.sizeSz) = false := by
      cases htc : l.thread.tcache with
      | none => simp [ThreadSt.parked, htc]
      | some tc =>
        simp only [ThreadSt.parked, htc, Option.map_some, Option.getD_some, TcacheSt.payloads]
        rw [Bool.eq_false_iff]; intro hm
        simp only [List.contains_iff_mem, List.mem_map, List.mem_flatMap, List.mem_range] at hm
        obtain ⟨e, ⟨i, -, he⟩, heq⟩ := hm
        simp only [Prod.mk.injEq] at heq
        exact top_not_entry hC hw hsp hst htc he (by omega)
    have hys : lc.av.out C = l.av.out C ++ [(l.av.tiles.top + C.hdr, z - C.sizeSz)] := by
      rw [hout]; simp [layout, Chunk.view, usable]
    refine .inr ⟨z - C.sizeSz, rfl, ?_, ?_⟩
    · unfold Local.arenaLive
      rw [hys, hlth]
      exact List.mem_filter.mpr ⟨List.mem_append_right _ (List.mem_singleton_self _), by rw [hnp]; rfl⟩
    · rw [hlive0 _ hys, List.filter_cons_of_pos (by rw [hnp]; rfl), List.filter_nil]
      unfold Local.live
      simp only [List.append_assoc, List.singleton_append]
      exact List.perm_middle

/-- **`new_heap`, then `_int_free` of the old top** is an `MStep`. -/
theorem newHeap_step (hC : C.Ok) {l : Local} (hw : LocalWF C l) (hsp : LocalSp C l)
    (hnm : l.isMain = false) {k : KernelSt} {h' hsize : Nat}
    (hk : l.kernel.mmap C.heapMaxSize C.heapMaxSize = (some h', k))
    (hhs : hsize ≤ C.heapMaxSize) (hpg : hsize % C.page = 0)
    (hmin : C.heapInfoSize + C.minSize ≤ hsize) {fr : Option Nat} {lc : Local}
    (hcs : closeSegment C (newHeapL C l k h' hsize) (h' + C.heapInfoSize) (hsize - C.heapInfoSize) false =
      (fr, lc)) {lf : Local} (hfo : freeOldTop C lc fr = .ok lf) : MStep C l lf := by
  obtain ⟨hwc, hF1, hth, hsub, hnot, hcase⟩ := newHeap_close hC hw hsp hnm hk hhs hpg hmin hcs
  have hspc := LocalSp.of_frame hC hw hsp hF1
  have hK1 : KeptAway l lc := fun tc i e ht he _ => ⟨tc, by rw [hth]; exact ht, he⟩
  rcases hcase with ⟨rfl, hperm⟩ | ⟨u, rfl, hmem, hperm⟩
  · cases hfo
    exact ⟨hwc, hperm, hF1, hK1, fun hn => by rw [hth]; exact hn⟩
  · have hfo' : intFree C lc (l.av.tiles.top + C.hdr - C.hdr) = .ok lf := by
      rw [Nat.add_sub_cancel]; exact hfo
    obtain ⟨hwf, hF2, hK2, hp2⟩ := bodyFree C hC lc lf _ u hwc hspc hmem hfo'
    refine ⟨hwf, ?_, Frame.trans_free hF1 hF2 (fun c hc h => hnot c hc (Nat.add_right_cancel h))
      hsub (by rw [hth]), KeptAway.trans hC hw hsp hF1 hK1 hK2,
      fun hn => intFree_tc_none hC hwc hmem (by rw [hth]; exact hn) hfo'⟩
    exact hp2.trans ((hperm.erase _).trans (List.Perm.of_eq (List.erase_cons_head _ _)))

/-- `new_heap`, then `_int_free` of the old top, does not abort. -/
theorem newHeap_total (hC : C.Ok) {l : Local} (hw : LocalWF C l) (hsp : LocalSp C l)
    (hnm : l.isMain = false) {k : KernelSt} {h' hsize : Nat}
    (hk : l.kernel.mmap C.heapMaxSize C.heapMaxSize = (some h', k))
    (hhs : hsize ≤ C.heapMaxSize) (hpg : hsize % C.page = 0)
    (hmin : C.heapInfoSize + C.minSize ≤ hsize) {fr : Option Nat} {lc : Local}
    (hcs : closeSegment C (newHeapL C l k h' hsize) (h' + C.heapInfoSize) (hsize - C.heapInfoSize) false =
      (fr, lc)) : ∃ lf, freeOldTop C lc fr = .ok lf := by
  obtain ⟨hwc, hF1, -, -, -, hcase⟩ := newHeap_close hC hw hsp hnm hk hhs hpg hmin hcs
  have hspc := LocalSp.of_frame hC hw hsp hF1
  rcases hcase with ⟨rfl, -⟩ | ⟨u, rfl, hmem, -⟩
  · exact ⟨lc, rfl⟩
  · obtain ⟨lf, hlf⟩ := totalFree C hC lc hwc hspc _ u hmem
    rw [Nat.add_sub_cancel] at hlf
    exact ⟨lf, hlf⟩

/-! ## The last resort and the whole non-main part -/

/-- **`sysmalloc`'s last resort** on a non-main arena (the `mmap` path when not tried, the carve). -/
theorem heapLastResort_body (hC : C.Ok) {l : Local} (hw : LocalWF C l) (hsp : LocalSp C l)
    (hi : l.shared.init = true) {n nb : Nat} (hnb : C.checkedRequest2size n = some nb) (tried : Bool) :
    MBody C n l (heapLastResort C l nb tried).1 (heapLastResort C l nb tried).2 := by
  unfold heapLastResort
  split
  · exact sysCarve_body hC hw hsp hnb
  · cases hm : sysmallocMmap C l nb with
    | mk r l₁ =>
      cases r with
      | some q => exact sysmallocMmap_body hC hw hsp hi hnb hm
      | none =>
        obtain ⟨k, rfl, h1, h2, h3⟩ := sysmallocMmap_none hm
        have S := kernel_step hw hsp h1 h2 h3
        exact MBody.of_step hC hw hsp S (sysCarve_body hC S.1 (S.sp hC hw hsp) hnb)

theorem alignUp_page_mod (hC : C.Ok) (x : Nat) : alignUp x C.page % C.page = 0 :=
  (alignUp_page' hC x).2

theorem pure_ok {α : Type} {a b : α} (h : (pure a : Res α) = .ok b) : a = b := Except.ok.inj h

theorem MBody.of_eq {n p : Nat} {l l' : Local} {r : Nat × Local} (h : MBody C n l r.1 r.2)
    (e : r = (p, l')) : MBody C n l p l' := by subst e; exact h

/-- `new_heap`'s size for a request of `nb` bytes. -/
def hsizeOf (C : Config) (nb : Nat) : Nat :=
  if alignUp (nb + C.minSize + C.heapInfoSize + C.topPad) C.page ≤ C.heapMaxSize then
    max (alignUp (nb + C.minSize + C.heapInfoSize + C.topPad) C.page) heapMinSize
  else alignUp (nb + C.minSize + C.heapInfoSize) C.page

/-- `sysNewHeap` with its heap size named. -/
def sysNewHeapAt (C : Config) (l : Local) (nb : Nat) (tried : Bool) (hsize : Nat) :
    Res (Nat × Local) := do
  if C.heapMaxSize < hsize then return heapLastResort C l nb tried
  match l.kernel.mmap C.heapMaxSize C.heapMaxSize with
  | (none, k) => return heapLastResort C { l with kernel := k } nb tried
  | (some h', k) =>
    let (freed, lc) := closeSegment C (newHeapL C l k h' hsize) (h' + C.heapInfoSize) (hsize - C.heapInfoSize) false
    let lf ← freeOldTop C lc freed
    return sysCarve C lf nb

theorem sysNewHeap_eq (l : Local) (nb : Nat) (tried : Bool) :
    sysNewHeap C l nb tried = sysNewHeapAt C l nb tried (hsizeOf C nb) := rfl

theorem hsizeOf_props (hC : C.Ok) (nb : Nat) :
    hsizeOf C nb % C.page = 0 ∧ C.heapInfoSize + C.minSize ≤ hsizeOf C nb := by
  have hw1 := alignUp_page' hC (nb + C.minSize + C.heapInfoSize + C.topPad)
  have hw2 := alignUp_page' hC (nb + C.minSize + C.heapInfoSize)
  have hP := hC.page
  unfold hsizeOf heapMinSize
  rw [hP] at hw1 hw2 ⊢
  split
  · rcases Nat.le_total (alignUp (nb + C.minSize + C.heapInfoSize + C.topPad) 4096) 0x8000 with hle | hle
    · rw [Nat.max_eq_right hle]; omega
    · rw [Nat.max_eq_left hle]; omega
  · omega

/-- **`sysNewHeap`** is a body. -/
theorem sysNewHeap_body (hC : C.Ok) {l : Local} (hw : LocalWF C l) (hsp : LocalSp C l)
    (hi : l.shared.init = true) (hnm : l.isMain = false) {n nb : Nat}
    (hnb : C.checkedRequest2size n = some nb) {tried : Bool} {p : Nat} {l' : Local}
    (h : sysNewHeap C l nb tried = .ok (p, l')) : MBody C n l p l' := by
  rw [sysNewHeap_eq] at h
  have hsz := hsizeOf_props hC nb
  generalize hsizeOf C nb = hsize at h hsz
  unfold sysNewHeapAt at h
  split at h
  · exact (heapLastResort_body hC hw hsp hi hnb tried).of_eq (pure_ok h)
  · rename_i hbig
    split at h
    · rename_i k hk
      obtain ⟨h1, h2, h3⟩ := mmap_none hk
      have S := kernel_step hw hsp h1 h2 h3
      exact MBody.of_step hC hw hsp S
        ((heapLastResort_body hC S.1 (S.sp hC hw hsp) hi hnb tried).of_eq (pure_ok h))
    · rename_i h' k hk
      split at h
      rename_i fr lc hcs
      cases hfo : freeOldTop C lc fr with
      | error e => rw [hfo] at h; cases h
      | ok lf =>
        rw [hfo, ok_bind] at h
        have S := newHeap_step hC hw hsp hnm hk (Nat.le_of_not_lt hbig) hsz.1 hsz.2 hcs hfo
        exact MBody.of_step hC hw hsp S ((sysCarve_body hC S.1 (S.sp hC hw hsp) hnb).of_eq (pure_ok h))

/-- `sysNewHeap` does not abort. -/
theorem sysNewHeap_total (hC : C.Ok) {l : Local} (hw : LocalWF C l) (hsp : LocalSp C l)
    (hnm : l.isMain = false) (nb : Nat) (tried : Bool) : ∃ r, sysNewHeap C l nb tried = .ok r := by
  rw [sysNewHeap_eq]
  have hsz := hsizeOf_props hC nb
  generalize hsizeOf C nb = hsize at hsz ⊢
  unfold sysNewHeapAt
  split
  · exact ⟨_, rfl⟩
  · rename_i hbig
    split
    · exact ⟨_, rfl⟩
    · rename_i h' k hk
      split
      rename_i fr lc hcs
      obtain ⟨lf, hlf⟩ := newHeap_total hC hw hsp hnm hk (Nat.le_of_not_lt hbig) hsz.1 hsz.2 hcs
      rw [hlf, ok_bind]
      exact ⟨_, rfl⟩

theorem heaps_cons_of_head? {l : List (Nat × Nat)} {h hs : Nat} (e : l.head? = some (h, hs)) :
    ∃ rest, l = (h, hs) :: rest := by
  cases l with
  | nil => cases e
  | cons a t => simp only [List.head?_cons, Option.some.injEq] at e; subst e; exact ⟨t, rfl⟩

/-- **`Algo.sysHeapBody`**: `sysmalloc`'s non-main part is a body. -/
theorem sysHeapBody (C : Config) : Task.algo.sysHeapBody C := by
  intro hC l l' n nb p tried hw hsp hi hnm hnb _ h
  unfold sysmallocHeap at h
  dsimp only at h
  split at h
  · rename_i h0 hs0 hhd
    obtain ⟨rest, hh⟩ := heaps_cons_of_head? hhd
    split at h
    · rename_i hcond
      split at h
      · rename_i k hk
        have S := grow_step hC hw hsp hnm hh (alignUp_page_mod hC _) hcond.2 hk
        exact MBody.of_step hC hw hsp S ((sysCarve_body hC S.1 (S.sp hC hw hsp) hnb).of_eq (pure_ok h))
      · rename_i k hk
        obtain ⟨h1, h2⟩ := mprotect_spec hk
        have S := kernel_step hw hsp h1 h2 (mprotect_maps hk)
        exact MBody.of_step hC hw hsp S (sysNewHeap_body hC S.1 (S.sp hC hw hsp) hi hnm hnb h)
    · exact sysNewHeap_body hC hw hsp hi hnm hnb h
  · cases h

/-- **`Algo.sysHeapTotal`**: `sysmalloc`'s non-main part does not abort. -/
theorem sysHeapTotal (C : Config) : Task.algo.sysHeapTotal C := by
  intro hC l n nb tried hw hsp hnm _ _
  obtain ⟨h0, hs0, rest, hh, -⟩ := (hw.heap hnm).cur
  unfold sysmallocHeap
  dsimp only
  split
  · rename_i h1 hs1 hhd
    obtain ⟨rest', hh'⟩ := heaps_cons_of_head? hhd
    split
    · split
      · exact ⟨_, rfl⟩
      · rename_i k hk
        obtain ⟨h1, h2⟩ := mprotect_spec hk
        have S := kernel_step hw hsp h1 h2 (mprotect_maps hk)
        exact sysNewHeap_total hC S.1 (S.sp hC hw hsp) hnm nb tried
    · exact sysNewHeap_total hC hw hsp hnm nb tried
  · rename_i hn
    exact absurd (by rw [hh]; rfl) (hn h0 hs0)

/-- **`Task.algo.bodyMalloc`** conditional only on `sysmalloc`'s main-arena part. -/
theorem bodyMalloc_main (C : Config) (hmain : Task.algo.sysMainBody C) : Task.algo.bodyMalloc C :=
  bodyMalloc_cons C hmain (sysHeapBody C)

/-- **`Task.algo.totalMalloc`** conditional only on `sysmalloc`'s main-arena part. -/
theorem totalMalloc_main (C : Config) (hmainT : Task.algo.sysMainTotal C) : Task.algo.totalMalloc C :=
  totalMalloc_cons C hmainT (sysHeapTotal C)

end Silmaril.Libc.Ptmalloc.Algo
