module

public import Silmaril.Proofs.Libc.Ptmalloc.Algo.Tiling
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.LeafLists
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.FreeTcache
public import Silmaril.Libc.Ptmalloc.Algo.Tasks.Defs

/-!
# ptmalloc algorithm: the arena steps of coalescing

Each step of `Silmaril.Libc.Ptmalloc.Algo.Step` that coalescing uses, on a well-formed view, is an
**arena step** (`Algo.ArenaStep`): the result is well formed, differs from the input only in
the arena, keeps the fastbins and keeps the lent-out payloads (`ArenaSt.out`). Arena steps
compose (`ArenaStep.trans`).

| step | lemma | components re-proved |
|---|---|---|
| `unlink` (a chunk in a regular bin, held `internal`) | `unlink_step` | Top + Bins or Unsorted |
| `fuse` (two held chunks) | `fuse_step` | Top |
| `unsortedPush` (a held chunk with used neighbours) | `unsortedPush_step` | Top + Unsorted |
| `mergeTop` (the held last chunk of the current segment) | `mergeTop_step` | Top |

The other components' invariants are carried over by their unchanged views
(`ArenaWF.withTilesViews`; `BinsWF.congr_sz`: the large-bin order reads only the sizes of
chunks in bins).
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc

theorem BinsWF.congr_sz {C : Config} {bs : BinsSt} {cs : List Chunk} {sz sz' : Nat → Nat}
    (h : BinsWF C bs cs sz) (hsz : ∀ c ∈ cs, sz' c.addr = sz c.addr) : BinsWF C bs cs sz' where
  exact := h.exact
  outside := h.outside
  nodup := h.nodup
  size := h.size
  sorted i hi := by
    refine (h.sorted i hi).imp_of_mem fun {a b} ha hb hab => ?_
    have hmem : ∀ x ∈ bs.lists i, sz' x = sz x := by
      intro x hx
      by_cases h2 : 2 ≤ i
      · obtain ⟨c, hc, rfl, -⟩ := (h.exact i h2 x).mp hx
        exact hsz c hc
      · rw [h.outside i (.inl (by omega))] at hx; cases hx
    rw [hmem a ha, hmem b hb]; exact hab
  binmap := h.binmap

/-! ## The kernel's byte total -/

theorem KernelSt.total_eq {k k' : KernelSt} (h1 : k'.brkStart = k.brkStart) (h2 : k'.brk = k.brk)
    (h3 : k'.maps = k.maps) : k'.total = k.total := by
  unfold KernelSt.total; rw [h1, h2, h3]

theorem KernelSt.total_cons (k : KernelSt) (m : Nat × Nat) :
    ({ k with maps := m :: k.maps } : KernelSt).total = k.total + m.2 := by
  unfold KernelSt.total; simp only [List.map_cons, List.sum_cons]; omega

theorem sum_erase_le {L : List (Nat × Nat)} {m : Nat × Nat} :
    (L.map (·.2)).sum ≤ ((L.erase m).map (·.2)).sum + m.2 := by
  induction L with
  | nil => simp
  | cons x L ih =>
    by_cases hx : x = m
    · subst hx; simp; omega
    · rw [List.erase_cons_tail (by simpa using hx)]
      simp only [List.map_cons, List.sum_cons]; omega

/-- `munmap` gives back at most the unmapped length. -/
theorem KernelSt.total_munmap (k : KernelSt) (a n : Nat) : k.total ≤ (k.munmap a n).total + n := by
  unfold KernelSt.total KernelSt.munmap
  have := sum_erase_le (L := k.maps) (m := (a, n))
  simp only at this ⊢; omega

/-- **A new tiling with the same list views** keeps `ArenaWF`. -/
theorem ArenaWF.withTilesViews {C : Config} {av : ArenaSt} (h : ArenaWF C av) (ts : TopSt)
    (ht : TopWF C ts)
    (hf : Chunk.view Use.isFast ts.heapChunks = av.fastView)
    (hs : Chunk.view Use.isSorted ts.heapChunks = av.sortedView)
    (hu : Chunk.view Use.isUnsorted ts.heapChunks = av.unsortedView) :
    ArenaWF C { av with tiles := ts } where
  tiles := ht
  fast := by show FastWF C av.fast (Chunk.view Use.isFast ts.heapChunks); rw [hf]; exact h.fast
  bins := by
    show BinsWF C av.bins (Chunk.view Use.isSorted ts.heapChunks) ts.sizeAt
    rw [hs]
    refine h.bins.congr_sz fun c hc => ?_
    have hc1 : c ∈ av.tiles.heapChunks := (List.mem_filter.mp hc).1
    have hc2 : c ∈ ts.heapChunks := by
      have : c ∈ Chunk.view Use.isSorted ts.heapChunks := by rw [hs]; exact hc
      exact (List.mem_filter.mp this).1
    rw [TopSt.sizeAt_of_mem ht.nodup hc2, TopSt.sizeAt_of_mem h.tiles.nodup hc1]
  unsorted := by
    show UnsortedWF C av.unsorted (Chunk.view Use.isUnsorted ts.heapChunks); rw [hu]; exact h.unsorted
  internal c hc _ := ht.minSize_all c hc

/-- **An arena change with the same heap end** keeps `LocalWF` (given the new arena's invariant). -/
theorem LocalWF.withAv' {C : Config} {l : Local} (h : LocalWF C l) (av : ArenaSt) (ha : ArenaWF C av)
    (hs : av.tiles.start = l.av.tiles.start)
    (hend : av.tiles.top + av.tiles.topSize = l.av.tiles.top + l.av.tiles.topSize)
    (hnc : av.tiles.noncontig = l.av.tiles.noncontig)
    (ho : av.tiles.old = [] ↔ l.av.tiles.old = []) (hap : Apart ({ l with av := av } : Local).spans)
    (hh : av.heaps = l.av.heaps := by rfl) (hr : av.reserve = l.av.reserve := by rfl)
    (hsm : av.tiles.systemMem ≤ l.av.tiles.systemMem := by first | exact Nat.le_refl _ | simp) :
    LocalWF C { l with av := av } where
  arena := ha
  shared := h.shared
  tcache := h.tcache
  main hm := by
    obtain ⟨⟨s1, s2⟩, b⟩ := h.main hm
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · simp only at s1 ⊢; rw [hs]; exact s1
    · intro hc; simp only at hc ⊢; rw [hnc] at hc; rw [hs, ho]; exact s2 hc
    · simp only [MainBrk] at b ⊢; rw [hs, hend, hnc]; exact b
  init h0 := by obtain ⟨a, b, c⟩ := h.init h0; exact ⟨by simp only; rw [hs]; exact a, b, c⟩
  apart := hap
  mmSize := h.mmSize
  heap hm := (h.heap hm).congr hh hr hs hend hsm
  sysMain hm := by
    show av.tiles.systemMem + l.shared.mm.mp.mmappedMem ≤ l.kernel.total
    have := h.sysMain hm; omega

/-- The lent-out payloads depend only on the client view of the tiling. -/
theorem ArenaSt.out_congr {C : Config} {av av' : ArenaSt}
    (h : Chunk.view (· = .client) av'.tiles.heapChunks = Chunk.view (· = .client) av.tiles.heapChunks) :
    av'.out C = av.out C := by
  unfold ArenaSt.out ArenaSt.chunks; rw [h]

/-- The view with `have_fastchunks` set: `malloc_consolidate` clears the flag first and empties
the fastbins after, so its intermediate states are well formed only up to that flag. -/
def Local.hf (l : Local) : Local := { l with av := { l.av with fast := { l.av.fast with haveFast := true } } }

theorem LocalWF.hf {C : Config} {l : Local} (h : LocalWF C l) : LocalWF C l.hf where
  arena :=
    { tiles := h.arena.tiles
      fast := { h.arena.fast with flag := fun _ => rfl }
      bins := h.arena.bins
      unsorted := h.arena.unsorted
      internal := h.arena.internal }
  shared := h.shared
  tcache := h.tcache
  main := h.main
  init := h.init
  apart := h.apart
  mmSize := h.mmSize
  heap hm := (h.heap hm).congr rfl rfl rfl rfl (Nat.le_refl _)
  sysMain := h.sysMain

theorem LocalWF.of_hf {C : Config} {l : Local} (h : LocalWF C l.hf)
    (hflag : (∃ i, l.av.fast.lists i ≠ []) → l.av.fast.haveFast = true) : LocalWF C l where
  arena :=
    { tiles := h.arena.tiles
      fast := { h.arena.fast with flag := hflag }
      bins := h.arena.bins
      unsorted := h.arena.unsorted
      internal := h.arena.internal }
  shared := h.shared
  tcache := h.tcache
  main := h.main
  init := h.init
  apart := h.apart
  mmSize := h.mmSize
  heap hm := (h.heap hm).congr rfl rfl rfl rfl (Nat.le_refl _)
  sysMain := h.sysMain

namespace Algo

variable {C : Config}

/-! ## Byte cover

A body's world-facing footprint (`Frame`) needs that the bytes the view owns after a step are
bytes it owned before (new ranges come from old ones). -/

/-- Byte `x` lies in one of the ranges `rs`. -/
def InSpans (rs : List (Nat × Nat)) (x : Nat) : Prop := ∃ s ∈ rs, s.1 ≤ x ∧ x < s.1 + s.2

/-- **Byte cover**: every byte of `l'`'s spans is a byte of `l`'s. -/
def SpanCover (l l' : Local) : Prop := ∀ x, InSpans l'.spans x → InSpans l.spans x

theorem SpanCover.refl (l : Local) : SpanCover l l := fun _ h => h

theorem SpanCover.trans {l l₁ l₂ : Local} (h₁ : SpanCover l l₁) (h₂ : SpanCover l₁ l₂) :
    SpanCover l l₂ := fun x h => h₁ x (h₂ x h)

theorem SpanCover.of_eq {l l' : Local} (h : l'.spans = l.spans) : SpanCover l l' := fun x hx => by
  rw [h] at hx; exact hx

theorem InSpans.mono {rs rs' : List (Nat × Nat)} {x : Nat} (h : InSpans rs x) (hs : ∀ s ∈ rs, s ∈ rs') :
    InSpans rs' x := by
  obtain ⟨s, hs0, h1, h2⟩ := h; exact ⟨s, hs s hs0, h1, h2⟩

/-- **Replacing ranges by ranges inside them keeps `Apart`**: `Y'` apart, every byte of `Y'` a
byte of `Y`. -/
theorem _root_.Silmaril.Libc.Ptmalloc.Apart.replace_cover {X Y Y' : List (Nat × Nat)} (h : Apart (X ++ Y)) (h' : Apart Y')
    (hc : ∀ s ∈ Y', ∀ x, s.1 ≤ x → x < s.1 + s.2 → InSpans Y x) : Apart (X ++ Y') := by
  have hX : Apart X := h.sublist (List.sublist_append_left ..)
  refine ⟨List.pairwise_append.mpr ⟨hX.1, h'.1, fun r hr s hs => ?_⟩, fun r hr => ?_⟩
  · by_cases h1 : r.1 + r.2 ≤ s.1
    · exact .inl h1
    by_cases h2 : s.1 + s.2 ≤ r.1
    · exact .inr h2
    have hpw := fun y hy => (List.pairwise_append.mp h.1).2.2 r hr y hy
    have hr0 := hX.2 r hr
    have hs0 := h'.2 s hs
    by_cases h3 : r.1 ≤ s.1
    · obtain ⟨y, hy, y1, y2⟩ := hc s hs s.1 (Nat.le_refl _) (by omega)
      have := hpw y hy; omega
    · obtain ⟨y, hy, y1, y2⟩ := hc s hs r.1 (by omega) (by omega)
      have := hpw y hy; omega
  · rcases List.mem_append.mp hr with hr | hr
    · exact hX.2 r hr
    · exact h'.2 r hr

/-- `Apart` up to a permutation on both sides, replacing a part by ranges inside it. -/
theorem _root_.Silmaril.Libc.Ptmalloc.Apart.perm_cover {L L' X Y Y' : List (Nat × Nat)} (h : Apart L) (hp : L.Perm (X ++ Y))
    (h' : Apart Y') (hc : ∀ s ∈ Y', ∀ x, s.1 ≤ x → x < s.1 + s.2 → InSpans Y x)
    (hp' : L'.Perm (X ++ Y')) : Apart L' :=
  ((h.perm hp).replace_cover h' hc).perm hp'.symm

theorem InSpans.chunk {ts : TopSt} {c : Chunk} (hc : c ∈ ts.heapChunks) {x : Nat} (h1 : c.addr ≤ x)
    (h2 : x < c.addr + c.size) : InSpans ts.spans x :=
  ⟨(c.addr, c.size), List.mem_append_left _ (List.mem_map_of_mem hc), h1, h2⟩

theorem InSpans.top {ts : TopSt} (hs : ts.start ≠ 0) {x : Nat} (h1 : ts.top ≤ x)
    (h2 : x < ts.top + ts.topSize) : InSpans ts.spans x :=
  ⟨(ts.top, ts.topSize), List.mem_append_right _ (by simp [hs]), h1, h2⟩

/-- A tiling whose chunks' bytes are old bytes and whose top is the old one. -/
theorem TopSt.cover_chunks {ts ts' : TopSt} (hs : ts'.start = ts.start) (ht : ts'.top = ts.top)
    (hz : ts'.topSize = ts.topSize)
    (h : ∀ c ∈ ts'.heapChunks, ∀ x, c.addr ≤ x → x < c.addr + c.size → InSpans ts.spans x) :
    ∀ x, InSpans ts'.spans x → InSpans ts.spans x := by
  rintro x ⟨sp, hsp, h1, h2⟩
  unfold TopSt.spans at hsp
  rcases List.mem_append.mp hsp with hsp | hsp
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hsp
    exact h c hc x h1 h2
  · rw [hs, ht, hz] at hsp
    exact ⟨sp, List.mem_append_right _ hsp, h1, h2⟩

/-- A change of the arena's tiling (the `mmap`ed chunks kept) whose bytes are old bytes. -/
theorem spanCover_tiles {l l' : Local} (hmm : l'.shared.mm.chunks = l.shared.mm.chunks)
    (h : ∀ x, InSpans l'.av.tiles.spans x → InSpans l.av.tiles.spans x)
    (hh : l'.av.heapSpans = l.av.heapSpans := by rfl) : SpanCover l l' := by
  rintro x ⟨s, hs, h1, h2⟩
  unfold Local.spans ArenaSt.spans at hs ⊢
  rcases List.mem_append.mp hs with hs | hs
  · rcases List.mem_append.mp hs with hs | hs
    · exact (h x ⟨s, hs, h1, h2⟩).mono fun _ h => List.mem_append_left _ (List.mem_append_left _ h)
    · rw [hh] at hs; exact ⟨s, List.mem_append_left _ (List.mem_append_right _ hs), h1, h2⟩
  · rw [hmm] at hs; exact ⟨s, List.mem_append_right _ hs, h1, h2⟩

theorem spanCover_relabel {l l' : Local} {a : Nat} {u : Use} (ht : l'.av.tiles = l.av.tiles.relabel a u)
    (hmm : l'.shared = l.shared) (hh : l'.av.heapSpans = l.av.heapSpans := by rfl) : SpanCover l l' :=
  spanCover_tiles (by rw [hmm]) (fun x hx => by rw [ht, TopSt.spans_relabel] at hx; exact hx) hh

/-- **An arena step**: well formed after (up to `have_fastchunks`), only the arena changed, the
fastbins, the heaps and the lent-out payloads kept, and every byte it owns after is a byte it
owned before. -/
structure ArenaStep (C : Config) (l l' : Local) : Prop where
  wf : LocalWF C l'.hf
  eq : l' = { l with av := l'.av }
  fast : l'.av.fast = l.av.fast
  out : l'.av.out C = l.av.out C
  cover : SpanCover l l'
  heaps : l'.av.heaps = l.av.heaps
  start : l'.av.tiles.start = l.av.tiles.start

theorem ArenaStep.trans {l l₁ l₂ : Local} (h₁ : ArenaStep C l l₁) (h₂ : ArenaStep C l₁ l₂) :
    ArenaStep C l l₂ where
  wf := h₂.wf
  eq := by rw [h₂.eq, h₁.eq]
  fast := h₂.fast.trans h₁.fast
  out := h₂.out.trans h₁.out
  cover := h₁.cover.trans h₂.cover
  heaps := h₂.heaps.trans h₁.heaps
  start := h₂.start.trans h₁.start

theorem ArenaStep.within {l l' : Local} (h : ArenaStep C l l') : Footprint.Within fpArena l l' := by
  rw [h.eq]; simp [Footprint.Within]

theorem tagFree_internal : Use.tagFree .internal = false := rfl

theorem view_relabel_internal {ts : TopSt} {p : Use → Bool} (hn : (ts.heapChunks.map (·.addr)).Nodup)
    {d : Chunk} (hd : d ∈ ts.heapChunks) (hp : p d.use = false) (hu : p .internal = false) :
    Chunk.view p (ts.relabel d.addr .internal).heapChunks = Chunk.view p ts.heapChunks :=
  view_relabel_of hn hd rfl hp hu

/-- **Removal of a held chunk from the unsorted bin** (`unlink_chunk` of an unsorted chunk). -/
theorem leafUnsortedRemove {l : Local} (hw : LocalWF C l) {d : Chunk} (hd : d ∈ l.av.tiles.heapChunks)
    (hdu : d.use = .bin 1) :
    LocalWF C { l with
      av := { l.av with
        tiles := l.av.tiles.relabel d.addr .internal
        unsorted := l.av.unsorted.remove d.addr } } := by
  have ht := hw.arena.tiles
  have hn := ht.nodup
  have ht' := ht.relabel (a := d.addr) (u := .internal) rfl
  have hav := hw.arena.withUnsorted (l.av.tiles.relabel d.addr .internal) (l.av.unsorted.remove d.addr) ht'
    (by rw [TopSt.heapChunks_relabel]; exact hw.arena.unsorted.erase (by simp))
    (view_relabel_internal hn hd (by rw [hdu]; rfl) rfl)
    (view_relabel_internal hn hd (by rw [hdu]; rfl) rfl) (TopSt.sizeAt_relabel ..)
    (fun c hc _ => ht'.minSize_all c hc)
  exact hw.withAv _ hav rfl rfl rfl rfl (TopSt.relabel_old_nil ..) (TopSt.spans_relabel ..)

theorem out_relabel_internal {l : Local} (hw : LocalWF C l) {d : Chunk} (hd : d ∈ l.av.tiles.heapChunks)
    (hdu : d.use ≠ .client) (av' : ArenaSt) (ht : av'.tiles = l.av.tiles.relabel d.addr .internal) :
    av'.out C = l.av.out C :=
  ArenaSt.out_congr (by rw [ht]; exact view_relabel_internal hw.arena.tiles.nodup hd (by simpa using hdu) rfl)

/-- **`unlink_chunk`** of a chunk in a regular bin, held `internal`. -/
theorem unlink_step {l : Local} (hw' : LocalWF C l.hf) {d : Chunk} (hd : d ∈ l.av.tiles.heapChunks)
    (hfree : d.use.tagFree = true) :
    ∃ l₁, unlink l d.addr .internal = .ok l₁ ∧ ArenaStep C l l₁ ∧
      l₁.av.tiles = l.av.tiles.relabel d.addr .internal := by
  have hw := hw'
  have hn : (l.av.tiles.heapChunks.map (·.addr)).Nodup := hw.arena.tiles.nodup
  have hfind : l.av.tiles.find? d.addr = some d := by
    unfold TopSt.find?; exact find?_addr hn hd
  obtain ⟨da, ds, du⟩ := d
  cases du with
  | client => simp [Use.tagFree] at hfree
  | internal => simp [Use.tagFree] at hfree
  | fast _ => simp [Use.tagFree] at hfree
  | bin i =>
    match i, hd, hfind with
    | 1, hd, hfind =>
      refine ⟨{ l with
          av := { l.av with
            tiles := l.av.tiles.relabel da .internal
            unsorted := l.av.unsorted.remove da } }, by simp only [unlink, hfind],
        ⟨leafUnsortedRemove (l := l.hf) hw hd rfl, rfl, rfl, ?_, spanCover_relabel rfl rfl, rfl, rfl⟩, rfl⟩
      exact out_relabel_internal (l := l.hf) hw hd (by simp) _ rfl
    | 0, hd, hfind =>
      have hb : l.av.bins.remove da 0 = l.av.bins := by
        have this : l.av.bins.lists 0 = [] := hw.arena.bins.outside 0 (.inl (by omega))
        cases hbs : l.av.bins with
        | mk ls bm =>
          rw [hbs] at this
          simp only [BinsSt.remove, BinsSt.mk.injEq, and_true]
          funext j; by_cases hj : j = 0
          · subst hj; simp only [ite_true]; simp only at this; rw [this]; rfl
          · simp [hj]
      refine ⟨l.binRemove da 0 .internal, by simp only [unlink, hfind],
        ⟨?_, rfl, rfl, ?_, spanCover_relabel rfl rfl, rfl, rfl⟩, rfl⟩
      · have ht : TopWF C l.av.tiles := hw.arena.tiles
        have ht' := ht.relabel (a := da) (u := .internal) rfl
        have hd' : (⟨da, ds, .bin 0⟩ : Chunk) ∈ l.av.tiles.heapChunks := hd
        have hav := hw.arena.withTilesViews _ ht' (view_relabel_internal hn hd' rfl rfl)
          (view_relabel_internal hn hd' rfl rfl) (view_relabel_internal hn hd' rfl rfl)
        have := hw.withAv _ hav rfl rfl rfl rfl (TopSt.relabel_old_nil ..) (TopSt.spans_relabel ..)
        simp only [Local.binRemove, Local.hf, hb]; exact this
      · exact out_relabel_internal (l := l.hf) hw hd (by simp) _ rfl
    | j + 2, hd, hfind =>
      have hj : 2 ≤ j + 2 := by omega
      have hmem : da ∈ l.hf.av.bins.lists (j + 2) :=
        ((hw.arena.bins.exact_all hj) da).mpr ⟨_, hd, rfl, rfl⟩
      refine ⟨l.binRemove da (j + 2) .internal, by simp only [unlink, hfind],
        ⟨(leafBinRemove (l := l.hf) hw hmem (.inr rfl)).1, rfl, rfl, ?_, spanCover_relabel rfl rfl, rfl, rfl⟩, rfl⟩
      exact out_relabel_internal (l := l.hf) hw hd (by simp) _ rfl

/-- **Fusing two held chunks** into one held chunk. -/
theorem fuse_step {l : Local} (hw : LocalWF C l.hf) {R₁ R₂ : List (Nat × List (Nat × Use))} {s : Nat}
    {pre post : List (Nat × Use)} {sz₁ sz₂ : Nat}
    (hr : l.av.tiles.runs = R₁ ++ (s, pre ++ (sz₁, .internal) :: (sz₂, .internal) :: post) :: R₂) :
    ArenaStep C l (fuse l (s + runLen pre) .internal) ∧
      (fuse l (s + runLen pre) .internal).av.tiles.runs =
        R₁ ++ (s, pre ++ (sz₁ + sz₂, .internal) :: post) :: R₂ := by
  have ht : TopWF C l.av.tiles := hw.arena.tiles
  have hn := ht.nodup
  have hr' := TopSt.runs_fuse (x := (sz₁, .internal)) (y := (sz₂, .internal)) Use.internal hr rfl hn
  have hr1 : l.av.tiles.runs = R₁ ++ (s, pre ++ [(sz₁, .internal), (sz₂, .internal)] ++ post) :: R₂ := by
    rw [hr]; simp
  have hr1' : (l.av.tiles.fuse (s + runLen pre) .internal).runs =
      R₁ ++ (s, pre ++ [(sz₁ + sz₂, .internal)] ++ post) :: R₂ := by
    rw [hr']; simp
  have hlen : runLen [(sz₁ + sz₂, Use.internal)] = runLen [(sz₁, .internal), (sz₂, .internal)] := by
    simp
  have h1 := ht.sizes _ (TopSt.mem_of_runs hr)
  have h2 := ht.sizes _ (TopSt.mem_of_runs_next hr)
  have hcoal0 := ht.runs_coal _ (by rw [hr]; exact List.mem_append_right _ (List.mem_cons_self ..))
  simp only at hcoal0
  rw [coalescedB_mid_used _ _ _ rfl] at hcoal0
  have hpost : coalescedB post = true := by
    have := hcoal0.2; rw [← List.nil_append ((sz₂, Use.internal) :: post), coalescedB_mid_used _ _ _ rfl] at this
    exact this.2
  have ht' : TopWF C (l.av.tiles.fuse (s + runLen pre) .internal) := by
    refine ht.replace hr1 hr1' (by simp) hlen ?_ ?_ ?_ ?_ rfl rfl rfl
    · intro e he
      simp only [List.mem_singleton] at he; subst he
      simp only at h1 h2 ⊢
      refine ⟨?_, by omega⟩
      rw [Nat.add_mod, h1.1, h2.1]; simp
    · show [s + runLen pre].Sublist [s + runLen pre, s + runLen pre + sz₁]
      simp
    · show coalescedB (pre ++ [(sz₁ + sz₂, Use.internal)] ++ post) = true
      rw [List.append_assoc, List.singleton_append, coalescedB_mid_used _ _ _ rfl]
      exact ⟨hcoal0.1, hpost⟩
    · intro h0 e he
      subst h0
      rw [List.append_assoc, List.singleton_append, getLast?_append_cons] at he
      rcases mem_getLast?_cons he with ⟨-, rfl⟩ | ⟨hne, he⟩
      · rfl
      · apply ht.runs_last (R₁ := R₁) (s := s) hr e
        rw [getLast?_append_cons, List.getLast?_cons_cons]
        cases post with
        | nil => exact absurd rfl hne
        | cons q qs => rw [List.getLast?_cons_cons]; exact he
  have hv : ∀ p : Use → Bool, p .internal = false →
      Chunk.view p (l.av.tiles.fuse (s + runLen pre) .internal).heapChunks = Chunk.view p l.av.tiles.heapChunks :=
    fun p hp => TopSt.view_replace hr1 hr1' hlen (by simp [hp]) (by simp [hp])
  have hav := hw.arena.withTilesViews _ ht' (hv _ rfl) (hv _ rfl) (hv _ rfl)
  have hap : Apart ({ l.hf with av := { l.hf.av with tiles := l.av.tiles.fuse (s + runLen pre) .internal } } : Local).spans := by
    have hold : Apart (l.av.tiles.spans ++ (l.av.heapSpans ++ l.shared.mm.chunks.map (fun c => (c.addr, c.size)))) :=
      (Local.spans_eq l) ▸ hw.apart
    have hH := TopSt.heapChunks_of_runs hr1
    have hH' := TopSt.heapChunks_of_runs hr1'
    rw [hlen] at hH'
    rw [Local.spans_eq]
    show Apart ((l.av.tiles.fuse (s + runLen pre) .internal).spans ++ (l.av.heapSpans ++ l.shared.mm.chunks.map (fun c => (c.addr, c.size))))
    unfold TopSt.spans at hold ⊢
    rw [List.append_assoc, hH, show layout (s + runLen pre) [(sz₁, Use.internal), (sz₂, Use.internal)] =
      [⟨s + runLen pre, sz₁, .internal⟩, ⟨s + runLen pre + sz₁, sz₂, .internal⟩] from rfl] at hold
    rw [List.append_assoc, hH', show layout (s + runLen pre) [(sz₁ + sz₂, Use.internal)] =
      [⟨s + runLen pre, sz₁ + sz₂, .internal⟩] from rfl,
      show (l.av.tiles.fuse (s + runLen pre) .internal).start = l.av.tiles.start from rfl,
      show (l.av.tiles.fuse (s + runLen pre) .internal).top = l.av.tiles.top from rfl,
      show (l.av.tiles.fuse (s + runLen pre) .internal).topSize = l.av.tiles.topSize from rfl]
    exact Apart.merge_chunks hold rfl rfl rfl
  have hcov : SpanCover l (fuse l (s + runLen pre) .internal) := by
    refine spanCover_tiles rfl (TopSt.cover_chunks rfl rfl rfl fun c hc x h1 h2 => ?_)
    have hH := TopSt.heapChunks_of_runs hr1
    have hH' := TopSt.heapChunks_of_runs hr1'
    rw [hlen] at hH'
    have hc' : c ∈ (l.av.tiles.fuse (s + runLen pre) .internal).heapChunks := hc
    rw [hH', show layout (s + runLen pre) [(sz₁ + sz₂, Use.internal)] =
      [⟨s + runLen pre, sz₁ + sz₂, .internal⟩] from rfl] at hc'
    have hold : ∀ d ∈ l.av.tiles.heapChunks, d.addr ≤ x → x < d.addr + d.size →
        InSpans l.av.tiles.spans x := fun d hd => InSpans.chunk hd
    rw [hH, show layout (s + runLen pre) [(sz₁, Use.internal), (sz₂, Use.internal)] =
      [⟨s + runLen pre, sz₁, .internal⟩, ⟨s + runLen pre + sz₁, sz₂, .internal⟩] from rfl] at hold
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc' hold
    rcases hc' with (hc' | rfl) | hc'
    · exact hold c (.inl (.inl hc')) h1 h2
    · simp only at h1 h2
      by_cases hx : x < s + runLen pre + sz₁
      · exact hold _ (.inl (.inr (.inl rfl))) h1 hx
      · exact hold _ (.inl (.inr (.inr rfl))) (by simp only; omega) (by simp only; omega)
    · exact hold c (.inr hc') h1 h2
  refine ⟨⟨hw.withAv' _ hav rfl rfl rfl
    (show (l.av.tiles.fuse (s + runLen pre) .internal).old = [] ↔ l.av.tiles.old = [] by simp [TopSt.fuse]) hap, rfl, rfl,
    ArenaSt.out_congr (hv _ (by decide)), hcov, rfl, rfl⟩, hr'⟩

/-- **Putting a held chunk at the head of the unsorted bin**, its neighbours used (and, in the
current segment, not the last chunk). -/
theorem unsortedPush_step {l : Local} (hw : LocalWF C l.hf) {R₁ R₂ : List (Nat × List (Nat × Use))}
    {s : Nat} {pre post : List (Nat × Use)} {sz : Nat}
    (hr : l.av.tiles.runs = R₁ ++ (s, pre ++ (sz, .internal) :: post) :: R₂)
    (hprev : ∀ e ∈ pre.getLast?, e.2.tagFree = false) (hnext : ∀ e ∈ post.head?, e.2.tagFree = false)
    (hlast : R₂ = [] → post ≠ []) :
    ArenaStep C l (l.unsortedPush (s + runLen pre)) := by
  have ht : TopWF C l.av.tiles := hw.arena.tiles
  have hn := ht.nodup
  have hr' := TopSt.runs_relabel (x := (sz, .internal)) (.bin 1) hr rfl hn
  have hr1 : l.av.tiles.runs = R₁ ++ (s, pre ++ [(sz, .internal)] ++ post) :: R₂ := by rw [hr]; simp
  have hr1' : (l.av.tiles.relabel (s + runLen pre) (.bin 1)).runs =
      R₁ ++ (s, pre ++ [(sz, .bin 1)] ++ post) :: R₂ := by rw [hr']; simp
  have hcoal0 := ht.runs_coal _ (by rw [hr]; exact List.mem_append_right _ (List.mem_cons_self ..))
  simp only at hcoal0
  rw [coalescedB_mid_used _ _ _ rfl] at hcoal0
  have hd := TopSt.mem_of_runs hr
  have ht' : TopWF C (l.av.tiles.relabel (s + runLen pre) (.bin 1)) := by
    refine ht.replace hr1 hr1' (by simp) (by simp) ?_ (List.Sublist.refl _) ?_ ?_ rfl rfl rfl
    · intro e he; simp only [List.mem_singleton] at he; subst he; exact ht.sizes _ hd
    · show coalescedB (pre ++ [(sz, Use.bin 1)] ++ post) = true
      rw [List.append_assoc, List.singleton_append, coalescedB_mid]
      exact ⟨hcoal0.1, hcoal0.2, fun _ => ⟨hprev, hnext⟩⟩
    · intro h0 e he
      have hne := hlast h0
      subst h0
      rw [List.append_assoc, List.singleton_append, getLast?_append_cons] at he
      rcases mem_getLast?_cons he with ⟨h, -⟩ | ⟨-, he⟩
      · exact absurd h hne
      · apply ht.runs_last (R₁ := R₁) (s := s) hr e
        rw [getLast?_append_cons]
        cases post with
        | nil => exact absurd rfl hne
        | cons q qs => rw [List.getLast?_cons_cons]; exact he
  have hcoal : (l.av.tiles.relabel (s + runLen pre) (.bin 1)).Coal :=
    ⟨ht'.coalesced, ht'.lastUsed, ht'.coalescedOld⟩
  have := leafUnsortedPush (l := l.hf) hw hd rfl (.inr rfl) hcoal
  refine ⟨this.1, rfl, rfl, ArenaSt.out_congr ?_, spanCover_relabel rfl rfl, rfl, rfl⟩
  exact view_relabel_of hn hd rfl (by simp) (by simp)

theorem TopSt.heapChunks_mergeTop {ts : TopSt} {cs : List (Nat × Use)} {x : Nat × Use}
    (hc : ts.chunks = cs ++ [x]) :
    ts.heapChunks = ts.mergeTop.heapChunks ++ [⟨ts.start + runLen cs, x.1, x.2⟩] := by
  have hm : ts.mergeTop = { ts with chunks := cs, top := ts.top - x.1, topSize := ts.topSize + x.1 } := by
    simp [TopSt.mergeTop, hc]
  rw [hm]
  simp [TopSt.heapChunks, hc, layout_append, layout]

/-- **Merging the held last chunk of the current segment into top.** -/
theorem mergeTop_step {l : Local} (hw : LocalWF C l.hf) {R₁ : List (Nat × List (Nat × Use))}
    {s : Nat} {pre : List (Nat × Use)} {sz : Nat}
    (hr : l.av.tiles.runs = R₁ ++ [(s, pre ++ [(sz, .internal)])])
    (hprev : ∀ e ∈ pre.getLast?, e.2.tagFree = false) :
    ArenaStep C l (mergeTop l) := by
  have ht : TopWF C l.av.tiles := hw.arena.tiles
  obtain ⟨-, hc⟩ := TopSt.runs_eq_append_singleton hr
  simp only [Prod.mk.injEq] at hc
  have ht' := ht.mergeTop hc.2 hprev
  have hH := TopSt.heapChunks_mergeTop hc.2
  have hv : ∀ p : Use → Bool, p .internal = false →
      Chunk.view p l.av.tiles.mergeTop.heapChunks = Chunk.view p l.av.tiles.heapChunks := by
    intro p hp; rw [hH]; simp [Chunk.view, List.filter_append, hp]
  have hm : l.av.tiles.mergeTop =
      { l.av.tiles with chunks := pre, top := l.av.tiles.top - sz, topSize := l.av.tiles.topSize + sz } := by
    simp [TopSt.mergeTop, hc.2]
  have hs : l.av.tiles.start ≠ 0 := fun h0 => by
    have := (ht.noHeap h0).1; rw [hc.2] at this; simp at this
  have htop : sz ≤ l.av.tiles.top := by
    have := ht.topAt hs; rw [hc.2] at this; rw [this]
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    omega
  have hav := hw.arena.withTilesViews _ ht' (hv _ rfl) (hv _ rfl) (hv _ rfl)
  have htop' : l.av.tiles.top = l.av.tiles.start + runLen pre + sz := by
    have := ht.topAt hs; rw [hc.2] at this; rw [this]
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    show _ = _ + runLen pre + _; simp [runLen]; omega
  have hap : Apart ({ l.hf with av := { l.hf.av with tiles := l.av.tiles.mergeTop } } : Local).spans := by
    have hold : Apart (l.av.tiles.spans ++ (l.av.heapSpans ++ l.shared.mm.chunks.map (fun c => (c.addr, c.size)))) :=
      (Local.spans_eq l) ▸ hw.apart
    rw [Local.spans_eq]
    show Apart (l.av.tiles.mergeTop.spans ++ (l.av.heapSpans ++ l.shared.mm.chunks.map (fun c => (c.addr, c.size))))
    unfold TopSt.spans at hold ⊢
    rw [hH] at hold
    have hs' : l.av.tiles.mergeTop.start ≠ 0 := by rw [hm]; exact hs
    simp only [hs, hs', ↓reduceIte] at hold ⊢
    have := Apart.merge_top hold (by simp only; rw [htop'])
    rw [show l.av.tiles.mergeTop.top = l.av.tiles.start + runLen pre by rw [hm]; simp only; omega,
      show l.av.tiles.mergeTop.topSize = sz + l.av.tiles.topSize by rw [hm]; simp only; omega]
    exact this
  refine ⟨hw.withAv' { l.hf.av with tiles := l.av.tiles.mergeTop } hav
    (show l.av.tiles.mergeTop.start = l.av.tiles.start by rw [hm])
    (show l.av.tiles.mergeTop.top + l.av.tiles.mergeTop.topSize = l.av.tiles.top + l.av.tiles.topSize by
      rw [hm]; simp only; omega)
    (show l.av.tiles.mergeTop.noncontig = l.av.tiles.noncontig by rw [hm])
    (show l.av.tiles.mergeTop.old = [] ↔ l.av.tiles.old = [] by rw [hm]) hap
    (hsm := Nat.le_of_eq (by rw [hm]; rfl)),
    rfl, rfl, ArenaSt.out_congr (hv _ (by decide)), ?_, rfl,
    show l.av.tiles.mergeTop.start = l.av.tiles.start by rw [hm]⟩
  refine spanCover_tiles rfl fun x ⟨sp, hsp, h1, h2⟩ => ?_
  have hsp' : sp ∈ l.av.tiles.mergeTop.spans := hsp
  unfold TopSt.spans at hsp'
  have hs' : l.av.tiles.mergeTop.start ≠ 0 := by rw [hm]; exact hs
  simp only [hs', ↓reduceIte, List.mem_append, List.mem_singleton] at hsp'
  rcases hsp' with hsp' | rfl
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hsp'
    exact InSpans.chunk (by rw [hH]; exact List.mem_append_left _ hc) h1 h2
  · rw [hm] at h1 h2; simp only at h1 h2
    by_cases hx : x < l.av.tiles.top
    · exact InSpans.chunk (c := ⟨l.av.tiles.start + runLen pre, sz, .internal⟩)
        (by rw [hH]; exact List.mem_append_right _ (List.mem_singleton_self _)) (by simp only; omega)
        (by simp only; omega)
    · exact InSpans.top hs (by omega) (by omega)

end Algo

end Silmaril.Libc.Ptmalloc
