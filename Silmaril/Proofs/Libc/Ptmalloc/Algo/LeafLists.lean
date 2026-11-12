module

public import Silmaril.Libc.Ptmalloc.Algo.Leaf.Thms
public import Silmaril.Libc.Ptmalloc.Top.Thms
public import Silmaril.Libc.Ptmalloc.Fastbins.Thms
public import Silmaril.Libc.Ptmalloc.Unsorted.Thms
public import Silmaril.Libc.Ptmalloc.Bins.Thms

/-!
# ptmalloc algorithm: the list leaf lemmas

`Algo.leafFastPush`, `Algo.leafFastPop`, `Algo.leafBinRemove`, `Algo.leafBinPushFront` (small
bins), `Algo.leafUnsortedPush`: each leaf keeps `LocalWF` and changes only the arena. Each proof
is the component lemma (`FastWF.push`, …) for the component the leaf changes, `TopWF.relabel`
(or `relabel_coal` when the new use is free) for the tiling, `TopSt.view_relabel` for the views
of the other components, and the composition theorem `ArenaWF.withFast`/`withBins`/
`withUnsorted`; `LocalWF.withAv` frames the thread, shared and kernel parts.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc

/-- **An arena change that keeps the tiling's geometry keeps `LocalWF`** (given the new arena's
invariant). -/
theorem LocalWF.withAv {C : Config} {l : Local} (h : LocalWF C l) (av : ArenaSt) (ha : ArenaWF C av)
    (hs : av.tiles.start = l.av.tiles.start) (ht : av.tiles.top = l.av.tiles.top)
    (htz : av.tiles.topSize = l.av.tiles.topSize) (hnc : av.tiles.noncontig = l.av.tiles.noncontig)
    (ho : av.tiles.old = [] ↔ l.av.tiles.old = []) (hsp : av.tiles.spans = l.av.tiles.spans)
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
    · simp only [MainBrk] at b ⊢; rw [hs, ht, htz, hnc]; exact b
  init h0 := by obtain ⟨a, b, c⟩ := h.init h0; exact ⟨by simp only; rw [hs]; exact a, b, c⟩
  apart := by
    have := h.apart; unfold Local.spans ArenaSt.spans ArenaSt.heapSpans at this ⊢; simp only
    rw [hsp, hh, hr]; exact this
  mmSize := h.mmSize
  heap hm := (h.heap hm).congr (by rw [hh]) (by rw [hr]) (by rw [hs]) (by rw [ht, htz]) hsm
  sysMain hm := by
    show av.tiles.systemMem + l.shared.mm.mp.mmappedMem ≤ l.kernel.total
    have := h.sysMain hm; omega

namespace Algo

theorem isUnsorted_bin_of {i : Nat} (hi : 2 ≤ i) : (Use.bin i).isUnsorted = false := by
  match i, hi with
  | n + 2, _ => rfl

variable {C : Config} {l : Local} {a i : Nat} {d : Chunk}

theorem view_relabel_of {ts : TopSt} {p : Use → Bool} {u : Use} (hn : (ts.heapChunks.map (·.addr)).Nodup)
    (hd : d ∈ ts.heapChunks) (hda : d.addr = a) (hp : p d.use = false) (hu : p u = false) :
    Chunk.view p (ts.relabel a u).heapChunks = Chunk.view p ts.heapChunks :=
  ts.view_relabel a u p (fun c hc hca => by
    have := chunk_unique hn hc hd (hca.trans hda.symm); subst this; exact hp) hu

private theorem geom (h : TopSt) (u : Use) :
    (h.relabel a u).start = h.start ∧ (h.relabel a u).top = h.top ∧
    (h.relabel a u).topSize = h.topSize ∧ (h.relabel a u).noncontig = h.noncontig ∧
    ((h.relabel a u).old = [] ↔ h.old = []) := ⟨rfl, rfl, rfl, rfl, TopSt.relabel_old_nil h a u⟩

/-- **`Algo.leafFastPush`**: `_int_free`'s fastbin push of a lent-out or held chunk. -/
theorem leafFastPush (hw : LocalWF C l) (hd : d ∈ l.av.chunks) (hda : d.addr = a)
    (hdu : d.use = .client ∨ d.use = .internal)
    (hsz : C.fidx d.size = i ∧ d.size ≤ C.maxFast ∧ i < C.nFast) :
    LocalWF C (l.fastPush a i) ∧
      Footprint.Within { thread := false, shared := false, kernel := false } l (l.fastPush a i) := by
  have ht := hw.arena.tiles
  have hn := ht.nodup
  have hp : ∀ p : Use → Bool, p .client = false → p .internal = false → p d.use = false := by
    intro p h1 h2; rcases hdu with h | h <;> rw [h] <;> assumption
  have ht' := ht.relabel (a := a) (u := .fast i) rfl
  have ha := hw.arena.withFast (l.av.tiles.relabel a (.fast i)) (l.av.fast.push a i) ht'
    (by rw [TopSt.heapChunks_relabel]
        exact hw.arena.fast.push hn hd hda (hp _ rfl rfl) hsz)
    (view_relabel_of hn hd hda (hp _ rfl rfl) rfl) (TopSt.sizeAt_relabel ..)
    (view_relabel_of hn hd hda (hp _ rfl rfl) rfl)
    (fun c hc _ => ht'.minSize_all c hc)
  obtain ⟨g1, g2, g3, g4, g5⟩ := geom (a := a) l.av.tiles (.fast i)
  exact ⟨hw.withAv _ ha g1 g2 g3 g4 g5 (TopSt.spans_relabel ..), by simp [Footprint.Within, Local.fastPush]⟩

/-- **`Algo.leafFastPop`**: `_int_malloc`'s fastbin pop, the chunk relabelled `u` (lent out, or
held). -/
theorem leafFastPop (hw : LocalWF C l) {p : Nat} {l' : Local} (h : l.fastPop i = some (p, l')) :
    LocalWF C l' ∧ Footprint.Within { thread := false, shared := false, kernel := false } l l' := by
  unfold Local.fastPop at h
  cases hp : l.av.fast.pop i with
  | none => rw [hp] at h; cases h
  | some r =>
    obtain ⟨b, fs'⟩ := r
    rw [hp] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have ht := hw.arena.tiles
    have hn := ht.nodup
    -- the popped chunk is in fastbin `i`
    have hb : b ∈ l.av.fast.lists i := by
      unfold FastSt.pop at hp; split at hp
      · cases hp
      · rename_i c rest hl; simp only [Option.some.injEq, Prod.mk.injEq] at hp
        rw [hl, ← hp.1]; exact List.mem_cons_self ..
    obtain ⟨d, hdv, hda, hdu⟩ := (hw.arena.fast.exact i b).mp hb
    have hd : d ∈ l.av.tiles.heapChunks := (List.mem_filter.mp hdv).1
    have ht' := ht.relabel (a := b) (u := .client) rfl
    have ha := hw.arena.withFast (l.av.tiles.relabel b .client) fs' ht'
      (by rw [TopSt.heapChunks_relabel]
          exact (FastWF.of_all (fun j => hw.arena.fast.exact_all j) hw.arena.fast.nodup
            (fun c hc k hk => hw.arena.fast.size c (List.mem_filter.mpr ⟨hc, by rw [hk]; rfl⟩) k hk)
            hw.arena.fast.flag).pop hn hp rfl)
      (view_relabel_of hn hd hda (by rw [hdu]; rfl) rfl) (TopSt.sizeAt_relabel ..)
      (view_relabel_of hn hd hda (by rw [hdu]; rfl) rfl)
      (fun c hc _ => ht'.minSize_all c hc)
    obtain ⟨g1, g2, g3, g4, g5⟩ := geom (a := b) l.av.tiles .client
    exact ⟨hw.withAv _ ha g1 g2 g3 g4 g5 (TopSt.spans_relabel ..), by simp [Footprint.Within]⟩

/-- **`Algo.leafBinRemove`**: `unlink_chunk` of `a` from small/large bin `i`, relabelled `u`
(lent out or held). -/
theorem leafBinRemove (hw : LocalWF C l) (ha : a ∈ l.av.bins.lists i) {u : Use}
    (hu : u = .client ∨ u = .internal) :
    LocalWF C (l.binRemove a i u) ∧
      Footprint.Within { thread := false, shared := false, kernel := false } l (l.binRemove a i u) := by
  have ht := hw.arena.tiles
  have hn := ht.nodup
  have hi : 2 ≤ i := by
    refine Nat.le_of_not_lt fun hlt => ?_
    rw [hw.arena.bins.outside i (.inl hlt)] at ha; cases ha
  obtain ⟨d, hd, hda, hdu⟩ := ((hw.arena.bins.exact_all hi) a).mp ha
  have huf : u.tagFree = false := by rcases hu with rfl | rfl <;> rfl
  have hus : u.isSorted = false := by rcases hu with rfl | rfl <;> rfl
  have ht' := ht.relabel (a := a) (u := u) huf
  have hfast : Chunk.view Use.isFast (l.av.tiles.relabel a u).heapChunks = l.av.fastView :=
    view_relabel_of hn hd hda (by rw [hdu]; rfl) (by rcases hu with rfl | rfl <;> rfl)
  have huns : Chunk.view Use.isUnsorted (l.av.tiles.relabel a u).heapChunks = l.av.unsortedView :=
    view_relabel_of hn hd hda (by rw [hdu]; exact isUnsorted_bin_of hi)
      (by rcases hu with rfl | rfl <;> rfl)
  have hav := hw.arena.withBins (l.av.tiles.relabel a u) (l.av.bins.remove a i) ht'
    (by rw [TopSt.heapChunks_relabel, TopSt.sizeAt_relabel]
        exact hw.arena.bins.remove hn ha hus)
    hfast huns (fun c hc _ => ht'.minSize_all c hc)
  obtain ⟨g1, g2, g3, g4, g5⟩ := geom (a := a) l.av.tiles u
  exact ⟨hw.withAv _ hav g1 g2 g3 g4 g5 (TopSt.spans_relabel ..), by simp [Footprint.Within, Local.binRemove]⟩

/-- **`Algo.leafBinPushFront`** (small bins): insert a lent-out or held chunk at the head of its
small bin, binmap marked; the tiling must stay coalesced (its neighbours are not free). -/
theorem leafBinPushFront (hw : LocalWF C l) (hd : d ∈ l.av.chunks) (hda : d.addr = a)
    (hdu : d.use = .client ∨ d.use = .internal)
    (hi : 2 ≤ i ∧ i ≤ C.lastBin ∧ C.binIndex d.size = i) (hsmall : i < C.nSmallBins)
    (hcoal : (l.av.tiles.relabel a (.bin i)).Coal) :
    LocalWF C (l.binPushFront a i) ∧
      Footprint.Within { thread := false, shared := false, kernel := false } l (l.binPushFront a i) := by
  have ht := hw.arena.tiles
  have hn := ht.nodup
  have hp : ∀ p : Use → Bool, p .client = false → p .internal = false → p d.use = false := by
    intro p h1 h2; rcases hdu with h | h <;> rw [h] <;> assumption
  have ht' := ht.relabel_coal hcoal
  have hav := hw.arena.withBins (l.av.tiles.relabel a (.bin i)) ((l.av.bins.pushFront a i).mark i) ht'
    (by rw [TopSt.heapChunks_relabel, TopSt.sizeAt_relabel]
        exact hw.arena.bins.pushSmall hn hd hda (hp _ rfl rfl) hi hsmall)
    (view_relabel_of hn hd hda (hp _ rfl rfl) rfl)
    (view_relabel_of hn hd hda (hp _ rfl rfl) (isUnsorted_bin_of hi.1))
    (fun c hc _ => ht'.minSize_all c hc)
  obtain ⟨g1, g2, g3, g4, g5⟩ := geom (a := a) l.av.tiles (.bin i)
  exact ⟨hw.withAv _ hav g1 g2 g3 g4 g5 (TopSt.spans_relabel ..), by simp [Footprint.Within, Local.binPushFront]⟩

/-- **`Algo.leafUnsortedPush`**: insert a lent-out or held chunk at the unsorted head; the
tiling must stay coalesced. -/
theorem leafUnsortedPush (hw : LocalWF C l) (hd : d ∈ l.av.chunks) (hda : d.addr = a)
    (hdu : d.use = .client ∨ d.use = .internal) (hcoal : (l.av.tiles.relabel a (.bin 1)).Coal) :
    LocalWF C (l.unsortedPush a) ∧
      Footprint.Within { thread := false, shared := false, kernel := false } l (l.unsortedPush a) := by
  have ht := hw.arena.tiles
  have hn := ht.nodup
  have hp : ∀ p : Use → Bool, p .client = false → p .internal = false → p d.use = false := by
    intro p h1 h2; rcases hdu with h | h <;> rw [h] <;> assumption
  have ht' := ht.relabel_coal hcoal
  have hav := hw.arena.withUnsorted (l.av.tiles.relabel a (.bin 1)) (l.av.unsorted.pushFront a) ht'
    (by rw [TopSt.heapChunks_relabel]
        exact hw.arena.unsorted.push hn ht.minSize_all hd hda
          (by rcases hdu with h | h <;> rw [h] <;> simp))
    (view_relabel_of hn hd hda (hp _ rfl rfl) rfl)
    (view_relabel_of hn hd hda (hp _ rfl rfl) rfl) (TopSt.sizeAt_relabel ..)
    (fun c hc _ => ht'.minSize_all c hc)
  obtain ⟨g1, g2, g3, g4, g5⟩ := geom (a := a) l.av.tiles (.bin 1)
  exact ⟨hw.withAv _ hav g1 g2 g3 g4 g5 (TopSt.spans_relabel ..), by simp [Footprint.Within, Local.unsortedPush]⟩

end Algo

end Silmaril.Libc.Ptmalloc
