module

public import Silmaril.Proofs.Libc.Ptmalloc.Algo.WorldOps

/-!
# ptmalloc algorithm: `_int_free` for the world (`Task.algo.bodyFree`, `totalFree`)

`Algo.wfIntFree` gives `LocalWF` and the live set; here the rest of the world's view of the body:

* **`Frame`** (`frame_of`): every path keeps the arena address, the shared part and
  `thread_arena`, and is a **`Shrink`**: the bytes the view owns after are bytes it owned before
  (`ArenaStep.cover`, `ConsStep.cover`), the kernel takes back only bytes the view owned
  (`systrim_shrink`: the break moves down inside the top chunk, which `systrim` checks ends at
  the break; `heapTrim_shrink`: `mprotect` changes no region), the break of a non-main arena is
  untouched and a heap is never lost. The lent-out chunks other than the freed one stay
  (`clients_of_out`, from the lent-out payloads); the only new tcache entry is the freed chunk.
* **No abort** (`coalesce_ok`, `consolidate_ok`, `systrim_ok`, `heapTrim_ok`, `freeMerge_ok`):
  `coalesce` always finds its chunk and its free neighbours in their bins, `heap_trim` finds the
  arena's heap (`LocalSp.heaps`), and the double-free checks fail on a lent-out, not parked chunk.

`Algo.bodyFree : ∀ C, Task.algo.bodyFree C`, `Algo.totalFree : ∀ C, Task.algo.totalFree C`.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

variable {C : Config}

/-! ## The bytes of a view and the kernel -/

/-- **A body step that only gives bytes back**: the view's bytes after are bytes it had; the kernel
keeps every byte it had except bytes the view owned and owns no more; the break start, the break
of a non-main arena and the arena's heaps are kept. -/
structure Shrink (l l' : Local) : Prop where
  isMain : l'.isMain = l.isMain
  cover : SpanCover l l'
  keep : ∀ x, l.kernel.Has x → (¬ InSpans l.spans x ∨ InSpans l'.spans x) → l'.kernel.Has x
  brkStart : l'.kernel.brkStart = l.kernel.brkStart
  brk : l.isMain = false → l'.kernel.brk = l.kernel.brk
  heaps : l.av.heaps ≠ [] → l'.av.heaps ≠ []
  maps : l'.kernel.maps = l.kernel.maps

theorem Shrink.refl (l : Local) : Shrink l l :=
  ⟨rfl, SpanCover.refl l, fun _ h _ => h, rfl, fun _ => rfl, id, rfl⟩

theorem Shrink.trans {l l₁ l₂ : Local} (h₁ : Shrink l l₁) (h₂ : Shrink l₁ l₂) : Shrink l l₂ where
  isMain := h₂.isMain.trans h₁.isMain
  cover := h₁.cover.trans h₂.cover
  keep x hx hc := by
    rcases hc with hc | hc
    · exact h₂.keep x (h₁.keep x hx (.inl hc)) (.inl fun h => hc (h₁.cover x h))
    · exact h₂.keep x (h₁.keep x hx (.inr (h₂.cover x hc))) (.inr hc)
  brkStart := h₂.brkStart.trans h₁.brkStart
  brk hm := (h₂.brk (by rw [h₁.isMain]; exact hm)).trans (h₁.brk hm)
  heaps h := h₂.heaps (h₁.heaps h)
  maps := h₂.maps.trans h₁.maps

/-- A change of the arena alone. -/
theorem Shrink.of_arena {l l' : Local} (hk : l'.kernel = l.kernel) (hm : l'.isMain = l.isMain)
    (hc : SpanCover l l') (hh : l'.av.heaps = l.av.heaps) : Shrink l l' :=
  ⟨hm, hc, fun x hx _ => by rw [hk]; exact hx, by rw [hk], fun _ => by rw [hk],
    fun h => by rw [hh]; exact h, by rw [hk]⟩

/-- A change of the kernel's answer counter alone. -/
theorem Shrink.of_kernel {l l' : Local} (hav : l'.av = l.av) (hsh : l'.shared = l.shared)
    (hm : l'.isMain = l.isMain) (h1 : l'.kernel.brkStart = l.kernel.brkStart)
    (h2 : l'.kernel.brk = l.kernel.brk) (h3 : l'.kernel.maps = l.kernel.maps) : Shrink l l' :=
  ⟨hm, SpanCover.of_eq (by unfold Local.spans ArenaSt.spans; rw [hav, hsh]),
    fun x hx _ => (kernel_has_congr h1 h2 h3).mpr hx, h1, fun _ => h2, fun h => by rw [hav]; exact h, h3⟩

theorem ArenaStep.shrink {l l' : Local} (h : ArenaStep C l l') : Shrink l l' := by
  have he := h.eq
  exact Shrink.of_arena (by rw [he]) (by rw [he]) h.cover h.heaps

theorem ConsStep.shrink {l l' : Local} (h : ConsStep C l l') : Shrink l l' := by
  have he := h.eq
  exact Shrink.of_arena (by rw [he]) (by rw [he]) h.cover h.heaps

/-- `malloc_consolidate` is a `ConsStep`. -/
theorem consolidate_step {l l' : Local} (hw : LocalWF C l) (h : consolidate C l = .ok l') :
    ConsStep C l l' := by
  unfold consolidate at h
  have hw0 : LocalWF C ({ l with av := { l.av with fast := { l.av.fast with haveFast := false } } } : Local).hf :=
    hw.hf
  obtain ⟨hst, -, -⟩ := consolidate_fold _ hw0 h
  exact ⟨hst.wf, by rw [hst.eq], hst.out, hst.cover, hst.heaps, hst.start, fun _ => hst.fastOff rfl⟩

theorem InSpans.local_tiles {l : Local} {x : Nat} (h : InSpans l.av.tiles.spans x) : InSpans l.spans x :=
  h.mono fun _ h => List.mem_append_left _ (List.mem_append_left _ h)

theorem mem_local_spans {l : Local} {sp : Nat × Nat} (h : sp ∈ l.spans) :
    (∃ c ∈ l.av.tiles.heapChunks, sp = (c.addr, c.size)) ∨
      (l.av.tiles.start ≠ 0 ∧ sp = (l.av.tiles.top, l.av.tiles.topSize)) ∨
      (∃ c ∈ l.shared.mm.chunks, sp = (c.addr, c.size)) ∨ sp ∈ l.av.heapSpans := by
  rw [Local.spans_eq] at h
  unfold TopSt.spans at h
  rcases List.mem_append.mp h with h | h
  · rcases List.mem_append.mp h with h | h
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h; exact .inl ⟨c, hc, rfl⟩
    · by_cases hs : l.av.tiles.start = 0
      · simp [hs] at h
      · simp only [hs, ↓reduceIte, List.mem_singleton] at h; exact .inr (.inl ⟨hs, h⟩)
  · rcases List.mem_append.mp h with h | h
    · exact .inr (.inr (.inr h))
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp h; exact .inr (.inr (.inl ⟨c, hc, rfl⟩))

/-- **A byte of the top chunk is in no other span** (`LocalWF.apart`). -/
theorem top_excl {l : Local} (hap : Apart l.spans) (hs : l.av.tiles.start ≠ 0) {x : Nat}
    (h1 : l.av.tiles.top ≤ x) (h2 : x < l.av.tiles.top + l.av.tiles.topSize) :
    (∀ c ∈ l.av.tiles.heapChunks, ¬ (c.addr ≤ x ∧ x < c.addr + c.size)) ∧
      (∀ c ∈ l.shared.mm.chunks, ¬ (c.addr ≤ x ∧ x < c.addr + c.size)) ∧
      (∀ sp ∈ l.av.heapSpans, ¬ (sp.1 ≤ x ∧ x < sp.1 + sp.2)) := by
  have hp := hap.1
  rw [Local.spans_eq] at hp
  unfold TopSt.spans at hp
  simp only [hs, ↓reduceIte] at hp
  rw [List.pairwise_append, List.pairwise_append] at hp
  obtain ⟨⟨-, -, hHT⟩, -, hAM⟩ := hp
  refine ⟨fun c hc ⟨a1, a2⟩ => ?_, fun c hc ⟨a1, a2⟩ => ?_, fun sp hsp ⟨a1, a2⟩ => ?_⟩
  · have := hHT _ (List.mem_map_of_mem (f := fun c : Chunk => (c.addr, c.size)) hc) _
      (List.mem_singleton_self _)
    simp only at this; omega
  · have := hAM _ (List.mem_append_right _ (List.mem_singleton_self _)) _
      (List.mem_append_right _ (List.mem_map_of_mem (f := fun c : Chunk => (c.addr, c.size)) hc))
    simp only at this; omega
  · have := hAM _ (List.mem_append_right _ (List.mem_singleton_self _)) _
      (List.mem_append_left _ hsp)
    simp only at this; omega

/-- Shrinking the top chunk gives no byte. -/
theorem TopSt.cover_shrinkTop (ts : TopSt) (e m : Nat) :
    ∀ x, InSpans ({ ts with topSize := ts.topSize - e, systemMem := m } : TopSt).spans x →
      InSpans ts.spans x := by
  rintro x ⟨sp, hsp, h1, h2⟩
  unfold TopSt.spans at hsp
  rcases List.mem_append.mp hsp with hsp | hsp
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hsp
    exact InSpans.chunk (ts := ts) hc h1 h2
  · by_cases hs : ts.start = 0
    · simp [hs] at hsp
    · simp only [hs, ↓reduceIte, List.mem_singleton] at hsp
      subst hsp
      simp only at h1 h2
      exact InSpans.top hs h1 (by omega)

theorem mprotect_maps {k k' : KernelSt} {b : Bool} (h : k.mprotect = (b, k')) : k'.maps = k.maps := by
  unfold KernelSt.mprotect KernelSt.ask at h
  cases ha : k.oracle.answer k.asked with
  | refuse => rw [ha] at h; simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; rfl
  | ok v => rw [ha] at h; simp only [Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; rfl

/-- **`systrim`'s kernel fact**: the break moves down by `extra` only when it is the top chunk's
end and `extra` is at most the top's size, so the bytes given back are top bytes. -/
theorem systrim_shrink (hC : C.Ok) {l l' : Local} (hap : Apart l.spans) (hs : l.av.tiles.start ≠ 0)
    (hm : l.isMain = true) {pad : Nat} (h : systrim C l pad = .ok l') : Shrink l l' := by
  unfold systrim at h
  dsimp only at h
  split at h
  · cases h; exact Shrink.refl l
  split at h
  · cases h; exact Shrink.refl l
  obtain ⟨-, hle⟩ := alignDown_page hC (l.av.tiles.topSize - C.minSize - 1 - pad)
  generalize alignDown (l.av.tiles.topSize - C.minSize - 1 - pad) C.page = extra at h hle
  split at h
  · cases h; exact Shrink.refl l
  split at h
  · cases h; exact Shrink.refl l
  rename_i h4
  have h4' : l.kernel.brk = l.av.tiles.top + l.av.tiles.topSize := by simpa using h4
  split at h
  · rename_i k hk
    cases h
    obtain ⟨hks, hkn, -⟩ := shrink_spec hk
    exact Shrink.of_kernel rfl rfl rfl hks (hkn rfl) (shrink_maps hk)
  · rename_i k hk
    cases h
    obtain ⟨hks, -, hky⟩ := shrink_spec hk
    obtain ⟨-, hk2⟩ := hky rfl
    have hkm := shrink_maps hk
    refine ⟨rfl, spanCover_tiles rfl (TopSt.cover_shrinkTop _ _ _), ?_, hks,
      fun h0 => absurd (hm.symm.trans h0) (by simp), fun h => h, hkm⟩
    intro x hx hc
    show k.Has x
    unfold KernelSt.Has at hx ⊢
    rw [hks, hk2, hkm]
    rcases hx with ⟨a1, a2⟩ | hx
    · by_cases hlt : x < l.kernel.brk - extra
      · exact .inl ⟨a1, hlt⟩
      · exfalso
        have hx1 : l.av.tiles.top ≤ x := by omega
        have hx2 : x < l.av.tiles.top + l.av.tiles.topSize := by omega
        rcases hc with hc | hc
        · exact hc (InSpans.local_tiles (InSpans.top hs hx1 hx2))
        · obtain ⟨sp, hsp, b1, b2⟩ := hc
          obtain ⟨hch, hmm, hhp⟩ := top_excl hap hs hx1 hx2
          rcases mem_local_spans hsp with ⟨c, hc, rfl⟩ | ⟨-, rfl⟩ | ⟨c, hc, rfl⟩ | hsp
          · exact hch c hc ⟨b1, b2⟩
          · simp only at b1 b2; omega
          · exact hmm c hc ⟨b1, b2⟩
          · exact hhp sp hsp ⟨b1, b2⟩
    · exact .inr hx

/-- **`heap_trim`'s kernel fact**: `mprotect` changes no region of the process. -/
theorem heapTrim_shrink {l l' : Local} (hH : HeapWF C l.av) (hT : TopWF C l.av.tiles) {pad : Nat}
    (h : heapTrim C l pad = .ok l') : Shrink l l' := by
  unfold heapTrim at h
  dsimp only at h
  split at h
  · cases h; exact Shrink.refl l
  split at h
  · cases h; exact Shrink.refl l
  split at h
  · cases h; exact Shrink.refl l
  have hle : alignDown (l.av.tiles.topSize - C.minSize - 1 - pad) C.page ≤
      l.av.tiles.topSize - C.minSize - 1 - pad := Nat.div_mul_le_self _ _
  generalize alignDown (l.av.tiles.topSize - C.minSize - 1 - pad) C.page = extra at h hle
  split at h
  · cases h; exact Shrink.refl l
  split at h
  · cases h
  rename_i hb hs rest hh
  split at h
  · rename_i k hk
    cases h
    obtain ⟨a, b⟩ := mprotect_spec hk
    exact Shrink.of_kernel rfl rfl rfl a b (mprotect_maps hk)
  · rename_i k hk
    cases h
    obtain ⟨a, b⟩ := mprotect_spec hk
    refine ⟨rfl, ?_, fun x hx _ => (kernel_has_congr a b (mprotect_maps hk)).mpr hx, a, fun _ => b,
      fun _ => by simp, mprotect_maps hk⟩
    obtain ⟨hlt, hend, -⟩ := hH.cur_of hh
    have htop : l.av.tiles.start ≤ l.av.tiles.top := by rw [hT.topAt (by omega)]; omega
    rintro x ⟨sp, hsp, h1, h2⟩
    rw [Local.spans_eq] at hsp
    rcases List.mem_append.mp hsp with hsp | hsp
    · exact InSpans.local_tiles (TopSt.cover_shrinkTop _ _ _ x ⟨sp, hsp, h1, h2⟩)
    rcases List.mem_append.mp hsp with hsp | hsp
    · unfold ArenaSt.heapSpans at hsp
      rcases List.mem_append.mp hsp with hsp | hsp
      · refine ⟨sp, ?_, h1, h2⟩
        rw [Local.spans_eq]
        refine List.mem_append_right _ (List.mem_append_left _ ?_)
        unfold ArenaSt.heapSpans
        refine List.mem_append_left _ ?_
        simp only [List.map_cons, List.mem_cons] at hsp
        rw [hh]; simp only [List.map_cons, List.mem_cons]; exact hsp
      · simp only at hsp
        split at hsp
        · simp at hsp
        · simp only [List.mem_singleton] at hsp
          subst hsp
          simp only at h1 h2
          by_cases hx : x < hb + hs
          · have hst : l.av.tiles.start ≠ 0 := by omega
            exact InSpans.local_tiles (InSpans.top hst (by omega) (by omega))
          · have hr : l.av.reserve ≠ 0 := by omega
            refine ⟨(hb + hs, l.av.reserve), ?_, by simp only; omega, by simp only; omega⟩
            rw [Local.spans_eq]
            refine List.mem_append_right _ (List.mem_append_left _ ?_)
            unfold ArenaSt.heapSpans
            rw [hh]
            simp [hr]
    · refine ⟨sp, ?_, h1, h2⟩
      rw [Local.spans_eq]
      exact List.mem_append_right _ (List.mem_append_right _ hsp)

/-- `_int_free_maybe_consolidate` only gives bytes back. -/
theorem maybeConsolidate_shrink (hC : C.Ok) {l l' : Local} (hw : LocalWF C l)
    (hs : l.av.tiles.start ≠ 0) {size : Nat} (h : maybeConsolidate C l size = .ok l') : Shrink l l' := by
  have tail : ∀ l₂ : Local, LocalWF C l₂.hf → l₂.av.tiles.start ≠ 0 → Shrink l l₂ →
      (if l₂.isMain = true then
        (if l₂.shared.mm.mp.trimThreshold ≤ l₂.av.tiles.topSize then systrim C l₂ C.topPad else pure l₂)
       else heapTrim C l₂ C.topPad) = .ok l' → Shrink l l' := by
    intro l₂ hw₂ hs2 hk h
    split at h
    · rename_i hm
      split at h
      · exact hk.trans (systrim_shrink hC hw₂.apart hs2 hm h)
      · cases h; exact hk
    · rename_i hm
      exact hk.trans (heapTrim_shrink
        ((hw₂.heap (Bool.eq_false_iff.mpr hm)).congr rfl rfl rfl rfl (Nat.le_refl _)) hw₂.arena.tiles h)
  unfold maybeConsolidate at h
  dsimp only at h
  split at h
  · cases h; exact Shrink.refl l
  split at h
  · cases hc : consolidate C l with
    | error e => rw [hc] at h; cases h
    | ok l₂ =>
      rw [hc, ok_bind] at h
      have hst := consolidate_step hw hc
      exact tail l₂ hst.wf (by rw [hst.start]; exact hs) hst.shrink h
  · exact tail l hw.hf hs (Shrink.refl l) h

theorem start_ne_of_chunk {ts : TopSt} (ht : TopWF C ts) {d : Chunk} (hd : d ∈ ts.heapChunks) :
    ts.start ≠ 0 := fun h0 => by
  obtain ⟨h1, h2⟩ := ht.noHeap h0
  simp [TopSt.heapChunks, h1, h2] at hd

/-- **The merge path only gives bytes back.** -/
theorem freeMerge_shrink (hC : C.Ok) {l l' : Local} (hw : LocalWF C l) {d : Chunk}
    (hd : d ∈ l.av.tiles.heapChunks) (hdu : d.use = .client) (h : freeMerge C l d.addr = .ok l') :
    Shrink l l' := by
  obtain ⟨hw1, -⟩ := relabelInternal_step hw hd hdu
  obtain ⟨R₁, s, pre, post, R₂, hr, ha⟩ := runs_of_chunk hw.arena.tiles hd
  rw [hdu] at hr
  have hr1 := TopSt.runs_relabel (x := (d.size, .client)) .internal hr ha hw.arena.tiles.nodup
  unfold freeMerge at h
  cases hc : coalesce (l.relabel d.addr .internal) d.addr with
  | error e => rw [hc] at h; cases h
  | ok v =>
    obtain ⟨size, l₂⟩ := v
    rw [hc, ok_bind] at h
    simp only at h
    have hst := coalesce_spec' (l := l.relabel d.addr .internal) hw1.hf hr1 ha hc
    have hw2 : LocalWF C l₂ := hst.wf.of_hf fun hne => by
      rw [hst.fast] at hne ⊢; exact hw1.arena.fast.flag hne
    have hs0 : Shrink l (l.relabel d.addr .internal) :=
      Shrink.of_arena rfl rfl (spanCover_relabel rfl rfl) rfl
    have hstart : l₂.av.tiles.start ≠ 0 := by
      rw [hst.start]; exact start_ne_of_chunk (ts := l.av.tiles) hw.arena.tiles hd
    exact hs0.trans (hst.shrink.trans (maybeConsolidate_shrink hC hw2 hstart h))

/-! ## The frame -/

/-- A lent-out chunk other than the freed one is still a chunk (the lent-out payloads lose only
the freed one). -/
theorem clients_of_out (hC : C.Ok) {l l' : Local} (hw : LocalWF C l) (hw' : LocalWF C l')
    {x : Nat × Nat} (hout : (l'.av.out C).Perm ((l.av.out C).erase x)) :
    ∀ c ∈ l.av.chunks, c.use = .client → (c.addr + C.hdr, usable C c false) ∉ [x] →
      c ∈ l'.av.chunks := by
  intro c hc hcu hnx
  have hy : (c.addr + C.hdr, c.size - C.sizeSz) ∈ l.av.out C := mem_out.mpr ⟨c, hc, hcu, rfl⟩
  have hne : (c.addr + C.hdr, c.size - C.sizeSz) ≠ x := fun h => hnx (by simp [usable, h])
  have hy' := hout.symm.subset ((List.mem_erase_of_ne hne).mpr hy)
  obtain ⟨d, hd, hdu, hde⟩ := mem_out.mp hy'
  simp only [Prod.mk.injEq] at hde
  have h1 := (hw.arena.tiles.sizes c hc).2
  have h2 := (hw'.arena.tiles.sizes d hd).2
  have hm := hC.minSize; have hz := hC.sizeSz
  have hcd : c = d := by
    obtain ⟨ca, cs, cu⟩ := c
    obtain ⟨da, ds, du⟩ := d
    simp only at hde hcu hdu h1 h2
    simp only [Chunk.mk.injEq]
    exact ⟨by omega, by omega, by rw [hcu, hdu]⟩
  rw [hcd]; exact hd

/-- **The `Frame` of a body that only gives bytes back.** -/
theorem frame_of {l l' : Local} {freed : List (Nat × Nat)} (hsp : LocalSp C l) (hap' : Apart l'.spans)
    (ha : l'.avAddr = l.avAddr) (hsh : l'.shared = l.shared)
    (harena : l'.thread.arena = l.thread.arena) (hs : Shrink l l')
    (hcl : ∀ c ∈ l.av.chunks, c.use = .client → (c.addr + C.hdr, usable C c false) ∉ freed →
      c ∈ l'.av.chunks)
    (hfr : ∀ tc' i e, l'.thread.tcache = some tc' → e ∈ tc'.bins i →
      (∃ tc j, l.thread.tcache = some tc ∧ e ∈ tc.bins j) ∨
      ((∃ c ∈ l'.av.chunks, c.addr = e.1 ∧ c.size = e.2 ∧ c.use = .client) ∧
        ((e.1 + C.hdr, e.2 - C.sizeSz) ∈ freed ∨ ∀ c ∈ l.av.chunks, c.addr = e.1 → c.use ≠ .client))) :
    Frame C l l' freed where
  avAddr := ha
  isMain := hs.isMain
  spatial r _ hc haw := by
    refine ⟨fun x h1 h2 => hs.keep x (hc x h1 h2) (.inl fun ⟨s, hs', s1, s2⟩ => ?_), fun s hs' => ?_⟩
    · have := haw s hs'; omega
    · refine Classical.byContradiction fun hne => ?_
      have hne' : s.1 < r.1 + r.2 ∧ r.1 < s.1 + s.2 := by omega
      have hs0 := hap'.2 s hs'
      rcases Nat.le_total r.1 s.1 with hle | hle
      · obtain ⟨s0, h0, a1, a2⟩ := hs.cover s.1 ⟨s, hs', Nat.le_refl _, by omega⟩
        have := haw s0 h0
        omega
      · obtain ⟨s0, h0, a1, a2⟩ := hs.cover r.1 ⟨s, hs', hle, by omega⟩
        have := haw s0 h0
        omega
  covered s hs' x h1 h2 := by
    have hx : InSpans l'.spans x := ⟨s, hs', h1, h2⟩
    obtain ⟨s0, h0, a1, a2⟩ := hs.cover x hx
    exact hs.keep x (hsp.covered s0 h0 x a1 a2) (.inr hx)
  brkStart := hs.brkStart
  nonMain h := ⟨hs.brk h, by rw [hsh]⟩
  acct h := by rw [hsh]; have := KernelSt.total_eq hs.brkStart (hs.brk h) hs.maps; omega
  init := by rw [hsh]
  arenas := by rw [hsh]; exact ⟨rfl, rfl, rfl⟩
  arena := harena
  heaps := hs.heaps
  clients := hcl
  fresh := hfr

/-! ## No abort -/

theorem coalesceTail_ok {l : Local} (hw : LocalWF C l.hf) {R₁ R₂ : List (Nat × List (Nat × Use))}
    {s : Nat} {pre post : List (Nat × Use)} {sz : Nat}
    (hr : l.av.tiles.runs = R₁ ++ (s, pre ++ (sz, .internal) :: post) :: R₂) :
    ∃ r, coalesceTail l (s + runLen pre) = .ok r := by
  have ht : TopWF C l.av.tiles := hw.arena.tiles
  have hloc := TopSt.locate_of_runs hr rfl ht.nodup
  unfold coalesceTail
  rw [hloc]
  simp only
  cases post with
  | nil =>
    by_cases hR : R₂ = []
    · subst hR
      simp only [List.head?_nil, Option.map_none, Option.getD_none, ite_true]
      exact ⟨_, rfl⟩
    · simp only [List.head?_nil, Option.map_none, Option.getD_none, hR, ite_false]
      exact ⟨_, rfl⟩
  | cons n post' =>
    obtain ⟨nsz, nu⟩ := n
    simp only [List.head?_cons, Option.map_some, Option.getD_some]
    by_cases hf : nu.tagFree = true
    · simp only [hf, ite_true]
      obtain ⟨l₃, hu, -, -⟩ := unlink_step hw (TopSt.mem_of_runs_next hr) hf
      simp only at hu
      rw [hu, ok_bind]
      exact ⟨_, rfl⟩
    · simp only [hf, Bool.false_eq_true, ite_false]
      exact ⟨_, rfl⟩

/-- **`coalesce` of a held chunk does not abort.** -/
theorem coalesce_ok {l : Local} (hw : LocalWF C l.hf) {R₁ R₂ : List (Nat × List (Nat × Use))}
    {s a : Nat} {pre post : List (Nat × Use)} {sz : Nat}
    (hr : l.av.tiles.runs = R₁ ++ (s, pre ++ (sz, .internal) :: post) :: R₂) (ha : s + runLen pre = a) :
    ∃ r, coalesce l a = .ok r := by
  subst ha
  have ht : TopWF C l.av.tiles := hw.arena.tiles
  have hloc := TopSt.locate_of_runs hr rfl ht.nodup
  rw [coalesce_of_locate hloc]
  simp only
  rcases List.eq_nil_or_concat pre with hpre | ⟨pre₀, pe, hpre⟩
  · subst hpre
    simp only [layout_nil, List.getLast?_nil]
    exact coalesceTail_ok hw hr
  · rw [List.concat_eq_append] at hpre
    subst hpre
    obtain ⟨psz, pu⟩ := pe
    have hr' : l.av.tiles.runs = R₁ ++ (s, pre₀ ++ (psz, pu) :: (sz, .internal) :: post) :: R₂ := by
      rw [hr]; simp
    have hlast : (layout s (pre₀ ++ [(psz, pu)])).getLast? = some ⟨s + runLen pre₀, psz, pu⟩ := by
      rw [layout_append]; simp [layout]
    rw [hlast]
    have hcoal := ht.runs_coal _ (by rw [hr']; exact List.mem_append_right _ (List.mem_cons_self ..))
    simp only at hcoal
    by_cases hpf : pu.tagFree = true
    · obtain ⟨l₁, hu, hst₁, ht₁⟩ := unlink_step hw (TopSt.mem_of_runs_prev hr') hpf
      simp only at hu
      simp only [hpf, ite_true, hu, ok_bind]
      have hr₁ : l₁.av.tiles.runs = R₁ ++ (s, pre₀ ++ (psz, .internal) :: (sz, .internal) :: post) :: R₂ := by
        rw [ht₁, TopSt.runs_relabel (x := (psz, pu)) .internal hr' rfl ht.nodup]
      obtain ⟨hst₂, hr₂⟩ := fuse_step hst₁.wf hr₁
      exact coalesceTail_ok hst₂.wf hr₂
    · simp only [hpf, Bool.false_eq_true, ite_false]
      exact coalesceTail_ok hw hr

theorem consolidateBin_ok (i : Nat) : ∀ (fuel : Nat) {l : Local}, LocalWF C l.hf →
    ∃ l', consolidateBin i fuel l = .ok l'
  | 0, l, _ => ⟨l, rfl⟩
  | fuel + 1, l, hw => by
    simp only [consolidateBin]
    cases hp : l.av.fast.pop i with
    | none => exact ⟨l, rfl⟩
    | some v =>
      obtain ⟨p, fs⟩ := v
      simp only
      obtain ⟨hst₁, d, hd, hda, hd'⟩ := consPop_step hw hp
      have ht₁ : TopWF C (l.av.tiles.relabel p .internal) := hst₁.wf.arena.tiles
      obtain ⟨R₁, s, pre, post, R₂, hr, ha⟩ := runs_of_chunk ht₁ hd'
      simp only at hr ha
      obtain ⟨⟨r, l₂⟩, hc⟩ := coalesce_ok
        (l := { l with av := { l.av with fast := fs, tiles := l.av.tiles.relabel p .internal } })
        hst₁.wf hr ha
      have hst₂ := coalesce_spec' hst₁.wf hr ha hc
      rw [hc, ok_bind]
      exact consolidateBin_ok i fuel hst₂.wf

theorem consolidate_fold_ok : ∀ (is : List Nat) {l : Local}, LocalWF C l.hf →
    ∃ l', is.foldlM (fun l i => consolidateBin i ((l.av.fast.lists i).length) l) l = .ok l'
  | [], l, _ => ⟨l, rfl⟩
  | i :: is, l, hw => by
    rw [List.foldlM_cons]
    obtain ⟨l₁, hc⟩ := consolidateBin_ok (C := C) i ((l.av.fast.lists i).length) hw
    obtain ⟨hst₁, -, -⟩ := consolidateBin_spec i _ hw hc
    rw [hc, ok_bind]
    exact consolidate_fold_ok is hst₁.wf

/-- **`malloc_consolidate` does not abort.** -/
theorem consolidate_ok {l : Local} (hw : LocalWF C l) : ∃ l', consolidate C l = .ok l' := by
  unfold consolidate; exact consolidate_fold_ok _ hw.hf

theorem systrim_ok (l : Local) (pad : Nat) : ∃ l', systrim C l pad = .ok l' := by
  unfold systrim
  dsimp only
  split
  · exact ⟨_, rfl⟩
  split
  · exact ⟨_, rfl⟩
  split
  · exact ⟨_, rfl⟩
  split
  · exact ⟨_, rfl⟩
  split
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- **`heap_trim` does not abort on an arena with a heap.** -/
theorem heapTrim_ok {l : Local} (hh : l.av.heaps ≠ []) (pad : Nat) : ∃ l', heapTrim C l pad = .ok l' := by
  unfold heapTrim
  dsimp only
  split
  · exact ⟨_, rfl⟩
  split
  · exact ⟨_, rfl⟩
  split
  · exact ⟨_, rfl⟩
  split
  · exact ⟨_, rfl⟩
  split
  · exact absurd ‹_› hh
  split
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem maybeConsolidate_ok {l : Local} (hw : LocalWF C l) (hh : l.isMain = false → l.av.heaps ≠ [])
    (size : Nat) : ∃ l', maybeConsolidate C l size = .ok l' := by
  have tail : ∀ l₂ : Local, l₂.isMain = l.isMain → l₂.av.heaps = l.av.heaps →
      ∃ l', (if l₂.isMain = true then
        (if l₂.shared.mm.mp.trimThreshold ≤ l₂.av.tiles.topSize then systrim C l₂ C.topPad else pure l₂)
       else heapTrim C l₂ C.topPad) = .ok l' := by
    intro l₂ hm hhp
    split
    · split
      · exact systrim_ok l₂ _
      · exact ⟨l₂, rfl⟩
    · rename_i hn
      exact heapTrim_ok (by rw [hhp]; exact hh (by rw [← hm]; simpa using hn)) _
  unfold maybeConsolidate
  dsimp only
  split
  · exact ⟨l, rfl⟩
  split
  · obtain ⟨l₂, hc⟩ := consolidate_ok hw
    rw [hc, ok_bind]
    have hst := consolidate_step hw hc
    exact tail l₂ (by rw [hst.eq]) hst.heaps
  · exact tail l rfl rfl

/-- **The merge path does not abort** (`heap_trim` needs the heap of a non-main arena). -/
theorem freeMerge_ok {l : Local} (hw : LocalWF C l) (hh : l.isMain = false → l.av.heaps ≠ [])
    {d : Chunk} (hd : d ∈ l.av.tiles.heapChunks) (hdu : d.use = .client) :
    ∃ l', freeMerge C l d.addr = .ok l' := by
  obtain ⟨hw1, -⟩ := relabelInternal_step hw hd hdu
  obtain ⟨R₁, s, pre, post, R₂, hr, ha⟩ := runs_of_chunk hw.arena.tiles hd
  rw [hdu] at hr
  have hr1 := TopSt.runs_relabel (x := (d.size, .client)) .internal hr ha hw.arena.tiles.nodup
  obtain ⟨⟨size, l₂⟩, hc⟩ := coalesce_ok (l := l.relabel d.addr .internal) hw1.hf hr1 ha
  have hst := coalesce_spec' (l := l.relabel d.addr .internal) hw1.hf hr1 ha hc
  have hw2 : LocalWF C l₂ := hst.wf.of_hf fun hne => by
    rw [hst.fast] at hne ⊢; exact hw1.arena.fast.flag hne
  have hm2 : l₂.isMain = l.isMain := by rw [hst.eq]; rfl
  unfold freeMerge
  rw [hc, ok_bind]
  exact maybeConsolidate_ok hw2 (fun hm => by rw [hst.heaps]; exact hh (by rw [← hm2]; exact hm)) size

/-! ## `_int_free` -/

/-- The opening of `_int_free` on a lent-out, not parked payload of the arena. -/
theorem intFree_open (hC : C.Ok) {l : Local} (hw : LocalWF C l) {p u : Nat} (hpu : (p, u) ∈ l.arenaLive C) :
    ∃ ch ∈ l.av.chunks, ch.use = .client ∧ p = ch.addr + C.hdr ∧ u = usable C ch false ∧
      (ch.addr + C.hdr, ch.size - C.sizeSz) ∉ l.thread.parked C ∧
      l.av.tiles.find? ch.addr = some ch ∧ ¬ (ch.addr % C.align ≠ 0 ∨ 2 ^ 64 < ch.addr + ch.size) ∧
      ¬ (ch.size < C.minSize ∨ ch.size % C.align ≠ 0) := by
  have hpu' := hpu
  unfold Local.arenaLive at hpu'
  obtain ⟨hout, hnp⟩ := List.mem_filter.mp hpu'
  obtain ⟨ch, hchv, hpe⟩ := List.mem_map.mp hout
  obtain ⟨hch, hcu⟩ := List.mem_filter.mp hchv
  have hcu' : ch.use = .client := by simpa using hcu
  simp only [Prod.mk.injEq] at hpe
  obtain ⟨rfl, rfl⟩ := hpe
  have htw := hw.arena.tiles
  have hsz := htw.sizes ch hch
  have hal := htw.aligned ch hch
  have hb := htw.bound ch hch
  have _ := hC
  refine ⟨ch, hch, hcu', rfl, rfl, ?_, find?_addr htw.nodup hch, by omega, by omega⟩
  simpa [List.contains_iff_mem, usable] using hnp

/-- `_int_free` after the tcache: the fastbin or merge path. -/
abbrev freeRest (C : Config) (l : Local) (ch : Chunk) : Res Local :=
  if ch.size ≤ C.maxFast then
    (if (l.av.fast.lists (C.fidx ch.size)).head? = some ch.addr then
      (Except.error Abort.doubleFreeFasttop : Res Local)
     else .ok (l.fastPush ch.addr (C.fidx ch.size)))
  else freeMerge C l ch.addr

/-- **`_int_free`'s shape** on a checked client chunk: the tcache, then `freeRest`. -/
theorem intFree_eq {l : Local} {ch : Chunk} (hf : l.av.tiles.find? ch.addr = some ch)
    (hcu : ch.use = .client) (h1 : ¬ (ch.addr % C.align ≠ 0 ∨ 2 ^ 64 < ch.addr + ch.size))
    (h2 : ¬ (ch.size < C.minSize ∨ ch.size % C.align ≠ 0)) :
    intFree C l ch.addr =
      match l.thread.tcache with
      | some tc =>
        if C.tidx ch.size < C.tcacheBins then
          if (ch.addr, ch.size) ∈ tc.bins (C.tidx ch.size) then .error .doubleFreeTcache
          else if (tc.bins (C.tidx ch.size)).length < C.tcacheCount then
            .ok (tcPut l (ch.addr, ch.size) (C.tidx ch.size))
          else freeRest C l ch
        else freeRest C l ch
      | none => freeRest C l ch := by
  unfold intFree
  rw [hf]
  simp only [hcu, h1, h2, ↓reduceIte]
  cases l.thread.tcache with
  | none => rfl
  | some tc =>
    simp only
    split
    · split
      · rfl
      · split <;> rfl
    · rfl

/-- **`Algo.totalFree`**. -/
theorem totalFree (C : Config) : Task.algo.totalFree C := by
  intro hC l hw hsp p u hpu
  obtain ⟨ch, hch, hcu, rfl, rfl, hnp, hf, h1, h2⟩ := intFree_open hC hw hpu
  have hpc : ch.addr + C.hdr - C.hdr = ch.addr := by omega
  rw [hpc, intFree_eq hf hcu h1 h2]
  have hrest : ∃ l', freeRest C l ch = .ok l' := by
    unfold freeRest
    split
    · split
      · exfalso
        rename_i hh
        cases hl : l.av.fast.lists (C.fidx ch.size) with
        | nil => rw [hl] at hh; cases hh
        | cons b rest =>
          rw [hl] at hh
          simp only [List.head?_cons, Option.some.injEq] at hh
          obtain ⟨d, hdv, hda, hdu⟩ := (hw.arena.fast.exact _ b).mp (by rw [hl]; exact List.mem_cons_self ..)
          have hd : d ∈ l.av.tiles.heapChunks := (List.mem_filter.mp hdv).1
          have := chunk_unique hw.arena.tiles.nodup hd hch (hda.trans hh)
          subst this
          rw [hcu] at hdu; cases hdu
      · exact ⟨_, rfl⟩
    · exact freeMerge_ok hw hsp.heaps hch hcu
  cases htc : l.thread.tcache with
  | none => exact hrest
  | some tc =>
    simp only
    split
    · split
      · rename_i hin
        exact absurd (mem_parked_of (hw.tcache tc htc) htc hin) (by simpa [epay] using hnp)
      · split
        · exact ⟨_, rfl⟩
        · exact hrest
    · exact hrest

/-- **The fastbin and merge paths' frame**: the thread is kept. -/
theorem freeRest_frame (hC : C.Ok) {l l' : Local} (hw : LocalWF C l) (hsp : LocalSp C l) {ch : Chunk}
    (hch : ch ∈ l.av.chunks) (hcu : ch.use = .client) (h : freeRest C l ch = .ok l')
    (hw' : LocalWF C l') :
    Frame C l l' [(ch.addr + C.hdr, usable C ch false)] ∧ KeptAway l l' := by
  unfold freeRest at h
  split at h
  · split at h
    · cases h
    · cases h
      refine ⟨frame_of hsp hw'.apart rfl rfl rfl (Shrink.of_arena rfl rfl (spanCover_relabel rfl rfl) rfl)
        (clients_of_out hC hw hw' (List.Perm.of_eq
          (out_relabel_client hw.arena.tiles.nodup hch hcu (by simp) (TopSt.heapChunks_relabel ..))))
        (fun tc' i e htc he => .inl ⟨tc', i, htc, he⟩), fun tc i e htc he _ => ⟨tc, htc, he⟩⟩
  · obtain ⟨-, h1, -, h3, h4, h5⟩ := freeMerge_spec hC hw hch hcu h
    exact ⟨frame_of hsp hw'.apart h1 h4 (by rw [h3]) (freeMerge_shrink hC hw hch hcu h)
      (clients_of_out hC hw hw' h5)
      (fun tc' i e htc he => .inl ⟨tc', i, by rw [h3] at htc; exact htc, he⟩),
      fun tc i e htc he _ => ⟨tc, by rw [h3]; exact htc, he⟩⟩

/-- **`Algo.bodyFree`**. -/
theorem bodyFree (C : Config) : Task.algo.bodyFree C := by
  intro hC l l' p u hw hsp hpu h
  have hwf := wfIntFree C hC l l' p u hw hpu h
  obtain ⟨ch, hch, hcu, rfl, rfl, hnp, hf, h1, h2⟩ := intFree_open hC hw hpu
  have hpc : ch.addr + C.hdr - C.hdr = ch.addr := by omega
  rw [hpc, intFree_eq hf hcu h1 h2] at h
  have hw' := hwf.1
  suffices hfk : Frame C l l' [(ch.addr + C.hdr, usable C ch false)] ∧ KeptAway l l' from
    ⟨hw', hfk.1, hfk.2, hwf.2.2⟩
  cases htc : l.thread.tcache with
  | none => rw [htc] at h; exact freeRest_frame hC hw hsp hch hcu h hw'
  | some tc =>
    rw [htc] at h
    simp only at h
    split at h
    · split at h
      · cases h
      · split at h
        · have hl' : l' = { l with thread := { l.thread with
              tcache := some (tc.put (ch.addr, ch.size) (C.tidx ch.size)) } } := by
            cases h; simp [tcPut, Local.tcachePut, htc]
          subst hl'
          refine ⟨frame_of hsp hw'.apart rfl rfl rfl (Shrink.of_arena rfl rfl (SpanCover.refl _) rfl)
            (fun c hc _ _ => hc) ?_, ?_⟩
          · intro tc' j e htc' he
            simp only [Option.some.injEq] at htc'
            subst htc'
            simp only [TcacheSt.put] at he
            split at he
            · rename_i hj
              subst hj
              rcases List.mem_cons.mp he with rfl | he
              · exact .inr ⟨⟨ch, hch, rfl, rfl, hcu⟩, .inl (by simp [usable])⟩
              · exact .inl ⟨tc, _, htc, he⟩
            · exact .inl ⟨tc, j, htc, he⟩
          · intro tc₀ j e htc₀ he _
            rw [htc] at htc₀
            cases htc₀
            refine ⟨_, rfl, ?_⟩
            simp only [TcacheSt.put]
            split
            · exact List.mem_cons_of_mem _ he
            · exact he
        · exact freeRest_frame hC hw hsp hch hcu h hw'
    · exact freeRest_frame hC hw hsp hch hcu h hw'

end Silmaril.Libc.Ptmalloc.Algo
