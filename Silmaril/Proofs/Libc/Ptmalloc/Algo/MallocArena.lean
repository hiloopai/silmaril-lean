module

public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocBins

/-!
# ptmalloc algorithm: the arena steps of `_int_malloc`'s bin paths

Generic steps on a free chunk `d` (in the unsorted bin or a small/large bin), each with the
lists the caller computed for the chunk taken out (the views of the tiling with `d` held
`internal`):

* `relabelLend`: lend `d` out whole (exact fit, `takeFit` without remainder): an `MBody`;
* `relabelSort`: move `d` to a small/large bin (the unsorted scan's sorting): an `MStep`.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc

theorem relabelRun_twice (a : Nat) (u u' : Use) : ∀ (s : Nat) (cs : List (Nat × Use)),
    relabelRun a u' s (relabelRun a u s cs) = relabelRun a u' s cs
  | _, [] => rfl
  | s, (sz, v) :: cs => by
    simp only [relabelRun, relabelRun_twice a u u' (s + sz) cs]
    by_cases h : s = a <;> simp [h]

theorem TopSt.relabel_twice (ts : TopSt) (a : Nat) (u u' : Use) :
    (ts.relabel a u).relabel a u' = ts.relabel a u' := by
  simp only [TopSt.relabel, relabelRun_twice, List.map_map, Function.comp_def]

theorem map_relabelAt_twice (a : Nat) (u u' : Use) (cs : List Chunk) :
    (cs.map (Chunk.relabelAt a u)).map (Chunk.relabelAt a u') = cs.map (Chunk.relabelAt a u') := by
  rw [List.map_map]
  congr 1
  funext c
  by_cases h : c.addr = a
  · simp [Chunk.relabelAt_of_eq h, Chunk.relabelAt_of_eq (c := { c with use := u }) h]
  · simp [Chunk.relabelAt_of_ne h]

/-- A view that sees neither of two uses is the same after relabelling to either. -/
theorem view_relabel_both {p : Use → Bool} {a : Nat} {u u' : Use} (hu : p u = false) (hu' : p u' = false) :
    ∀ cs : List Chunk, Chunk.view p (cs.map (Chunk.relabelAt a u)) = Chunk.view p (cs.map (Chunk.relabelAt a u'))
  | [] => rfl
  | c :: cs => by
    have ih := view_relabel_both (a := a) hu hu' cs
    simp only [Chunk.view, List.map_cons, List.filter_cons] at ih ⊢
    by_cases h : c.addr = a
    · simp [Chunk.relabelAt_of_eq h, hu, hu', ih]
    · simp only [Chunk.relabelAt_of_ne h, ih]

/-- **Relabelling a chunk to `client`** adds it to the client view (up to order). -/
theorem view_client_relabel_to {a : Nat} {d : Chunk} (hda : d.addr = a) (hdu : d.use ≠ .client) :
    ∀ {cs : List Chunk}, (cs.map (·.addr)).Nodup → d ∈ cs →
      (Chunk.view (· = .client) (cs.map (Chunk.relabelAt a .client))).Perm
        ({ d with use := .client } :: Chunk.view (· = .client) cs)
  | [], _, h => by cases h
  | c :: cs, hn, hd => by
    rw [List.map_cons, List.nodup_cons] at hn
    by_cases hc : c.addr = a
    · have hcd : c = d := chunk_unique (cs := c :: cs) (by rw [List.map_cons, List.nodup_cons]; exact hn)
        (List.mem_cons_self ..) hd (hc.trans hda.symm)
      subst hcd
      have hrest : ∀ e ∈ cs, e.addr ≠ a := fun e he h => hn.1 (by rw [hc, ← h]; exact List.mem_map_of_mem he)
      rw [List.map_cons, Chunk.relabelAt_of_eq hc, Algo.map_relabelAt_of_not_mem hrest]
      simp [Chunk.view, hdu]
    · have hd' : d ∈ cs := by
        rcases List.mem_cons.mp hd with rfl | h
        · exact absurd hda hc
        · exact h
      rw [List.map_cons, Chunk.relabelAt_of_ne hc]
      have ih := view_client_relabel_to hda hdu hn.2 hd'
      simp only [Chunk.view, List.filter_cons] at ih ⊢
      split
      · exact (List.Perm.cons _ ih).trans (List.Perm.swap _ _ _)
      · exact ih

namespace Algo

variable {C : Config}

theorem request2size_ge (hC : C.Ok) (n : Nat) : n + C.sizeSz ≤ C.request2size n := by
  have h8 := hC.sizeSz; have h16 := hC.align; have h32 := hC.minSize
  unfold Config.request2size Config.alignMask
  rw [h8, h16, h32]
  split <;> omega

theorem request2size_spec (hC : C.Ok) {n nb : Nat} (h : C.checkedRequest2size n = some nb) :
    n + C.sizeSz ≤ nb ∧ nb % C.align = 0 ∧ C.minSize ≤ nb := by
  unfold Config.checkedRequest2size at h
  split at h
  · cases h
  · simp only [Option.some.injEq] at h
    subst h
    refine ⟨request2size_ge hC n, ?_, ?_⟩ <;>
    · have h8 := hC.sizeSz; have h16 := hC.align; have h32 := hC.minSize
      unfold Config.request2size Config.alignMask
      rw [h8, h16, h32]
      split <;> omega

theorem not_fast_of_free {u : Use} (h : u.tagFree = true) : u.isFast = false := by
  cases u <;> simp_all [Use.tagFree, Use.isFast]

theorem not_client_of_free {u : Use} (h : u.tagFree = true) : u ≠ .client := by
  rintro rfl; simp [Use.tagFree] at h

/-- Relabelling a non-client chunk keeps the client chunks. -/
theorem keep_clients {cs : List Chunk} {a : Nat} {u : Use} (hn : (cs.map (·.addr)).Nodup) {d : Chunk}
    (hd : d ∈ cs) (hda : d.addr = a) (hdu : d.use ≠ .client) :
    ∀ c ∈ cs, c.use = .client → c ∈ cs.map (Chunk.relabelAt a u) := by
  intro c hc hcu
  have hca : c.addr ≠ a := fun h => by
    have := chunk_unique hn hc hd (h.trans hda.symm); subst this; exact hdu hcu
  exact List.mem_map.mpr ⟨c, hc, Chunk.relabelAt_of_ne hca⟩

/-- The lent-out payloads after relabelling a non-client chunk to `client`. -/
theorem out_relabelClient {av av' : ArenaSt} (hn : (av.tiles.heapChunks.map (·.addr)).Nodup) {d : Chunk}
    (hd : d ∈ av.tiles.heapChunks) (hnc : d.use ≠ .client) (ht : av'.tiles = av.tiles.relabel d.addr .client) :
    (av'.out C).Perm ((d.addr + C.hdr, d.size - C.sizeSz) :: av.out C) := by
  unfold ArenaSt.out ArenaSt.chunks
  rw [ht, TopSt.heapChunks_relabel]
  have := (view_client_relabel_to rfl hnc hn hd).map (fun c : Chunk => (c.addr + C.hdr, usable C c false))
  simpa [usable] using this

/-- **Lending a free chunk out whole** (the unsorted scan's exact fit, `takeFit` without a
remainder): given the bins and the unsorted bin without it, an `MBody`. -/
theorem relabelLend (hC : C.Ok) {n : Nat} {l : Local} (hw : LocalWF C l) (hs : LocalSp C l)
    {d : Chunk} (hd : d ∈ l.av.chunks) (hdu : d.use.tagFree = true) (hn : n + C.sizeSz ≤ d.size)
    (bs : BinsSt) (us : UnsortedSt)
    (hbins : BinsWF C bs (Chunk.view Use.isSorted (l.av.chunks.map (Chunk.relabelAt d.addr .internal)))
      l.av.tiles.sizeAt)
    (hus : UnsortedWF C us (Chunk.view Use.isUnsorted (l.av.chunks.map (Chunk.relabelAt d.addr .internal)))) :
    MBody C n l (d.addr + C.hdr)
      { l with av := { l.av with tiles := l.av.tiles.relabel d.addr .client, bins := bs, unsorted := us } } := by
  have ht := hw.arena.tiles
  have hn' := ht.nodup
  have ht' := ht.relabel (a := d.addr) (u := .client) rfl
  have hH : (l.av.tiles.relabel d.addr .client).heapChunks = l.av.chunks.map (Chunk.relabelAt d.addr .client) :=
    TopSt.heapChunks_relabel ..
  have hnc := not_client_of_free hdu
  have hav : ArenaWF C { l.av with tiles := l.av.tiles.relabel d.addr .client, bins := bs, unsorted := us } :=
    { tiles := ht'
      fast := by
        show FastWF C l.av.fast (Chunk.view Use.isFast (l.av.tiles.relabel d.addr .client).heapChunks)
        rw [view_relabel_of hn' hd rfl (not_fast_of_free hdu) rfl]; exact hw.arena.fast
      bins := by
        show BinsWF C bs (Chunk.view Use.isSorted (l.av.tiles.relabel d.addr .client).heapChunks)
          (l.av.tiles.relabel d.addr .client).sizeAt
        rw [hH, TopSt.sizeAt_relabel, view_relabel_both (u := .client) (u' := .internal) rfl rfl]
        exact hbins
      unsorted := by
        show UnsortedWF C us (Chunk.view Use.isUnsorted (l.av.tiles.relabel d.addr .client).heapChunks)
        rw [hH, view_relabel_both (u := .client) (u' := .internal) rfl rfl]
        exact hus
      internal := fun c hc _ => ht'.minSize_all c hc }
  have hw' := hw.withAv _ hav rfl rfl rfl rfl (TopSt.relabel_old_nil ..) (TopSt.spans_relabel ..)
  have hd' : { d with use := .client } ∈ (l.av.tiles.relabel d.addr .client).heapChunks := by
    rw [hH]; exact List.mem_map.mpr ⟨d, hd, Chunk.relabelAt_of_eq rfl⟩
  refine MBody.of_arena hC hw' hs (by
      show SpansIn ((l.av.tiles.relabel d.addr .client).spans ++ l.av.heapSpans)
        (l.av.tiles.spans ++ l.av.heapSpans)
      rw [TopSt.spans_relabel]; exact SpansIn.refl _) rfl
    (fun c hc hcu => by
      show c ∈ (l.av.tiles.relabel d.addr .client).heapChunks
      rw [hH]; exact keep_clients hn' hd rfl hnc c hc hcu)
    (d := { d with use := .client }) hd' (fun c hc hca hcu => by
      have := chunk_unique hn' hc hd hca; subst this; exact hnc hcu) ?_ hn
  exact out_relabelClient (d := d) hn' hd hnc rfl

/-- The payload of an arena chunk that is not a client is not parked (the tcache holds client
chunks of the arena or chunks away from it). -/
theorem not_parked_of (hC : C.Ok) {l : Local} (hw : LocalWF C l) (hs : LocalSp C l) {d : Chunk}
    (hd : d ∈ l.av.chunks) (hnot : ∀ c ∈ l.av.chunks, c.addr = d.addr → c.use ≠ .client) :
    (d.addr + C.hdr, d.size - C.sizeSz) ∉ l.thread.parked C ∧
      ∀ tc, l.thread.tcache = some tc → ∀ i e, e ∈ tc.bins i → e.1 ≠ d.addr := by
  have h8 := hC.sizeSz
  have key : ∀ tc, l.thread.tcache = some tc → ∀ i e, e ∈ tc.bins i → e.1 ≠ d.addr := by
    intro tc htc i e he hea
    rcases hs.entries tc htc i e he with ⟨c, hc, h1, -, h3⟩ | ⟨ha, -⟩
    · exact hnot c hc (h1.trans hea) h3
    · have hdpos : 0 < d.size := by have := (hw.arena.tiles.sizes d hd).2; have := hC.minSize; omega
      have hepos := entry_pos hC hw htc he
      rcases ha _ (mem_spans_of_chunk hd) with h3 | h3 <;> simp only at h3 <;> omega
  refine ⟨fun hp => ?_, key⟩
  obtain ⟨tc, htc, i, -, e, he, hpe⟩ := mem_parked.mp hp
  simp only [epay, Prod.mk.injEq] at hpe
  exact key tc htc i e he (by unfold Config.hdr at hpe; omega)

/-- **The tcache stash of the unsorted scan's exact fit** (`tcache_put` of the fitting unsorted
chunk, the scan going on): an `MStep`. -/
theorem stashStep (hC : C.Ok) {l : Local} (hw : LocalWF C l) (hs : LocalSp C l)
    {d : Chunk} (hd : d ∈ l.av.chunks) (hdu : d.use = .bin 1)
    (us : UnsortedSt)
    (hus : UnsortedWF C us (Chunk.view Use.isUnsorted (l.av.chunks.map (Chunk.relabelAt d.addr .internal))))
    {tc : TcacheSt} (htc : l.thread.tcache = some tc) {t : Nat} (ht : t < C.tcacheBins)
    (hidx : C.tidx d.size = t) (hroom : (tc.bins t).length < C.tcacheCount) :
    MStep C l (tcPut { l with av := { l.av with tiles := l.av.tiles.relabel d.addr .client, unsorted := us } } (d.addr, d.size) t) := by
  have h8 := hC.sizeSz
  have hn' := hw.arena.tiles.nodup
  have hnc : d.use ≠ .client := by rw [hdu]; simp
  have hnot : ∀ c ∈ l.av.chunks, c.addr = d.addr → c.use ≠ .client := fun c hc hca hcu => by
    have := chunk_unique hn' hc hd hca; subst this; exact hnc hcu
  have hbins : BinsWF C l.av.bins (Chunk.view Use.isSorted (l.av.chunks.map (Chunk.relabelAt d.addr .internal)))
      l.av.tiles.sizeAt := by
    have : Chunk.view Use.isSorted (l.av.chunks.map (Chunk.relabelAt d.addr .internal)) = l.av.sortedView := by
      show Chunk.view _ (l.av.tiles.heapChunks.map _) = _
      rw [← TopSt.heapChunks_relabel]
      exact view_relabel_of hn' hd rfl (by rw [hdu]; rfl) rfl
    rw [this]; exact hw.arena.bins
  have hb := relabelLend (n := 0) hC hw hs hd (by rw [hdu]; rfl) (by have := (hw.arena.tiles.sizes d hd).2; have := hC.minSize; omega)
    l.av.bins us hbins hus
  obtain ⟨⟨hw₁, -, -⟩, hF, hK, -⟩ := hb
  -- the put
  have hput : tcPut { l with av := { l.av with tiles := l.av.tiles.relabel d.addr .client, unsorted := us } } (d.addr, d.size) t =
      { l with av := { l.av with tiles := l.av.tiles.relabel d.addr .client, unsorted := us }, thread := { l.thread with tcache := some (tc.put (d.addr, d.size) t) } } := by
    simp [tcPut, Local.tcachePut, htc]
  have hnp := (not_parked_of hC hw hs hd hnot)
  have hsz := hw.arena.tiles.sizes d hd
  have hdal := hw.arena.tiles.aligned d hd
  have hdnn := hw.arena.tiles.nonNull d hd
  have hfit : ∀ tc', ({ l with av := { l.av with tiles := l.av.tiles.relabel d.addr .client, unsorted := us } } : Local).thread.tcache = some tc' → (d.addr, d.size) ∉ tc'.bins t ∧
      (tc'.bins t).length < C.tcacheCount := by
    intro tc' h'
    have h' : l.thread.tcache = some tc' := h'
    rw [htc] at h'; cases h'
    exact ⟨fun hm => hnp.2 tc htc t _ hm rfl, hroom⟩
  have hw₂ : LocalWF C { l with av := { l.av with tiles := l.av.tiles.relabel d.addr .client, unsorted := us }, thread := { l.thread with tcache := some (tc.put (d.addr, d.size) t) } } :=
    (leafTcachePut C { l with av := { l.av with tiles := l.av.tiles.relabel d.addr .client, unsorted := us } }
      { l with av := { l.av with tiles := l.av.tiles.relabel d.addr .client, unsorted := us }, thread := { l.thread with tcache := some (tc.put (d.addr, d.size) t) } }
      (d.addr, d.size) t hC hw₁ ht hidx hsz.1 hsz.2 hdnn hdal hfit
      (by simp [Local.tcachePut, htc])).1
  rw [hput]
  refine ⟨hw₂, ?_, ?_, ?_, fun h => by rw [htc] at h; cases h⟩
  · -- live: the chunk is lent out and parked
    have hout₁ := out_relabelClient (C := C) (av := l.av)
      (av' := { l.av with tiles := l.av.tiles.relabel d.addr .client, unsorted := us }) hn' hd hnc rfl
    have hP : (ThreadSt.parked C { l.thread with tcache := some (tc.put (d.addr, d.size) t) }).Perm
        ((d.addr + C.hdr, d.size - C.sizeSz) :: l.thread.parked C) := by
      simp only [ThreadSt.parked, htc, Option.map_some, Option.getD_some]
      exact TcacheSt.payloads_put ht
    unfold Local.live
    simp only
    refine List.Perm.append_right _ ?_
    have hnd := out_nodup (C := C) hw₁.arena.tiles
    simp only at hnd
    rw [filter_not_mem_cons hnd hP]
    have h1 := (hout₁.filter (fun y => !(l.thread.parked C).contains y))
    rw [List.filter_cons_of_pos (by simpa [contains_false] using hnp.1)] at h1
    exact (h1.erase _).trans (by simp)
  · exact
    { avAddr := rfl, isMain := rfl, spatial := hF.spatial, covered := hF.covered,
      brkStart := rfl, nonMain := fun _ => ⟨rfl, rfl⟩, acct := fun _ => Nat.le_refl _, init := rfl, arenas := ⟨rfl, rfl, rfl⟩,
      arena := rfl, heaps := hF.heaps, clients := hF.clients,
      fresh := fun tc' i e htc' he => by
        simp only [Option.some.injEq] at htc'
        subst htc'
        simp only [TcacheSt.put] at he
        by_cases hi : i = t
        · subst hi
          simp only [ite_true, List.mem_cons] at he
          rcases he with rfl | he
          · refine .inr ⟨⟨{ d with use := .client }, ?_, rfl, rfl, rfl⟩, .inr hnot⟩
            show _ ∈ (l.av.tiles.relabel d.addr .client).heapChunks
            rw [TopSt.heapChunks_relabel]; exact List.mem_map.mpr ⟨d, hd, Chunk.relabelAt_of_eq rfl⟩
          · exact .inl ⟨tc, i, htc, he⟩
        · simp only [hi, ite_false] at he
          exact .inl ⟨tc, i, htc, he⟩ }
  · intro tc' i e htc' he _
    rw [htc] at htc'; cases htc'
    refine ⟨_, rfl, ?_⟩
    simp only [TcacheSt.put]
    by_cases hi : i = t
    · subst hi; simp only [ite_true]; exact List.mem_cons_of_mem _ he
    · simp only [hi, ite_false]; exact he

/-- `tcache_get` parks the popped entry's payload less. -/
theorem payloads_get_eq {tc : TcacheSt} (hw : TcacheWF C tc) {i : Nat} {e : Nat × Nat}
    {rest : List (Nat × Nat)} (hb : tc.bins i = e :: rest) :
    (tc.payloads C).Perm (epay C e ::
      ({ tc with bins := fun j => if j = i then rest else tc.bins j } : TcacheSt).payloads C) := by
  have hi : i < C.tcacheBins := by
    refine Nat.lt_of_not_le fun hle => ?_
    have := hw.bins i hle; rw [hb] at this; cases this
  unfold TcacheSt.payloads
  have hp := TcacheSt.flatMap_update_perm tc.bins i e rest hb (List.range C.tcacheBins) List.nodup_range
    (List.mem_range.mpr hi)
  exact (hp.map _).trans (by simp [epay])

/-- **`return tcache_get (tc_idx)`** of a client chunk of the arena at the head of the bin: an
`MBody`. -/
theorem getLend (hC : C.Ok) {n : Nat} {l : Local} (hw : LocalWF C l) (hs : LocalSp C l)
    {tc : TcacheSt} (htc : l.thread.tcache = some tc) {t : Nat} {e : Nat × Nat}
    {rest : List (Nat × Nat)} (hb : tc.bins t = e :: rest)
    {c : Chunk} (hc : c ∈ l.av.chunks) (hca : c.addr = e.1) (hcs : c.size = e.2)
    (hcu : c.use = .client) (hn : n + C.sizeSz ≤ e.2) :
    ∃ p l', l.tcacheGet C t = some (p, l') ∧ MBody C n l p l' := by
  have h8 := hC.sizeSz; have h16 := hC.align
  have htw := hw.tcache tc htc
  have hn' := hw.arena.tiles.nodup
  obtain ⟨tc', htc'⟩ : ∃ tc' : TcacheSt, tc' = { tc with bins := fun j => if j = t then rest else tc.bins j } :=
    ⟨_, rfl⟩
  have hget : l.tcacheGet C t = some (e.1 + C.hdr, { l with thread := { l.thread with tcache := some tc' } }) := by
    simp [Local.tcacheGet, htc, TcacheSt.get, hb, htc']
  refine ⟨_, _, hget, ?_⟩
  have hw' := (leafTcacheGet C l _ t _ hC hw hget).1
  have hsub : ∀ j x, x ∈ tc'.bins j → x ∈ tc.bins j := by
    intro j x hx; by_cases hj : j = t
    · subst hj; simp only [htc', ite_true] at hx; rw [hb]; exact List.mem_cons_of_mem _ hx
    · simpa [htc', hj] using hx
  have he : e ∈ tc.bins t := by rw [hb]; exact List.mem_cons_self ..
  -- the popped payload is no longer parked
  have hP : (l.thread.parked C).Perm (epay C e ::
      ({ l.thread with tcache := some tc' } : ThreadSt).parked C) := by
    simp only [ThreadSt.parked, htc, Option.map_some, Option.getD_some]
    rw [htc']; exact payloads_get_eq htw hb
  have hnp' : epay C e ∉ ({ l.thread with tcache := some tc' } : ThreadSt).parked C := by
    intro hm
    obtain ⟨tc1, h1, j, -, x, hx, hxe⟩ := mem_parked.mp hm
    simp only [Option.some.injEq] at h1; subst h1
    have hxs := htw.size j x (hsub j x hx)
    have hes := htw.size t e he
    have := epay_inj hxe.symm (by have := hC.minSize; omega) (by have := hC.minSize; omega)
    subst this
    by_cases hj : j = t
    · subst hj; simp only [htc', ite_true] at hx
      have hnd := (htw.nodup j).1; rw [hb] at hnd; exact (List.nodup_cons.mp hnd).1 hx
    · exact hj (hxs.1.symm.trans hes.1)
  have hpay : epay C e = (c.addr + C.hdr, c.size - C.sizeSz) := by simp [epay, hca, hcs]
  have hout : epay C e ∈ l.av.out C := by rw [hpay]; exact mem_out.mpr ⟨c, hc, hcu, rfl⟩
  have hpk : epay C e ∈ l.thread.parked C := hP.symm.subset (List.mem_cons_self ..)
  have hal : e.1 % C.align = 0 := (htw.nonNull t e he).2
  refine ⟨⟨hw', within_empty rfl rfl, .inr ⟨by unfold Config.hdr; omega,
    by unfold Config.hdr; rw [h8, h16] at *; omega, e.2 - C.sizeSz, by omega, ?_, ?_⟩⟩, ?_, ?_,
    fun h => by rw [htc] at h; cases h⟩
  · -- the live set
    unfold Local.live
    simp only
    rw [← List.cons_append]
    refine List.Perm.append_right _ ?_
    have hnd := out_nodup (C := C) hw.arena.tiles
    rw [filter_not_mem_cons hnd hP]
    have hm : epay C e ∈ (l.av.out C).filter fun y => !(({ l.thread with tcache := some tc' } : ThreadSt).parked C).contains y :=
      List.mem_filter.mpr ⟨hout, by simpa [contains_false] using hnp'⟩
    exact List.perm_cons_erase hm
  · intro q hq
    rcases mem_llive.mp hq with ⟨hqo, hqp⟩ | hqm
    · obtain ⟨c', hc', hcu', rfl⟩ := mem_out.mp hqo
      have hne : c'.addr ≠ c.addr := fun h => by
        have := chunk_unique hn' hc' hc h; subst this
        exact hqp (by rw [← hpay]; exact hpk)
      have hap := Apart.ne_apart hw.apart (mem_spans_of_chunk hc') (mem_spans_of_chunk hc)
        (fun h => hne (congrArg Prod.fst h))
      have := pay_apart hC (kok_arena hw hc') (kok_arena hw hc) hap
      simp only [kpay, usable, Bool.false_eq_true, ite_false] at this
      rw [← hca, ← hcs]; exact this
    · obtain ⟨m, hm, -, rfl⟩ := mem_shlive.mp hqm
      have hm' : (m.addr, m.size) ∈ l.shared.mm.chunks.map (fun c => (c.addr, c.size)) :=
        List.mem_map.mpr ⟨m, hm, rfl⟩
      have hap := Apart.cross hw.apart (span_mem_spans hc) hm'
      have := pay_apart hC (kok_arena hw hc) (kok_mm hw hm) hap
      simp only [kpay, usable, ite_true, Bool.false_eq_true, ite_false] at this
      rw [← hca, ← hcs]; omega
  · exact
    { avAddr := rfl, isMain := rfl, spatial := fun _ _ hc ha => ⟨hc, ha⟩, covered := hs.covered,
      brkStart := rfl, nonMain := fun _ => ⟨rfl, rfl⟩, acct := fun _ => Nat.le_refl _, init := rfl, arenas := ⟨rfl, rfl, rfl⟩,
      arena := rfl, heaps := id, clients := fun _ hc _ _ => hc,
      fresh := fun tc1 i x h1 hx => by
        simp only [Option.some.injEq] at h1; subst h1
        exact .inl ⟨tc, i, htc, hsub i x hx⟩ }
  · intro tc1 i x h1 hx ha
    rw [htc] at h1; cases h1
    refine ⟨tc', rfl, ?_⟩
    by_cases hi : i = t
    · subst hi
      rw [hb] at hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exfalso
        have hm := mem_spans_of_chunk hc
        rw [hca, hcs] at hm
        exact not_away_self hm (entry_pos hC hw htc he) ha
      · simp [htc', hx]
    · simpa [htc', hi] using hx

/-- **Sorting an unsorted chunk into small/large bin `i`** (given the new bins and the unsorted
bin without it): an `MStep`. -/
theorem relabelSort {l : Local} (hw : LocalWF C l) (hs : LocalSp C l)
    {d : Chunk} (hd : d ∈ l.av.chunks) (hdu : d.use = .bin 1) {i : Nat} (hi : 2 ≤ i)
    (bs : BinsSt) (us : UnsortedSt)
    (hbins : BinsWF C bs (Chunk.view Use.isSorted (l.av.chunks.map (Chunk.relabelAt d.addr (.bin i))))
      l.av.tiles.sizeAt)
    (hus : UnsortedWF C us (Chunk.view Use.isUnsorted (l.av.chunks.map (Chunk.relabelAt d.addr .internal)))) :
    MStep C l { l with av := { l.av with tiles := l.av.tiles.relabel d.addr (.bin i), bins := bs, unsorted := us } } := by
  have ht := hw.arena.tiles
  have hn' := ht.nodup
  have hcoal := TopSt.coal_relabel_same (u := .bin i) ⟨ht.coalesced, ht.lastUsed, ht.coalescedOld⟩ hn' hd rfl
    (by rw [hdu]; rfl)
  have ht' := ht.relabel_coal hcoal
  have hH : (l.av.tiles.relabel d.addr (.bin i)).heapChunks = l.av.chunks.map (Chunk.relabelAt d.addr (.bin i)) :=
    TopSt.heapChunks_relabel ..
  have hnc : d.use ≠ .client := by rw [hdu]; simp
  have hav : ArenaWF C { l.av with tiles := l.av.tiles.relabel d.addr (.bin i), bins := bs, unsorted := us } :=
    { tiles := ht'
      fast := by
        show FastWF C l.av.fast (Chunk.view Use.isFast (l.av.tiles.relabel d.addr (.bin i)).heapChunks)
        rw [view_relabel_of hn' hd rfl (by rw [hdu]; rfl) rfl]; exact hw.arena.fast
      bins := by
        show BinsWF C bs (Chunk.view Use.isSorted (l.av.tiles.relabel d.addr (.bin i)).heapChunks)
          (l.av.tiles.relabel d.addr (.bin i)).sizeAt
        rw [hH, TopSt.sizeAt_relabel]; exact hbins
      unsorted := by
        show UnsortedWF C us (Chunk.view Use.isUnsorted (l.av.tiles.relabel d.addr (.bin i)).heapChunks)
        rw [hH, view_relabel_both (u := .bin i) (u' := .internal) (isUnsorted_bin_of hi) rfl]
        exact hus
      internal := fun c hc _ => ht'.minSize_all c hc }
  have hw' := hw.withAv _ hav rfl rfl rfl rfl (TopSt.relabel_old_nil ..) (TopSt.spans_relabel ..)
  refine MStep.of_arena hw' hs (by
      show SpansIn ((l.av.tiles.relabel d.addr (.bin i)).spans ++ l.av.heapSpans)
        (l.av.tiles.spans ++ l.av.heapSpans)
      rw [TopSt.spans_relabel]; exact SpansIn.refl _) rfl ?_
    (fun c hc hcu => by
      show c ∈ (l.av.tiles.relabel d.addr (.bin i)).heapChunks
      rw [hH]; exact keep_clients hn' hd rfl hnc c hc hcu)
  rw [ArenaSt.out_congr (av := l.av) (view_relabel_of hn' hd rfl (by simpa using hnc) (by simp))]

theorem nodup_mid {α β : Type} (f : α → β) {A B : List α} {d : α} (h : ((A ++ d :: B).map f).Nodup) :
    ∀ c ∈ A ++ B, f c ≠ f d := by
  rw [List.map_append, List.map_cons] at h
  have := List.perm_middle.nodup_iff.mp h
  rw [List.nodup_cons] at this
  intro c hc he; apply this.1; rw [← he, ← List.map_append]; exact List.mem_map_of_mem hc

/-- The chunks of a tiling around a chunk `d`, before and after a split of `d`. -/
theorem split_chunks {ts : TopSt} (ht : TopWF C ts) {d : Chunk} (hd : d ∈ ts.heapChunks)
    {nb : Nat} (hle : nb ≤ d.size) (u₁ u₂ : Use) :
    ∃ A B, ts.heapChunks = A ++ d :: B ∧
      (ts.split d.addr nb u₁ u₂).heapChunks = A ++ ⟨d.addr, nb, u₁⟩ :: ⟨d.addr + nb, d.size - nb, u₂⟩ :: B ∧
      ∀ c ∈ A ++ B, c.addr ≠ d.addr := by
  obtain ⟨R₁, s, pre, post, R₂, hr, ha⟩ := runs_of_chunk ht hd
  have hr' := TopSt.runs_split' (x := (d.size, d.use)) nb u₁ u₂ hr ha ht.nodup
  have hH := TopSt.heapChunks_of_runs (ts := ts) (R₁ := R₁) (R₂ := R₂) (s := s) (pre := pre)
    (mid := [(d.size, d.use)]) (post := post) (by rw [hr]; simp)
  have hH' := TopSt.heapChunks_of_runs (ts := ts.split d.addr nb u₁ u₂) (R₁ := R₁) (R₂ := R₂) (s := s)
    (pre := pre) (mid := [(nb, u₁), (d.size - nb, u₂)]) (post := post) (by rw [hr']; simp)
  have hl : runLen [(nb, u₁), (d.size - nb, u₂)] = runLen [(d.size, d.use)] := by simp [runLen]; omega
  rw [hl] at hH'
  have h1 : ts.heapChunks = (TopSt.flat R₁ ++ layout s pre) ++ d :: (layout (s + runLen pre + runLen [(d.size, d.use)]) post ++ TopSt.flat R₂) := by
    rw [hH]; simp [layout, ha]
  refine ⟨_, _, h1, ?_, ?_⟩
  · rw [hH']; simp [layout, ha]
  · have hn := ht.nodup
    rw [h1] at hn
    exact nodup_mid _ hn

/-- Splitting a free chunk keeps `TopWF` (its neighbours are not free, the other chunks apart). -/
theorem topWF_split {l : Local} (hw : LocalWF C l) {d : Chunk} (hd : d ∈ l.av.chunks) (hdu : d.use.tagFree = true)
    {nb : Nat} (hnb : nb % C.align = 0) (hmin : C.minSize ≤ nb) (hrem : nb + C.minSize ≤ d.size)
    (hpos : 0 < nb) (hm0 : 0 < C.minSize) (u₂ : Use) :
    TopWF C (l.av.tiles.split d.addr nb .client u₂) := by
  have ht := hw.arena.tiles
  obtain ⟨R₁, s, pre, post, R₂, hr, ha⟩ := runs_of_chunk ht hd
  have hcoal0 := ht.runs_coal _ (by rw [hr]; exact List.mem_append_right _ (List.mem_cons_self ..))
  simp only at hcoal0
  rw [coalescedB_mid] at hcoal0
  obtain ⟨-, -, hnb3⟩ := hcoal0
  obtain ⟨-, hnext⟩ := hnb3 hdu
  have hlast : R₂ = [] → post ≠ [] := by
    intro h0 hp; subst h0; subst hp
    have := ht.runs_last (R₁ := R₁) (s := s) hr (d.size, d.use) (by rw [getLast?_append_cons]; rfl)
    simp only at this; rw [hdu] at this; cases this
  have hap : ∀ c ∈ l.av.tiles.heapChunks, c.addr ≠ s + runLen pre →
      c.addr + c.size ≤ s + runLen pre ∨ s + runLen pre + d.size ≤ c.addr := by
    intro c hc hne
    rw [ha] at hne ⊢
    exact Apart.ne_apart hw.apart (mem_spans_of_chunk hc) (mem_spans_of_chunk hd)
      (fun h => hne (congrArg Prod.fst h))
  have := ht.splitFree hr hnext hlast (s₁ := nb) (u₁ := .client) (u₂ := u₂) rfl hnb hmin (by omega)
    (by omega) hpos hap
  rw [ha] at this
  exact this

/-- **Lending the first `nb` bytes of a free chunk out**, the remainder at the head of the
unsorted bin (`takeFit` with a remainder, the `last_remainder` split): given the bins without the
chunk and the new unsorted list, an `MBody`. -/
theorem splitLend (hC : C.Ok) {n : Nat} {l : Local} (hw : LocalWF C l) (hs : LocalSp C l)
    {d : Chunk} (hd : d ∈ l.av.chunks) (hdu : d.use.tagFree = true)
    {nb : Nat} (hnb : nb % C.align = 0) (hmin : C.minSize ≤ nb) (hrem : nb + C.minSize ≤ d.size)
    (hn : n + C.sizeSz ≤ nb) (bs : BinsSt)
    (hbins : BinsWF C bs (Chunk.view Use.isSorted (l.av.chunks.map (Chunk.relabelAt d.addr .internal)))
      l.av.tiles.sizeAt)
    (us : UnsortedSt) (hus : us.list = (d.addr + nb) :: l.av.unsorted.list.erase d.addr)
    (hlr : us.lastRem < 2 ^ 64) :
    MBody C n l (d.addr + C.hdr) { l with av := { l.av with
      tiles := l.av.tiles.split d.addr nb .client (.bin 1), bins := bs, unsorted := us } } := by
  have h32 := hC.minSize
  have ht := hw.arena.tiles
  have hn' := ht.nodup
  have hpos : 0 < nb := by omega
  have hts := topWF_split hw hd hdu hnb hmin hrem hpos (by omega) (.bin 1)
  obtain ⟨A, B, hH, hH', hAB⟩ := split_chunks ht hd (nb := nb) (by omega) .client (.bin 1)
  have hnc := not_client_of_free hdu
  have hnf := not_fast_of_free hdu
  -- membership
  have hmemA : ∀ c ∈ A, c ∈ l.av.chunks := fun c hc => by
    show c ∈ l.av.tiles.heapChunks; rw [hH]; exact List.mem_append_left _ hc
  have hmemB : ∀ c ∈ B, c ∈ l.av.chunks := fun c hc => by
    show c ∈ l.av.tiles.heapChunks; rw [hH]; simp [hc]
  have hmemA' : ∀ c ∈ A, c ∈ (l.av.tiles.split d.addr nb .client (.bin 1)).heapChunks := fun c hc => by
    rw [hH']; exact List.mem_append_left _ hc
  have hmemB' : ∀ c ∈ B, c ∈ (l.av.tiles.split d.addr nb .client (.bin 1)).heapChunks := fun c hc => by
    rw [hH']; simp [hc]
  have hAne : ∀ c ∈ A, c.addr ≠ d.addr := fun c hc => hAB c (List.mem_append_left _ hc)
  have hBne : ∀ c ∈ B, c.addr ≠ d.addr := fun c hc => hAB c (List.mem_append_right _ hc)
  -- the old chunk at `a + nb`: none
  have hnew : ∀ c ∈ l.av.chunks, c.addr ≠ d.addr + nb := by
    intro c hc hca
    by_cases hcd : c.addr = d.addr
    · omega
    · have := Apart.ne_apart hw.apart (mem_spans_of_chunk hc) (mem_spans_of_chunk hd)
        (fun h => hcd (congrArg Prod.fst h))
      simp only at this; omega
  have hrel : l.av.chunks.map (Chunk.relabelAt d.addr .internal) = A ++ { d with use := .internal } :: B := by
    show l.av.tiles.heapChunks.map _ = _
    rw [hH, List.map_append, List.map_cons, Algo.map_relabelAt_of_not_mem hAne,
      Algo.map_relabelAt_of_not_mem hBne, Chunk.relabelAt_of_eq rfl]
  have hmemN : ∀ c, c ∈ (l.av.tiles.split d.addr nb .client (.bin 1)).heapChunks ↔
      c ∈ A ∨ c = ⟨d.addr, nb, .client⟩ ∨ c = ⟨d.addr + nb, d.size - nb, .bin 1⟩ ∨ c ∈ B := by
    intro c; rw [hH']; simp
  have hmemO : ∀ c, c ∈ l.av.chunks ↔ c ∈ A ∨ c = d ∨ c ∈ B := by
    intro c; show c ∈ l.av.tiles.heapChunks ↔ _; rw [hH]; simp
  -- the views
  have hfv : Chunk.view Use.isFast (l.av.tiles.split d.addr nb .client (.bin 1)).heapChunks = l.av.fastView := by
    unfold ArenaSt.fastView ArenaSt.chunks
    rw [hH', hH]
    simp [Chunk.view, List.filter_append, hnf, show Use.isFast .client = false from rfl,
      show Use.isFast (.bin 1) = false from rfl]
  have hsv : Chunk.view Use.isSorted (l.av.tiles.split d.addr nb .client (.bin 1)).heapChunks =
      Chunk.view Use.isSorted (l.av.chunks.map (Chunk.relabelAt d.addr .internal)) := by
    rw [hrel, hH']; simp [Chunk.view, List.filter_append, Use.isSorted]
  have hbins' : BinsWF C bs (Chunk.view Use.isSorted (l.av.tiles.split d.addr nb .client (.bin 1)).heapChunks)
      (l.av.tiles.split d.addr nb .client (.bin 1)).sizeAt := by
    rw [hsv]
    refine hbins.congr_sz fun c hc => ?_
    have hc1 := (List.mem_filter.mp hc).1
    have hc2 := (List.mem_filter.mp hc).2
    rw [hrel] at hc1
    have hcAB : c ∈ A ∨ c ∈ B := by
      simp only [List.mem_append, List.mem_cons] at hc1
      rcases hc1 with h | rfl | h
      · exact .inl h
      · simp [Use.isSorted] at hc2
      · exact .inr h
    have h1 : c ∈ (l.av.tiles.split d.addr nb .client (.bin 1)).heapChunks := (hmemN c).mpr (by
      rcases hcAB with h | h
      · exact .inl h
      · exact .inr (.inr (.inr h)))
    have h2 : c ∈ l.av.tiles.heapChunks := (hmemO c).mpr (by
      rcases hcAB with h | h
      · exact .inl h
      · exact .inr (.inr h))
    rw [TopSt.sizeAt_of_mem hts.nodup h1, TopSt.sizeAt_of_mem hn' h2]
  have huv : UnsortedWF C us (Chunk.view Use.isUnsorted (l.av.tiles.split d.addr nb .client (.bin 1)).heapChunks) := by
    have hold := hw.arena.unsorted
    refine ⟨fun x => ?_, ?_, fun c hc => hts.minSize_all c (List.mem_filter.mp hc).1, hlr⟩
    · rw [hus, List.mem_cons, hold.nodup.mem_erase_iff]
      constructor
      · rintro (rfl | ⟨hx, hxl⟩)
        · exact ⟨⟨d.addr + nb, d.size - nb, .bin 1⟩,
            List.mem_filter.mpr ⟨(hmemN _).mpr (.inr (.inr (.inl rfl))), rfl⟩, rfl, rfl⟩
        · obtain ⟨c, hc, hca, hcu⟩ := (hold.exact x).mp hxl
          have hc1 := (hmemO c).mp (List.mem_filter.mp hc).1
          refine ⟨c, List.mem_filter.mpr ⟨(hmemN c).mpr ?_, (List.mem_filter.mp hc).2⟩, hca, hcu⟩
          rcases hc1 with h | rfl | h
          · exact .inl h
          · exact absurd hca.symm hx
          · exact .inr (.inr (.inr h))
      · rintro ⟨c, hc, hca, hcu⟩
        have hc1 := (hmemN c).mp (List.mem_filter.mp hc).1
        have hold' : c ∈ l.av.chunks → x ∈ l.av.unsorted.list := fun h =>
          (hold.exact x).mpr ⟨c, List.mem_filter.mpr ⟨h, by rw [hcu]; rfl⟩, hca, hcu⟩
        rcases hc1 with h | rfl | rfl | h
        · exact .inr ⟨by rw [← hca]; exact hAne c h, hold' ((hmemO c).mpr (.inl h))⟩
        · cases hcu
        · exact .inl hca.symm
        · exact .inr ⟨by rw [← hca]; exact hBne c h, hold' ((hmemO c).mpr (.inr (.inr h)))⟩
    · rw [hus]
      refine List.nodup_cons.mpr ⟨fun hm => ?_, hold.nodup.erase _⟩
      obtain ⟨c, hc, hca, -⟩ := (hold.exact _).mp (List.mem_of_mem_erase hm)
      exact hnew c (List.mem_filter.mp hc).1 hca
  have hav : ArenaWF C { l.av with tiles := l.av.tiles.split d.addr nb .client (.bin 1), bins := bs, unsorted := us } :=
    { tiles := hts
      fast := by
        show FastWF C l.av.fast (Chunk.view Use.isFast (l.av.tiles.split d.addr nb .client (.bin 1)).heapChunks)
        rw [hfv]; exact hw.arena.fast
      bins := hbins'
      unsorted := huv
      internal := fun c hc _ => hts.minSize_all c hc }
  have hw' : LocalWF C { l with av := { l.av with tiles := l.av.tiles.split d.addr nb .client (.bin 1), bins := bs, unsorted := us } } := by
    refine hw.withAv' _ hav rfl rfl rfl (by simp [TopSt.split]) ?_
    have hap0 := hw.apart
    unfold Local.spans ArenaSt.spans TopSt.spans at hap0 ⊢
    rw [hH']
    rw [hH] at hap0
    have e1 : (l.av.tiles.split d.addr nb .client (.bin 1)).start = l.av.tiles.start := rfl
    have e2 : (l.av.tiles.split d.addr nb .client (.bin 1)).top = l.av.tiles.top := rfl
    have e3 : (l.av.tiles.split d.addr nb .client (.bin 1)).topSize = l.av.tiles.topSize := rfl
    have e4 : ({ l.av with tiles := l.av.tiles.split d.addr nb .client (.bin 1), bins := bs, unsorted := us } : ArenaSt).heapSpans = l.av.heapSpans := rfl
    simp only [e1, e2, e3, e4]
    have := Apart.split_mid (L := A.map (fun c => (c.addr, c.size)))
      (X := B.map (fun c => (c.addr, c.size)) ++ (if l.av.tiles.start = 0 then [] else
        [(l.av.tiles.top, l.av.tiles.topSize)]) ++ l.av.heapSpans ++
          l.shared.mm.chunks.map (fun c => (c.addr, c.size)))
      (r := (d.addr, d.size)) (by simpa [List.append_assoc] using hap0) hpos (by omega)
    simpa [List.append_assoc] using this
  have hout : (({ l.av with tiles := l.av.tiles.split d.addr nb .client (.bin 1), bins := bs, unsorted := us } : ArenaSt).out C).Perm ((d.addr + C.hdr, nb - C.sizeSz) :: l.av.out C) := by
    unfold ArenaSt.out ArenaSt.chunks
    simp only
    rw [hH', hH]
    simp only [Chunk.view, List.filter_append, List.filter_cons, hnc, decide_false, decide_true,
      ite_true, Bool.false_eq_true, ite_false, List.map_append, List.map_cons, usable]
    exact List.perm_middle
  have hin : SpansIn ({ l.av with tiles := l.av.tiles.split d.addr nb .client (.bin 1), bins := bs, unsorted := us } : ArenaSt).spans l.av.spans := by
    show SpansIn ((l.av.tiles.split d.addr nb .client (.bin 1)).spans ++ l.av.heapSpans)
      (l.av.tiles.spans ++ l.av.heapSpans)
    refine SpansIn.append_right ?_ _
    intro r hr
    unfold TopSt.spans at hr ⊢
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
      have hold : ∀ c' ∈ l.av.tiles.heapChunks, ∃ s ∈ l.av.tiles.heapChunks.map (fun c => (c.addr, c.size)) ++
          (if l.av.tiles.start = 0 then [] else [(l.av.tiles.top, l.av.tiles.topSize)]),
          s.1 ≤ c'.addr ∧ c'.addr + c'.size ≤ s.1 + s.2 :=
        fun c' hc' => ⟨(c'.addr, c'.size), List.mem_append_left _ (List.mem_map_of_mem hc'), Nat.le_refl _, Nat.le_refl _⟩
      rcases (hmemN c).mp hc with h | rfl | rfl | h
      · exact hold c ((hmemO c).mpr (.inl h))
      · obtain ⟨s', hs', h1, h2⟩ := hold d hd; exact ⟨s', hs', h1, (by simp only at h1 h2 ⊢; omega)⟩
      · obtain ⟨s', hs', h1, h2⟩ := hold d hd; exact ⟨s', hs', (by simp only at h1 h2 ⊢; omega), (by simp only at h1 h2 ⊢; omega)⟩
      · exact hold c ((hmemO c).mpr (.inr (.inr h)))
    · simp only [TopSt.split] at hr
      exact ⟨r, List.mem_append_right _ hr, Nat.le_refl _, Nat.le_refl _⟩
  have hcl : ∀ c ∈ l.av.chunks, c.use = .client →
      c ∈ ({ l.av with tiles := l.av.tiles.split d.addr nb .client (.bin 1), bins := bs, unsorted := us } : ArenaSt).chunks := by
    intro c hc hcu
    show c ∈ (l.av.tiles.split d.addr nb .client (.bin 1)).heapChunks
    rcases (hmemO c).mp hc with h | rfl | h
    · exact (hmemN c).mpr (.inl h)
    · exact absurd hcu hnc
    · exact (hmemN c).mpr (.inr (.inr (.inr h)))
  exact MBody.of_arena hC hw' hs hin rfl hcl (d := ⟨d.addr, nb, .client⟩)
    ((hmemN _).mpr (.inr (.inl rfl)))
    (fun c hc hca hcu => by
      have := chunk_unique hn' hc hd hca; subst this; exact hnc hcu) hout hn

end Algo

end Silmaril.Libc.Ptmalloc
