module

public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocTop

/-!
# ptmalloc algorithm: lending out a free chunk, and parking it in the tcache

`Algo.Take`: a step that lends out one free chunk `d` of the arena (relabels it `client`) and
changes nothing else the frame speaks of (the fastbin pop, a small-bin removal). Such a step is a
body for `d`'s payload (`Take.body`), and followed by `tcache_put` of `d` it is an `MStep`
(`Take.park`: a tcache refill step). `d` is at no tcache entry (`LocalSp.entries`: an entry is a
client chunk, or apart from the view), so its payload is neither parked nor live before.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

variable {C : Config}

/-- **One free chunk `d` lent out**: the arena's tiling relabels it `client`, the rest of the view
the frame speaks of is unchanged. -/
structure Take (C : Config) (l l₁ : Local) (d : Chunk) : Prop where
  wf : LocalWF C l₁
  avAddr : l₁.avAddr = l.avAddr
  isMain : l₁.isMain = l.isMain
  thread : l₁.thread = l.thread
  shared : l₁.shared = l.shared
  kernel : l₁.kernel = l.kernel
  mem : d ∈ l.av.chunks
  use : d.use ≠ .client
  tiles : l₁.av.tiles = l.av.tiles.relabel d.addr .client
  heaps : l₁.av.heaps = l.av.heaps
  reserve : l₁.av.reserve = l.av.reserve := by rfl

theorem view_relabel_client {d : Chunk} (hdu : d.use ≠ .client) :
    ∀ {cs : List Chunk}, (cs.map (·.addr)).Nodup → d ∈ cs →
      (Chunk.view (· = .client) (cs.map (Chunk.relabelAt d.addr .client))).Perm
        ({ d with use := .client } :: Chunk.view (· = .client) cs)
  | [], _, hd => by cases hd
  | c :: cs, hn, hd => by
    have hn' : (cs.map (·.addr)).Nodup := (List.nodup_cons.mp hn).2
    by_cases hc : c.addr = d.addr
    · have hcd : c = d := by
        rcases List.mem_cons.mp hd with h | h
        · exact h.symm
        · exact absurd (List.mem_map.mpr ⟨d, h, hc.symm⟩) (List.nodup_cons.mp hn).1
      subst hcd
      have hrest : cs.map (Chunk.relabelAt c.addr .client) = cs :=
        map_relabelAt_of_not_mem fun x hx hxa =>
          (List.nodup_cons.mp hn).1 (List.mem_map.mpr ⟨x, hx, hxa⟩)
      simp only [List.map_cons, Chunk.relabelAt_of_eq rfl, hrest, Chunk.view, List.filter_cons,
        decide_true, ↓reduceIte, hdu, decide_false, Bool.false_eq_true]
      exact List.Perm.refl _
    · have hd' : d ∈ cs := by
        rcases List.mem_cons.mp hd with h | h
        · exact absurd (h ▸ rfl) hc
        · exact h
      have ih := view_relabel_client hdu hn' hd'
      simp only [List.map_cons, Chunk.relabelAt_of_ne hc, Chunk.view, List.filter_cons] at ih ⊢
      split
      · exact (List.Perm.cons _ ih).trans (List.Perm.swap _ _ _)
      · exact ih

namespace Take

variable {l l₁ : Local} {d : Chunk}

theorem chunks (T : Take C l l₁ d) :
    l₁.av.chunks = l.av.chunks.map (Chunk.relabelAt d.addr .client) := by
  unfold ArenaSt.chunks; rw [T.tiles, TopSt.heapChunks_relabel]

theorem spans (T : Take C l l₁ d) : l₁.spans = l.spans := by
  unfold Local.spans ArenaSt.spans ArenaSt.heapSpans
  rw [T.tiles, TopSt.spans_relabel, T.shared, T.heaps, T.reserve]

theorem out (T : Take C l l₁ d) (hw : LocalWF C l) :
    (l₁.av.out C).Perm ((d.addr + C.hdr, usable C d false) :: l.av.out C) := by
  unfold ArenaSt.out
  rw [T.chunks]
  exact (view_relabel_client T.use hw.arena.tiles.nodup T.mem).map _

theorem mem_client (T : Take C l l₁ d) : (⟨d.addr, d.size, .client⟩ : Chunk) ∈ l₁.av.chunks := by
  rw [T.chunks]
  exact List.mem_map.mpr ⟨d, T.mem, Chunk.relabelAt_of_eq rfl⟩

theorem keep_client (T : Take C l l₁ d) (hw : LocalWF C l) {c : Chunk} (hc : c ∈ l.av.chunks)
    (hcu : c.use = .client) : c ∈ l₁.av.chunks := by
  rw [T.chunks]
  have hne : c.addr ≠ d.addr := fun h => by
    have := chunk_unique hw.arena.tiles.nodup hc T.mem h
    subst this; exact T.use hcu
  exact List.mem_map.mpr ⟨c, hc, Chunk.relabelAt_of_ne hne⟩

theorem not_entry (hC : C.Ok) (T : Take C l l₁ d) (hw : LocalWF C l) (hsp : LocalSp C l)
    {tc : TcacheSt} (ht : l.thread.tcache = some tc) {j : Nat} {e : Nat × Nat} (he : e ∈ tc.bins j) :
    e.1 ≠ d.addr := by
  intro heq
  have h0 := entry_pos hC hw ht he
  have hds := (hw.arena.tiles.sizes d T.mem).2
  have hM := hC.minSize
  rcases hsp.entries tc ht j e he with ⟨c, hc, h1, -, h3⟩ | ⟨ha, -⟩
  · have := chunk_unique hw.arena.tiles.nodup hc T.mem (h1.trans heq)
    subst this; exact T.use h3
  · have := ha _ (mem_spans_of_chunk T.mem); omega

theorem not_parked (hC : C.Ok) (T : Take C l l₁ d) (hw : LocalWF C l) (hsp : LocalSp C l) :
    (l.thread.parked C).contains (d.addr + C.hdr, usable C d false) = false := by
  cases htc : l.thread.tcache with
  | none => simp [ThreadSt.parked, htc]
  | some tc =>
    simp only [ThreadSt.parked, htc, Option.map_some, Option.getD_some, TcacheSt.payloads]
    rw [Bool.eq_false_iff]; intro hm
    simp only [List.contains_iff_mem, List.mem_map, List.mem_flatMap, List.mem_range] at hm
    obtain ⟨e, ⟨i, -, he⟩, heq⟩ := hm
    simp only [Prod.mk.injEq] at heq
    exact T.not_entry hC hw hsp htc he (by omega)

theorem live (hC : C.Ok) (T : Take C l l₁ d) (hw : LocalWF C l) (hsp : LocalSp C l) :
    (l₁.live C).Perm ((d.addr + C.hdr, usable C d false) :: l.live C) := by
  unfold Local.live
  rw [T.thread, T.shared]
  have h := (T.out hw).filter (fun pu => !(l.thread.parked C).contains pu)
  rw [List.filter_cons_of_pos (by rw [T.not_parked hC hw hsp]; rfl)] at h
  exact (List.Perm.append_right _ h)

theorem frame (T : Take C l l₁ d) (hw : LocalWF C l) (hsp : LocalSp C l) : Frame C l l₁ [] where
  avAddr := T.avAddr
  isMain := T.isMain
  spatial r _ hc ha := by rw [T.kernel, T.spans]; exact ⟨hc, ha⟩
  covered r hr := by rw [T.kernel]; rw [T.spans] at hr; exact hsp.covered r hr
  brkStart := by rw [T.kernel]
  nonMain _ := by rw [T.kernel, T.shared]; exact ⟨rfl, rfl⟩
  acct _ := by rw [T.kernel, T.shared]; exact Nat.le_refl _
  init := by rw [T.shared]
  arenas := by rw [T.shared]; exact ⟨rfl, rfl, rfl⟩
  arena := by rw [T.thread]
  heaps h := by rw [T.heaps]; exact h
  clients c hc hu _ := T.keep_client hw hc hu
  fresh tc' i e ht he := by
    rw [T.thread] at ht
    exact .inl ⟨tc', i, ht, he⟩

/-- **Lending out a free chunk** is a body for its payload. -/
theorem body (hC : C.Ok) (T : Take C l l₁ d) (hw : LocalWF C l) (hsp : LocalSp C l) {n : Nat}
    (hn : n + C.sizeSz ≤ d.size) : MBody C n l (d.addr + C.hdr) l₁ := by
  have hlive := T.live hC hw hsp
  have hap := (llive_apart hC T.wf)
  have hpw := (hlive.pairwise_iff (fun {a b} h => h.symm)).mp hap.1
  have hx := hap.2 _ (hlive.symm.subset (List.mem_cons_self ..))
  have hal := hw.arena.tiles.aligned d T.mem
  have hA := hC.align; have hS := hC.sizeSz
  have hhdr : C.hdr = 16 := by unfold Config.hdr; omega
  refine ⟨⟨T.wf, within_of_frame (T.frame hw hsp),
      .inr ⟨hx.1, by rw [hhdr, hA]; rw [hA] at hal; omega, usable C d false,
        by simp only [usable, Bool.false_eq_true, ↓reduceIte]; omega, hlive,
        fun q hq => ((List.pairwise_cons.mp hpw).1 q hq).symm⟩⟩,
    T.frame hw hsp, fun tc _ _ ht he _ => ⟨tc, by rw [T.thread]; exact ht, he⟩,
    fun h => by rw [T.thread]; exact h⟩

/-- **Lending out a free chunk and parking it** in tcache bin `t` (a tcache refill step) is an
`MStep`. -/
theorem park (hC : C.Ok) (T : Take C l l₁ d) (hw : LocalWF C l) (hsp : LocalSp C l)
    {tc : TcacheSt} (ht : l₁.thread.tcache = some tc) {t : Nat} (hi : t < C.tcacheBins)
    (hidx : C.tidx d.size = t) (hroom : (tc.bins t).length < C.tcacheCount) :
    MStep C l (tcPut l₁ (d.addr, d.size) t) := by
  have ht0 : l.thread.tcache = some tc := by rw [← T.thread]; exact ht
  have hput : tcPut l₁ (d.addr, d.size) t =
      { l₁ with thread := { l₁.thread with tcache := some (tc.put (d.addr, d.size) t) } } := by
    simp [tcPut, Local.tcachePut, ht]
  have hsz := hw.arena.tiles.sizes d T.mem
  have hnn := hw.arena.tiles.nonNull d T.mem
  have hal := hw.arena.tiles.aligned d T.mem
  have hnot : (d.addr, d.size) ∉ tc.bins t := fun hm =>
    T.not_entry hC hw hsp ht0 hm rfl
  obtain ⟨hwl, -⟩ := leafTcachePut C l₁ _ (d.addr, d.size) t hC T.wf hi hidx hsz.1 hsz.2 hnn hal
    (fun tc' ht' => by rw [ht] at ht'; cases ht'; exact ⟨hnot, hroom⟩)
    (by rw [Local.tcachePut, ht]; rfl)
  have hl1 := T.live hC hw hsp
  have hout : (d.addr + C.hdr, d.size - C.sizeSz) ∈ l₁.av.out C :=
    (T.out hw).symm.subset (List.mem_cons_self ..)
  have hnp : (d.addr + C.hdr, d.size - C.sizeSz) ∉ l₁.thread.parked C := by
    rw [T.thread]; intro hm
    have := T.not_parked hC hw hsp
    simp only [usable, Bool.false_eq_true, ↓reduceIte] at this
    rw [List.contains_iff_mem.mpr hm] at this; cases this
  have hlive : ((tcPut l₁ (d.addr, d.size) t).live C).Perm (l.live C) := by
    refine (live_tcPut T.wf ht hi hout hnp).trans ?_
    have := hl1.erase (d.addr + C.hdr, d.size - C.sizeSz)
    simp only [usable, Bool.false_eq_true, ↓reduceIte, List.erase_cons_head] at this
    exact this
  rw [hput] at hlive ⊢
  refine ⟨hwl, hlive, ?_, fun tc₀ i e ht₀ he _ => ?_, fun h => by rw [ht0] at h; cases h⟩
  · exact
      { avAddr := T.avAddr
        isMain := T.isMain
        spatial := fun r _ hc ha => by
          show l₁.kernel.Covers r ∧ Away l₁.spans r
          rw [T.kernel, T.spans]; exact ⟨hc, ha⟩
        covered := fun r hr => by
          show l₁.kernel.Covers r
          have hr' : r ∈ l₁.spans := hr
          rw [T.kernel]; rw [T.spans] at hr'; exact hsp.covered r hr'
        brkStart := by show l₁.kernel.brkStart = _; rw [T.kernel]
        nonMain := fun _ => by
          show l₁.kernel.brk = _ ∧ l₁.shared.mm.mp.sbrkBase = _
          rw [T.kernel, T.shared]; exact ⟨rfl, rfl⟩
        acct := fun _ => by
          show _ + l₁.shared.mm.mp.mmappedMem ≤ l₁.kernel.total + _
          rw [T.kernel, T.shared]; exact Nat.le_refl _
        init := by show l₁.shared.init = _; rw [T.shared]
        arenas := by
          show l₁.shared.arenas = _ ∧ l₁.shared.freeList = _ ∧ l₁.shared.narenas = _
          rw [T.shared]; exact ⟨rfl, rfl, rfl⟩
        arena := by show l₁.thread.arena = _; rw [T.thread]
        heaps := fun h => by show l₁.av.heaps ≠ []; rw [T.heaps]; exact h
        clients := fun c hc hu _ => T.keep_client hw hc hu
        fresh := fun tc' i e ht' he => by
          simp only [Option.some.injEq] at ht'
          subst ht'
          simp only [TcacheSt.put] at he
          split at he
          · rename_i hit
            rcases List.mem_cons.mp he with rfl | he
            · exact .inr ⟨⟨_, T.mem_client, rfl, rfl, rfl⟩, .inr fun c hc hca hcu => by
                have := chunk_unique hw.arena.tiles.nodup hc T.mem hca
                subst this; exact T.use hcu⟩
            · exact .inl ⟨tc, i, ht0, hit ▸ he⟩
          · exact .inl ⟨tc, i, ht0, he⟩ }
  · rw [ht0] at ht₀; cases ht₀
    refine ⟨tc.put (d.addr, d.size) t, rfl, ?_⟩
    simp only [TcacheSt.put]
    split
    · rename_i hit; subst hit; exact List.mem_cons_of_mem _ he
    · exact he

end Take

end Silmaril.Libc.Ptmalloc.Algo
