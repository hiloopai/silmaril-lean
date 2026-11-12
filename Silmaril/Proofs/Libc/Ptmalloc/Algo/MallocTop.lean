module

public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocBody
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.WorldOps

/-!
# ptmalloc algorithm: `use_top`

`Algo.useTop_body`: carving `nb` bytes off a top chunk of at least `nb + MINSIZE` bytes
(`_int_malloc`'s `use_top`, `sysmalloc`'s final carve) is a body (`MBody`): the tiling gains the
new client chunk at the old top's address, the live set gains its payload, which is apart from
every live payload because the top chunk is apart from every span (`LocalWF.apart`) and no tcache
entry lies at its address (`LocalSp.entries`); the new spans lie inside the old top's (`Frame`).
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

variable {C : Config}

/-! ## Spans inside old spans -/

/-- `r` lies inside `s`. -/
def Inside (r s : Nat × Nat) : Prop := s.1 ≤ r.1 ∧ r.1 + r.2 ≤ s.1 + s.2

theorem away_of_inside {rs : List (Nat × Nat)} {x : Nat × Nat} (ha : Away rs x) {r : Nat × Nat}
    {s : Nat × Nat} (hs : s ∈ rs) (hi : Inside r s) : x.1 + x.2 ≤ r.1 ∨ r.1 + r.2 ≤ x.1 := by
  have := ha s hs; obtain ⟨h1, h2⟩ := hi; omega

theorem covers_of_inside {k : KernelSt} {r s : Nat × Nat} (hc : k.Covers s) (hi : Inside r s) :
    k.Covers r := fun x h1 h2 => hc x (by have := hi.1; omega) (by have := hi.2; omega)

/-- **A body whose new spans lie inside old ones**, with the kernel kept: the spatial clauses of
`Frame`. -/
theorem spatial_of_inside {l l' : Local} (hk : l'.kernel = l.kernel)
    (hsub : ∀ r ∈ l'.spans, ∃ s ∈ l.spans, Inside r s) :
    ∀ r, 0 < r.2 → l.kernel.Covers r → Away l.spans r → l'.kernel.Covers r ∧ Away l'.spans r := by
  intro r _ hc ha
  refine ⟨by rw [hk]; exact hc, fun x hx => ?_⟩
  obtain ⟨s, hs, hi⟩ := hsub x hx
  exact away_of_inside ha hs hi

theorem covered_of_inside {l l' : Local} (hk : l'.kernel = l.kernel) (hsp : LocalSp C l)
    (hsub : ∀ r ∈ l'.spans, ∃ s ∈ l.spans, Inside r s) : ∀ r ∈ l'.spans, l'.kernel.Covers r := by
  intro r hr
  obtain ⟨s, hs, hi⟩ := hsub r hr
  rw [hk]; exact covers_of_inside (hsp.covered s hs) hi

theorem inside_refl (r : Nat × Nat) : Inside r r := ⟨Nat.le_refl _, Nat.le_refl _⟩

/-! ## The top chunk apart from the rest -/

theorem spans_eq_top {l : Local} (hs : l.av.tiles.start ≠ 0) :
    l.spans = (l.av.tiles.heapChunks.map (fun c => (c.addr, c.size)) ++ [(l.av.tiles.top, l.av.tiles.topSize)]) ++
      (l.av.heapSpans ++ l.shared.mm.chunks.map (fun c => (c.addr, c.size))) := by
  rw [Local.spans_eq]; unfold TopSt.spans; rw [ite_eq_right_iff.mpr (fun h => absurd h hs)]

theorem top_apart_chunk {l : Local} (hw : LocalWF C l) (hs : l.av.tiles.start ≠ 0) {c : Chunk}
    (hc : c ∈ l.av.tiles.heapChunks) :
    c.addr + c.size ≤ l.av.tiles.top ∨ l.av.tiles.top + l.av.tiles.topSize ≤ c.addr := by
  have h := hw.apart.1
  rw [spans_eq_top hs, List.pairwise_append, List.pairwise_append] at h
  exact h.1.2.2 _ (List.mem_map_of_mem hc) (l.av.tiles.top, l.av.tiles.topSize) (List.mem_singleton_self _)

theorem top_apart_mm {l : Local} (hw : LocalWF C l) (hs : l.av.tiles.start ≠ 0) {c : Chunk}
    (hc : c ∈ l.shared.mm.chunks) :
    l.av.tiles.top + l.av.tiles.topSize ≤ c.addr ∨ c.addr + c.size ≤ l.av.tiles.top := by
  have h := hw.apart.1
  rw [spans_eq_top hs, List.pairwise_append] at h
  exact h.2.2 (l.av.tiles.top, l.av.tiles.topSize) (List.mem_append_right _ (List.mem_singleton_self _)) _
    (List.mem_append_right _ (List.mem_map_of_mem hc))

theorem top_pos {l : Local} (hw : LocalWF C l) (hs : l.av.tiles.start ≠ 0) : 0 < l.av.tiles.topSize := by
  have := hw.apart.2 (l.av.tiles.top, l.av.tiles.topSize) (by rw [spans_eq_top hs]; simp)
  exact this

/-- No tcache entry is at the top chunk's address. -/
theorem top_not_entry (hC : C.Ok) {l : Local} (hw : LocalWF C l) (hsp : LocalSp C l)
    (hs : l.av.tiles.start ≠ 0) {tc : TcacheSt} (ht : l.thread.tcache = some tc) {i : Nat}
    {e : Nat × Nat} (he : e ∈ tc.bins i) : e.1 ≠ l.av.tiles.top := by
  intro heq
  have h0 := entry_pos hC hw ht he
  have hz := top_pos hw hs
  rcases hsp.entries tc ht i e he with ⟨c, hc, h1, h2, -⟩ | ⟨ha, -⟩
  · have := top_apart_chunk hw hs hc
    have := (hw.arena.tiles.sizes c hc).2
    have := hC.minSize
    omega
  · have := ha (l.av.tiles.top, l.av.tiles.topSize) (by rw [spans_eq_top hs]; simp)
    simp only at this; omega

/-! ## `use_top` -/

theorem heapChunks_useTop {ts : TopSt} (htop : ts.top = ts.start + runLen ts.chunks)
    (nb : Nat) (u : Use) :
    (ts.useTop nb u).heapChunks = ts.heapChunks ++ [⟨ts.top, nb, u⟩] := by
  unfold TopSt.heapChunks TopSt.useTop
  simp only
  rw [layout_append, htop]
  simp [layout]

theorem view_append_client (p : Use → Bool) (hp : p .client = false) (cs : List Chunk) (a nb : Nat) :
    Chunk.view p (cs ++ [⟨a, nb, .client⟩]) = Chunk.view p cs := by
  unfold Chunk.view; rw [List.filter_append]; simp [hp]

theorem topWF_useTop (hC : C.Ok) {ts : TopSt} (h : TopWF C ts) (hs : ts.start ≠ 0) {nb : Nat}
    (hnb : nb % C.align = 0) (hmin : C.minSize ≤ nb) (hz : nb + C.minSize ≤ ts.topSize)
    (hfresh : ts.top ∉ ts.heapChunks.map (·.addr)) :
    TopWF C (ts.useTop nb .client) := by
  have hc := heapChunks_useTop (h.topAt hs) nb .client
  have hA := hC.align; have hM := hC.minSize
  have htA := h.topAligned
  have htB := h.topBound hs
  have htop := h.topAt hs
  refine
    { sizes := ?_, aligned := ?_, nonNull := ?_, topAt := ?_, topAligned := ?_, topMin := ?_,
      coalesced := ?_, lastUsed := ?_, coalescedOld := h.coalescedOld, sysMem := ?_,
      sysMemBound := h.sysMemBound, noHeap := fun h0 => absurd h0 hs, nodup := ?_, bound := ?_,
      topBound := ?_ }
  · intro c hc'; rw [hc] at hc'
    rcases List.mem_append.mp hc' with hc' | hc'
    · exact h.sizes c hc'
    · simp at hc'; subst hc'; exact ⟨hnb, hmin⟩
  · intro c hc'; rw [hc] at hc'
    rcases List.mem_append.mp hc' with hc' | hc'
    · exact h.aligned c hc'
    · simp at hc'; subst hc'; exact htA.1
  · intro c hc'; rw [hc] at hc'
    rcases List.mem_append.mp hc' with hc' | hc'
    · exact h.nonNull c hc'
    · simp at hc'; subst hc'; simp only; omega
  · intro _; simp only [TopSt.useTop, List.map_append, List.sum_append]
    simp; omega
  · simp only [TopSt.useTop]; rw [hA] at htA hnb ⊢; omega
  · intro _; simp only [TopSt.useTop]; omega
  · show coalescedB (ts.chunks ++ [(nb, .client)]) = true
    rw [coalescedB_mid_used _ _ _ rfl]; exact ⟨h.coalesced, rfl⟩
  · intro c hc'; simp only [TopSt.useTop, List.getLast?_append, List.getLast?_singleton] at hc'
    simp at hc'; subst hc'; rfl
  · rw [hc]; simp only [TopSt.useTop, List.map_append, List.sum_append, List.map_cons,
      List.map_nil, List.sum_cons, List.sum_nil]
    have := h.sysMem; omega
  · rw [hc, List.map_append, List.nodup_append]
    refine ⟨h.nodup, by simp, ?_⟩
    intro a ha b hb; simp at hb; subst hb; intro hab; subst hab; exact hfresh ha
  · intro c hc'; rw [hc] at hc'
    rcases List.mem_append.mp hc' with hc' | hc'
    · exact h.bound c hc'
    · simp at hc'; subst hc'; simp only; omega
  · intro _; simp only [TopSt.useTop]; omega

/-- **`use_top`** is a body. -/
theorem useTop_body (hC : C.Ok) {l : Local} (hw : LocalWF C l) (hsp : LocalSp C l) {n nb : Nat}
    (hnb : C.checkedRequest2size n = some nb) (hs : l.av.tiles.start ≠ 0)
    (hz : nb + C.minSize ≤ l.av.tiles.topSize) :
    MBody C n l (l.av.tiles.top + C.hdr) (withTiles l (l.av.tiles.useTop nb .client)) := by
  have hT := hw.arena.tiles
  have hnbE : nb = C.request2size n := by
    unfold Config.checkedRequest2size at hnb; split at hnb <;> simp_all
  obtain ⟨hnbA, hnbM, hnbN⟩ := request2size_props hC n
  rw [← hnbE] at hnbA hnbM hnbN
  have hA := hC.align; have hM := hC.minSize; have hS := hC.sizeSz
  have hhdr : C.hdr = 16 := by unfold Config.hdr; omega
  have hc := heapChunks_useTop (hT.topAt hs) nb .client
  have hzp := top_pos hw hs
  have hfresh : l.av.tiles.top ∉ l.av.tiles.heapChunks.map (·.addr) := by
    intro hm
    obtain ⟨c, hc', hca⟩ := List.mem_map.mp hm
    have := top_apart_chunk hw hs hc'
    have := (hT.sizes c hc').2
    omega
  have hT' := topWF_useTop hC hT hs hnbA hnbM hz hfresh
  have hviews (p : Use → Bool) (hp : p .client = false) :
      Chunk.view p (l.av.tiles.useTop nb .client).heapChunks = Chunk.view p l.av.tiles.heapChunks := by
    rw [hc]; exact view_append_client p hp _ _ _
  have hA' := hw.arena.withTilesViews _ hT' (hviews _ rfl) (hviews _ rfl) (hviews _ rfl)
  -- the new spans
  have hsp' : (withTiles l (l.av.tiles.useTop nb .client)).spans =
      (l.av.tiles.heapChunks.map (fun c => (c.addr, c.size)) ++ (l.av.tiles.top, nb) ::
        (l.av.tiles.top + nb, l.av.tiles.topSize - nb) :: (l.av.heapSpans ++ l.shared.mm.chunks.map (fun c => (c.addr, c.size)))) := by
    rw [Local.spans_eq,
      show (withTiles l (l.av.tiles.useTop nb .client)).av.heapSpans = l.av.heapSpans from rfl]
    unfold TopSt.spans
    simp only [withTiles]
    rw [hc]
    simp [TopSt.useTop, hs]
  have hap : Apart (withTiles l (l.av.tiles.useTop nb .client)).spans := by
    rw [hsp']
    have h0 := hw.apart
    rw [spans_eq_top hs, List.append_assoc, List.singleton_append] at h0
    exact h0.split_mid (by omega) (by omega)
  have hwl : LocalWF C (withTiles l (l.av.tiles.useTop nb .client)) :=
    hw.withAv' _ hA' rfl (by simp only [TopSt.useTop]; omega) rfl Iff.rfl hap
  have hsub : ∀ r ∈ (withTiles l (l.av.tiles.useTop nb .client)).spans, ∃ s ∈ l.spans, Inside r s := by
    intro r hr
    rw [hsp'] at hr
    have hmem : (l.av.tiles.top, l.av.tiles.topSize) ∈ l.spans := by rw [spans_eq_top hs]; simp
    simp only [List.mem_append, List.mem_cons] at hr
    rcases hr with hr | rfl | rfl | hr
    · exact ⟨r, by rw [spans_eq_top hs]; simp [hr], inside_refl r⟩
    · exact ⟨_, hmem, ⟨Nat.le_refl _, by simp only; omega⟩⟩
    · exact ⟨_, hmem, ⟨by simp only; omega, by simp only; omega⟩⟩
    · exact ⟨r, by rw [spans_eq_top hs]; simp only [List.mem_append]; exact .inr hr, inside_refl r⟩
  -- the live set
  have hout : (withTiles l (l.av.tiles.useTop nb .client)).av.out C =
      l.av.out C ++ [(l.av.tiles.top + C.hdr, nb - C.sizeSz)] := by
    simp only [withTiles, ArenaSt.out, ArenaSt.chunks, Chunk.view, hc, List.filter_append,
      List.map_append]
    simp [usable]
  have hnp : (l.thread.parked C).contains (l.av.tiles.top + C.hdr, nb - C.sizeSz) = false := by
    cases htc : l.thread.tcache with
    | none => simp [ThreadSt.parked, htc]
    | some tc =>
      simp only [ThreadSt.parked, htc, Option.map_some, Option.getD_some, TcacheSt.payloads]
      rw [Bool.eq_false_iff]; intro hm
      simp only [List.contains_iff_mem, List.mem_map, List.mem_flatMap, List.mem_range] at hm
      obtain ⟨e, ⟨i, -, he⟩, heq⟩ := hm
      simp only [Prod.mk.injEq] at heq
      exact top_not_entry hC hw hsp hs htc he (by omega)
  have hlive : ((withTiles l (l.av.tiles.useTop nb .client)).live C).Perm
      ((l.av.tiles.top + C.hdr, nb - C.sizeSz) :: l.live C) := by
    unfold Local.live
    rw [hout, List.filter_append]
    simp only [withTiles]
    rw [List.filter_cons_of_pos (by rw [hnp]; rfl), List.filter_nil]
    simp only [List.append_assoc, List.singleton_append]
    exact List.perm_middle
  have hfar : ∀ q ∈ l.live C, q.1 + q.2 ≤ l.av.tiles.top + C.hdr ∨ l.av.tiles.top + C.hdr + (nb - C.sizeSz) ≤ q.1 := by
    intro q hq
    unfold Local.live at hq
    rcases List.mem_append.mp hq with hq | hq
    · have hq := (List.mem_filter.mp hq).1
      simp only [ArenaSt.out, ArenaSt.chunks, Chunk.view, List.mem_map, List.mem_filter] at hq
      obtain ⟨c, ⟨hc', -⟩, rfl⟩ := hq
      have := top_apart_chunk hw hs hc'
      have := (hT.sizes c hc').2
      simp only [usable, Bool.false_eq_true, ↓reduceIte]; omega
    · simp only [SharedSt.live, List.mem_map, List.mem_filter] at hq
      obtain ⟨c, ⟨hc', -⟩, rfl⟩ := hq
      have := top_apart_mm hw hs hc'
      have := (hw.mmSize c hc').1
      simp only [usable, ↓reduceIte]; omega
  refine ⟨⟨hwl, ⟨rfl, rfl, fun h => absurd h (by decide), fun h => absurd h (by decide),
      fun h => absurd h (by decide), fun h => absurd h (by decide)⟩,
      .inr ⟨by omega, by rw [hA] at hnbA ⊢; have := hT.topAligned.1; rw [hA] at this; omega,
        nb - C.sizeSz, by omega, hlive, hfar⟩⟩, ?_, fun tc _ _ ht he _ => ⟨tc, ht, he⟩, id⟩
  exact
    { avAddr := rfl
      isMain := rfl
      spatial := spatial_of_inside (l := l) rfl hsub
      covered := covered_of_inside (l := l) rfl hsp hsub
      brkStart := rfl
      nonMain := fun _ => ⟨rfl, rfl⟩
      acct := fun _ => Nat.le_refl _
      init := rfl
      arenas := ⟨rfl, rfl, rfl⟩
      arena := rfl
      heaps := id
      clients := fun c hc' _ _ => by
        show c ∈ (l.av.tiles.useTop nb .client).heapChunks
        rw [hc]; exact List.mem_append_left _ hc'
      fresh := fun tc' i e ht he => .inl ⟨tc', i, ht, he⟩ }

end Silmaril.Libc.Ptmalloc.Algo
