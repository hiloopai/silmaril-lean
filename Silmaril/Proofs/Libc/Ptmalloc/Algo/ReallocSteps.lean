module

public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocFit
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocTop
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.FreeBody

/-!
# ptmalloc algorithm: the steps of `_int_realloc`

* the `Frame` algebra with freed payloads (`Frame.mono`, `Frame.comp`, `Frame.drop`,
  `LocalSp.of_frame'`, `KeptAway.trans'`): `_int_realloc` gives back its old payload, and its
  pieces (`_int_malloc`, the split, `_int_free` of the remainder) compose;
* `TopWF.splitUsed`: splitting a chunk into two used chunks keeps `TopWF`;
* `Algo.splitClient`: the split of a lent-out chunk into two lent-out chunks, as a view step;
* `Algo.reallocSplit_spec`: `_int_realloc`'s *split below* (the remainder of at least `MINSIZE`
  cut off and `_int_free`d).
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc

namespace TopWF

variable {C : Config} {ts : TopSt}

/-- **Splitting a chunk into two used chunks** (its other chunks apart from it) keeps `TopWF`. -/
theorem splitUsed (h : TopWF C ts) {R₁ R₂ : List (Nat × List (Nat × Use))} {s : Nat}
    {pre post : List (Nat × Use)} {sz : Nat} {v : Use}
    (hr : ts.runs = R₁ ++ (s, pre ++ (sz, v) :: post) :: R₂)
    {s₁ : Nat} {u₁ u₂ : Use} (hu₁ : u₁.tagFree = false) (hu₂ : u₂.tagFree = false)
    (hs₁ : s₁ % C.align = 0) (hmin₁ : C.minSize ≤ s₁) (hmin₂ : C.minSize ≤ sz - s₁) (hlt : s₁ < sz)
    (hpos : 0 < s₁) (hap : ∀ c ∈ ts.heapChunks, c.addr ≠ s + runLen pre →
      c.addr + c.size ≤ s + runLen pre ∨ s + runLen pre + sz ≤ c.addr) :
    TopWF C (ts.split (s + runLen pre) s₁ u₁ u₂) := by
  have hn := h.nodup
  have hr' := TopSt.runs_split' (x := (sz, v)) s₁ u₁ u₂ hr rfl hn
  have hd := TopSt.mem_of_runs hr
  simp only at hd hr'
  have hr1 : ts.runs = R₁ ++ (s, pre ++ [(sz, v)] ++ post) :: R₂ := by rw [hr]; simp
  have hr1' : (ts.split (s + runLen pre) s₁ u₁ u₂).runs =
      R₁ ++ (s, pre ++ [(s₁, u₁), (sz - s₁, u₂)] ++ post) :: R₂ := by rw [hr']; simp
  have hcoal0 := h.runs_coal _ (by rw [hr]; exact List.mem_append_right _ (List.mem_cons_self ..))
  simp only at hcoal0
  rw [coalescedB_mid] at hcoal0
  obtain ⟨hc1, hc2, -⟩ := hcoal0
  have hszd := h.sizes _ hd
  simp only at hszd
  have hal0 := h.aligned _ hd
  have hnn0 := h.nonNull _ hd
  simp only at hal0 hnn0
  refine h.replaceN hr1 hr1' (by simp) (by simp [runLen]; omega) ?_ ?_ ?_ ?_ ?_ rfl rfl rfl
  · intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact ⟨hs₁, hmin₁⟩
    · refine ⟨?_, hmin₂⟩
      simp only
      exact Nat.sub_mod_eq_zero_of_mod_eq (by rw [hszd.1, hs₁])
  · intro c hc
    simp only [layout, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨hal0, hnn0⟩
    · simp only
      exact ⟨by rw [Nat.add_mod, hal0, hs₁]; rfl, by omega⟩
  · have hH := TopSt.heapChunks_of_runs hr1
    have hH' := TopSt.heapChunks_of_runs hr1'
    have hrl : runLen [(s₁, u₁), (sz - s₁, u₂)] = runLen [(sz, v)] := by simp [runLen]; omega
    rw [hrl] at hH'
    rw [hH']
    have hn' := hn
    rw [hH] at hn'
    simp only [layout, List.map_append, List.map_cons, List.append_assoc,
      List.cons_append, List.nil_append, runLen_cons, runLen_nil, Nat.add_zero] at hn' ⊢
    refine nodup_insert hn' fun hm => ?_
    have hm' : s + runLen pre + s₁ ∈ ts.heapChunks.map (·.addr) := by
      rw [hH]
      simp only [layout, List.map_append, List.map_cons, List.append_assoc,
        List.cons_append, List.nil_append, runLen_cons, runLen_nil, Nat.add_zero]
      exact hm
    obtain ⟨c, hc, hca⟩ := List.mem_map.mp hm'
    rcases hap c hc (by omega) with h1 | h1 <;> omega
  · show coalescedB (pre ++ [(s₁, u₁), (sz - s₁, u₂)] ++ post) = true
    rw [List.append_assoc, List.cons_append, coalescedB_mid_used _ _ _ hu₁,
      List.singleton_append, coalescedB_cons]
    exact ⟨hc1, hc2, fun h' => absurd h' (by rw [hu₂]; simp)⟩
  · intro h0 e he
    subst h0
    rw [List.append_assoc, List.cons_append, getLast?_append_cons, List.singleton_append,
      List.getLast?_cons_cons] at he
    rcases mem_getLast?_cons he with ⟨-, rfl⟩ | ⟨hne, he⟩
    · exact hu₂
    · apply h.runs_last (R₁ := R₁) (s := s) hr e
      rw [getLast?_append_cons]
      cases post with
      | nil => exact absurd rfl hne
      | cons q qs => rw [List.getLast?_cons_cons]; exact he

/-- **Resizing the current segment's last chunk** (`_int_realloc`'s growth into top: the chunk
merged into top and `nb` bytes carved back) keeps `TopWF`. -/
theorem grow (h : TopWF C ts) (hA : C.align = 16) {pre : List (Nat × Use)} {sz : Nat} {u u' : Use}
    (hc : ts.chunks = pre ++ [(sz, u)]) {nb : Nat} (hnb : nb % C.align = 0) (hmin : C.minSize ≤ nb)
    (hz : nb + C.minSize ≤ sz + ts.topSize) (hu' : u'.tagFree = false) :
    TopWF C { ts with chunks := pre ++ [(nb, u')], top := ts.top - sz + nb, topSize := ts.topSize + sz - nb } := by
  have hs : ts.start ≠ 0 := fun h0 => by have := (h.noHeap h0).1; rw [hc] at this; simp at this
  have hH : ts.heapChunks = ((ts.old.flatMap fun g => layout g.start g.chunks) ++ layout ts.start pre) ++
      [⟨ts.start + runLen pre, sz, u⟩] := by
    simp [TopSt.heapChunks, hc, layout_append, layout]
  have hH' : TopSt.heapChunks { ts with chunks := pre ++ [(nb, u')], top := ts.top - sz + nb, topSize := ts.topSize + sz - nb } =
      ((ts.old.flatMap fun g => layout g.start g.chunks) ++ layout ts.start pre) ++
        [⟨ts.start + runLen pre, nb, u'⟩] := by
    simp [TopSt.heapChunks, layout_append, layout]
  have hxc : (⟨ts.start + runLen pre, sz, u⟩ : Chunk) ∈ ts.heapChunks := by rw [hH]; simp
  have hx := h.sizes _ hxc
  have hxa := h.aligned _ hxc
  have hxn := h.nonNull _ hxc
  simp only at hx hxa hxn
  have htop : ts.top = ts.start + runLen pre + sz := by
    have := h.topAt hs; rw [hc] at this; rw [this]; show _ = _ + runLen _ + _
    rw [show (pre ++ [(sz, u)]).map (·.1) = pre.map (·.1) ++ [sz] by simp, List.sum_append]; simp [runLen]; omega
  have htB := h.topBound hs
  have htA := h.topAligned
  have hsm := h.sysMem
  rw [hH] at hsm
  have hmem : ∀ c ∈ ((ts.old.flatMap fun g => layout g.start g.chunks) ++ layout ts.start pre),
      c ∈ ts.heapChunks := fun c hc' => by rw [hH]; exact List.mem_append_left _ hc'
  have hall : ∀ P : Chunk → Prop, (∀ c ∈ ts.heapChunks, P c) → P ⟨ts.start + runLen pre, nb, u'⟩ →
      ∀ c ∈ TopSt.heapChunks { ts with chunks := pre ++ [(nb, u')], top := ts.top - sz + nb, topSize := ts.topSize + sz - nb }, P c := by
    intro P h1 h2 c hc'
    rw [hH'] at hc'
    rcases List.mem_append.mp hc' with hc' | hc'
    · exact h1 c (hmem c hc')
    · simp only [List.mem_singleton] at hc'; subst hc'; exact h2
  rw [hA] at hnb htA hx hxa
  exact
  { sizes := hall _ h.sizes ⟨by rw [hA]; exact hnb, hmin⟩
    aligned := hall _ h.aligned (by simp only; rw [hA]; exact hxa)
    nonNull := hall _ h.nonNull hxn
    topAt := fun _ => by
      simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
        List.sum_nil]
      show _ = ts.start + (runLen pre + (nb + 0))
      omega
    topAligned := by simp only; rw [hA]; omega
    topMin := fun _ => by simp only; omega
    coalesced := by
      show coalescedB (pre ++ [(nb, u')]) = true
      have := h.coalesced; unfold Coalesced at this; rw [hc] at this
      rw [coalescedB_mid_used _ _ _ hu']
      exact ⟨coalescedB_append_left _ _ this, rfl⟩
    lastUsed := by
      intro c hc'; simp only [List.getLast?_append, List.getLast?_singleton, Option.some_or,
        Option.mem_def, Option.some.injEq] at hc'
      subst hc'; exact hu'
    coalescedOld := h.coalescedOld
    sysMem := by
      rw [hH']
      simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil] at hsm ⊢
      omega
    sysMemBound := h.sysMemBound
    noHeap := fun h0 => absurd h0 hs
    nodup := by
      rw [hH']
      have := h.nodup; rw [hH] at this
      simpa using this
    bound := hall _ h.bound (by simp only; omega)
    topBound := fun _ => by simp only; omega }

end TopWF

namespace Algo

variable {C : Config}

/-! ## The frame algebra with freed payloads -/

/-- `Frame` is monotone in the freed payloads. -/
theorem Frame.mono {l l' : Local} {f f' : List (Nat × Nat)} (h : Frame C l l' f)
    (hs : ∀ x ∈ f, x ∈ f') : Frame C l l' f' :=
  { h with
    clients := fun c hc hu hn => h.clients c hc hu (fun hm => hn (hs _ hm))
    fresh := fun tc' i e ht he => by
      rcases h.fresh tc' i e ht he with h1 | ⟨h1, h2 | h2⟩
      · exact .inl h1
      · exact .inr ⟨h1, .inl (hs _ h2)⟩
      · exact .inr ⟨h1, .inr h2⟩ }

/-- **Two frames compose** when what the second frees was lent out and not parked, the client
chunks the whole frees are the ones the pieces free, and the new tcache entries of each piece are
accounted for. -/
theorem Frame.comp {l l₁ l₂ : Local} {f₁ f₂ f : List (Nat × Nat)} (hw₁ : LocalWF C l₁)
    (h₁ : Frame C l l₁ f₁) (h₂ : Frame C l₁ l₂ f₂)
    (hcl : ∀ c ∈ l.av.chunks, c.use = .client → (c.addr + C.hdr, usable C c false) ∉ f →
      (c.addr + C.hdr, usable C c false) ∉ f₁ ∧ (c.addr + C.hdr, usable C c false) ∉ f₂)
    (hpk : ∀ x ∈ f₂, x ∉ l₁.thread.parked C)
    (hold : ∀ e : Nat × Nat, (e.1 + C.hdr, e.2 - C.sizeSz) ∈ f₁ →
      (e.1 + C.hdr, e.2 - C.sizeSz) ∈ f ∨ ∀ c ∈ l.av.chunks, c.addr = e.1 → c.use ≠ .client)
    (hnew : ∀ tc' i e, l₂.thread.tcache = some tc' → e ∈ tc'.bins i →
      (¬ ∃ tc j, l₁.thread.tcache = some tc ∧ e ∈ tc.bins j) →
      ((e.1 + C.hdr, e.2 - C.sizeSz) ∈ f₂ ∨ ∀ c ∈ l₁.av.chunks, c.addr = e.1 → c.use ≠ .client) →
      (e.1 + C.hdr, e.2 - C.sizeSz) ∈ f ∨ ∀ c ∈ l.av.chunks, c.addr = e.1 → c.use ≠ .client) :
    Frame C l l₂ f where
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
  clients c hc hu hn :=
    have h := hcl c hc hu hn
    h₂.clients c (h₁.clients c hc hu h.1) hu h.2
  fresh tc'' i e ht he := by
    by_cases hin : ∃ tc j, l₁.thread.tcache = some tc ∧ e ∈ tc.bins j
    · obtain ⟨tc', j, ht', he'⟩ := hin
      rcases h₁.fresh tc' j e ht' he' with h | ⟨⟨c, hc, h1, h2, h3⟩, hfr'⟩
      · exact .inl h
      · have hpay : (c.addr + C.hdr, usable C c false) ∉ f₂ := by
          intro hm
          apply hpk _ hm
          have := mem_parked_of (hw₁.tcache tc' ht') ht' he'
          rw [show (c.addr + C.hdr, usable C c false) = epay C e by simp [epay, usable, h1, h2]]
          exact this
        refine .inr ⟨⟨c, h₂.clients c hc h3 hpay, h1, h2, h3⟩, ?_⟩
        rcases hfr' with hm | hm
        · exact hold e hm
        · exact .inr hm
    · rcases h₂.fresh tc'' i e ht he with h | ⟨hc, hfr⟩
      · exact absurd h hin
      · exact .inr ⟨hc, hnew tc'' i e ht he hin hfr⟩

/-- **A freed payload with no lent-out chunk at its address before** can be dropped from a
frame. -/
theorem Frame.drop {l l' : Local} {f : List (Nat × Nat)} {x : Nat × Nat} (h : Frame C l l' (x :: f))
    (hx : ∀ c ∈ l.av.chunks, c.use = .client → c.addr + C.hdr ≠ x.1) : Frame C l l' f :=
  { h with
    clients := fun c hc hu hn => h.clients c hc hu (fun hm => by
      rcases List.mem_cons.mp hm with hm | hm
      · exact hx c hc hu (by rw [← hm])
      · exact hn hm)
    fresh := fun tc' i e ht he => by
      rcases h.fresh tc' i e ht he with h1 | ⟨h1, h2 | h2⟩
      · exact .inl h1
      · rcases List.mem_cons.mp h2 with h2 | h2
        · refine .inr ⟨h1, .inr fun c hc hca hcu => hx c hc hcu ?_⟩
          rw [hca, ← h2]
        · exact .inr ⟨h1, .inl h2⟩
      · exact .inr ⟨h1, .inr h2⟩ }

/-- **`LocalSp` is carried by a frame** whose freed payloads were not parked. -/
theorem LocalSp.of_frame' (hC : C.Ok) {l l' : Local} {f : List (Nat × Nat)} (hw : LocalWF C l)
    (hsp : LocalSp C l) (hF : Frame C l l' f) (hpk : ∀ x ∈ f, x ∉ l.thread.parked C) :
    LocalSp C l' where
  covered := hF.covered
  entries tc' ht' i e he := by
    rcases hF.fresh tc' i e ht' he with ⟨tc, j, ht, he0⟩ | ⟨hc, -⟩
    · rcases hsp.entries tc ht j e he0 with ⟨c, hc, h1, h2, h3⟩ | ⟨ha, hcv⟩
      · refine .inl ⟨c, hF.clients c hc h3 fun hm => hpk _ hm ?_, h1, h2, h3⟩
        rw [show (c.addr + C.hdr, usable C c false) = epay C e by simp [epay, usable, h1, h2]]
        exact mem_parked_of (hw.tcache tc ht) ht he0
      · have h := hF.spatial e (entry_pos hC hw ht he0) hcv ha
        exact .inr ⟨h.2, h.1⟩
    · exact .inl hc
  heaps hm := hF.heaps (hsp.heaps (by rw [← hF.isMain]; exact hm))

/-- **`KeptAway` composes** over any frame. -/
theorem KeptAway.trans' (hC : C.Ok) {l l₁ l₂ : Local} {f : List (Nat × Nat)} (hw : LocalWF C l)
    (hsp : LocalSp C l) (hF : Frame C l l₁ f) (k₁ : KeptAway l l₁) (k₂ : KeptAway l₁ l₂) :
    KeptAway l l₂ := by
  intro tc i e ht he ha
  obtain ⟨tc₁, ht₁, he₁⟩ := k₁ tc i e ht he ha
  apply k₂ tc₁ i e ht₁ he₁
  have h0 := entry_pos hC hw ht he
  rcases hsp.entries tc ht i e he with ⟨c, hc, h1, h2, -⟩ | ⟨-, hcv⟩
  · exfalso
    have hm := mem_spans_of_chunk hc
    rw [h1, h2] at hm
    exact not_away_self hm h0 ha
  · exact (hF.spatial e h0 hcv ha).2

theorem keptAway_refl (l : Local) : KeptAway l l := fun tc _ _ ht he _ => ⟨tc, ht, he⟩

/-! ## Live payloads -/

/-- A live payload's length is `8` or `0` modulo `16` (an arena chunk's `size - SIZE_SZ`, an
`mmap`ed chunk's `size - 2 * SIZE_SZ`). -/
theorem live_mod (hC : C.Ok) {l : Local} (hw : LocalWF C l) {y : Nat × Nat} (hy : y ∈ l.live C) :
    y.2 % 16 = 8 ∨ y.2 % 16 = 0 := by
  have h8 := hC.sizeSz; have h16 := hC.align; have h32 := hC.minSize; have hpg := hC.page
  rcases mem_llive.mp hy with ⟨hyo, -⟩ | hys
  · obtain ⟨c, hc, -, rfl⟩ := mem_out.mp hyo
    obtain ⟨h1, h2⟩ := hw.arena.tiles.sizes c hc
    rw [h16] at h1; rw [h32] at h2
    show (c.size - C.sizeSz) % 16 = 8 ∨ (c.size - C.sizeSz) % 16 = 0
    rw [h8]; omega
  · obtain ⟨m, hm, hmu, rfl⟩ := mem_shlive.mp hys
    have h1 := (hw.shared.mm.page m hm hmu).2
    have h2 := (hw.mmSize m hm).1
    unfold Config.hdr at h2
    rw [hpg] at h1; rw [h8] at h2
    show (m.size - 2 * C.sizeSz) % 16 = 8 ∨ (m.size - 2 * C.sizeSz) % 16 = 0
    rw [h8]; omega

/-- A live payload of the arena's lent-out list is a live payload of the arena (not `mmap`ed). -/
theorem arenaLive_of {l : Local} (hw : LocalWF C l) {y : Nat × Nat} (hy : y ∈ l.live C)
    (hyo : y ∈ l.av.out C) : y ∈ l.arenaLive C := by
  rcases mem_llive.mp hy with ⟨-, hnp⟩ | hys
  · exact List.mem_filter.mpr ⟨hyo, by simpa [contains_false] using hnp⟩
  · exfalso
    obtain ⟨c, hc, -, hce⟩ := mem_out.mp hyo
    obtain ⟨m, hm, -, hme⟩ := mem_shlive.mp hys
    rw [hce] at hme
    simp only [Prod.mk.injEq] at hme
    exact addr_clash hw.apart (r := (c.addr, c.size)) (span_mem_spans hc)
      (List.mem_map.mpr ⟨m, hm, rfl⟩) (by simp only; omega)

theorem arenaLive_sub {l : Local} {y : Nat × Nat} (h : y ∈ l.arenaLive C) : y ∈ l.live C := by
  unfold Local.live; exact List.mem_append_left _ h

theorem arenaLive_not_parked {l : Local} {y : Nat × Nat} (h : y ∈ l.arenaLive C) :
    y ∉ l.thread.parked C := by
  have := (List.mem_filter.mp h).2
  simpa [contains_false] using this

theorem arenaLive_out {l : Local} {y : Nat × Nat} (h : y ∈ l.arenaLive C) : y ∈ l.av.out C :=
  (List.mem_filter.mp h).1

/-- The view's live set after an arena step that changes the lent-out payloads, with the thread
and the shared part kept: the not parked ones follow. -/
theorem live_of_out_perm {l l' : Local} {R A A' : List (Nat × Nat)} (hth : l'.thread = l.thread)
    (hsh : l'.shared = l.shared) (hout : (l.av.out C).Perm (A ++ R)) (hout' : (l'.av.out C).Perm (A' ++ R))
    (hA : ∀ x ∈ A, x ∉ l.thread.parked C) (hA' : ∀ x ∈ A', x ∉ l.thread.parked C) :
    (l.live C).Perm (A ++ (R.filter fun pu => !(l.thread.parked C).contains pu) ++ l.shared.live C) ∧
    (l'.live C).Perm (A' ++ (R.filter fun pu => !(l.thread.parked C).contains pu) ++ l.shared.live C) := by
  have key : ∀ {X : List (Nat × Nat)}, (∀ x ∈ X, x ∉ l.thread.parked C) →
      (X ++ R).filter (fun pu => !(l.thread.parked C).contains pu) =
        X ++ R.filter (fun pu => !(l.thread.parked C).contains pu) := by
    intro X hX
    rw [List.filter_append, List.filter_eq_self.mpr]
    intro x hx; simpa [contains_false] using hX x hx
  unfold Local.live
  rw [hth, hsh]
  exact ⟨List.Perm.append_right _ ((hout.filter _).trans (List.Perm.of_eq (key hA))),
    List.Perm.append_right _ ((hout'.filter _).trans (List.Perm.of_eq (key hA')))⟩

/-! ## Splitting a lent-out chunk -/

/-- **Splitting a lent-out chunk `d`** into `nb` and `d.size - nb` bytes, both lent out: well
formed, the spans inside the old ones, the client chunks other than `d` kept, the lent-out
payloads `d`'s replaced by the two pieces'. -/
theorem splitClient (hC : C.Ok) {l : Local} (hw : LocalWF C l) {d : Chunk} (hd : d ∈ l.av.chunks)
    (hdu : d.use = .client) {nb : Nat} (hnb : nb % C.align = 0) (hmin : C.minSize ≤ nb)
    (hrem : nb + C.minSize ≤ d.size) :
    LocalWF C (withTiles l (l.av.tiles.split d.addr nb .client .client)) ∧
    SpansIn (withTiles l (l.av.tiles.split d.addr nb .client .client)).av.spans l.av.spans ∧
    (∀ c, c ∈ (withTiles l (l.av.tiles.split d.addr nb .client .client)).av.chunks ↔
      (c ∈ l.av.chunks ∧ c ≠ d) ∨ c = ⟨d.addr, nb, .client⟩ ∨ c = ⟨d.addr + nb, d.size - nb, .client⟩) ∧
    (∀ c ∈ l.av.chunks, c.addr ≠ d.addr + nb) ∧
    ∃ R, (l.av.out C).Perm ([(d.addr + C.hdr, d.size - C.sizeSz)] ++ R) ∧
      ((withTiles l (l.av.tiles.split d.addr nb .client .client)).av.out C).Perm
        ([(d.addr + C.hdr, nb - C.sizeSz), (d.addr + nb + C.hdr, d.size - nb - C.sizeSz)] ++ R) := by
  have h32 := hC.minSize
  have ht := hw.arena.tiles
  have hn' := ht.nodup
  have hpos : 0 < nb := by omega
  obtain ⟨R₁, s, pre, post, R₂, hr, ha⟩ := runs_of_chunk ht hd
  have hap : ∀ c ∈ l.av.tiles.heapChunks, c.addr ≠ s + runLen pre →
      c.addr + c.size ≤ s + runLen pre ∨ s + runLen pre + d.size ≤ c.addr := by
    intro c hc hne
    rw [ha] at hne ⊢
    exact Apart.ne_apart hw.apart (mem_spans_of_chunk hc) (mem_spans_of_chunk hd)
      (fun h => hne (congrArg Prod.fst h))
  have hts : TopWF C (l.av.tiles.split d.addr nb .client .client) := by
    have := ht.splitUsed hr (s₁ := nb) (u₁ := .client) (u₂ := .client) rfl rfl hnb hmin (by omega)
      (by omega) hpos hap
    rw [ha] at this; exact this
  obtain ⟨A, B, hH, hH', hAB⟩ := split_chunks ht hd (nb := nb) (by omega) .client .client
  have hAne : ∀ c ∈ A, c.addr ≠ d.addr := fun c hc => hAB c (List.mem_append_left _ hc)
  have hBne : ∀ c ∈ B, c.addr ≠ d.addr := fun c hc => hAB c (List.mem_append_right _ hc)
  have hnew : ∀ c ∈ l.av.chunks, c.addr ≠ d.addr + nb := by
    intro c hc hca
    by_cases hcd : c.addr = d.addr
    · omega
    · have := Apart.ne_apart hw.apart (mem_spans_of_chunk hc) (mem_spans_of_chunk hd)
        (fun h => hcd (congrArg Prod.fst h))
      simp only at this; omega
  have hmemO : ∀ c, c ∈ l.av.chunks ↔ c ∈ A ∨ c = d ∨ c ∈ B := by
    intro c; show c ∈ l.av.tiles.heapChunks ↔ _; rw [hH]; simp
  have hmemN : ∀ c, c ∈ (l.av.tiles.split d.addr nb .client .client).heapChunks ↔
      c ∈ A ∨ c = ⟨d.addr, nb, .client⟩ ∨ c = ⟨d.addr + nb, d.size - nb, .client⟩ ∨ c ∈ B := by
    intro c; rw [hH']; simp
  have hnotd : ∀ c, c ∈ A ∨ c ∈ B → c ≠ d := by
    rintro c (h | h) rfl
    · exact hAne c h rfl
    · exact hBne c h rfl
  -- the views: neither the old chunk nor the pieces are in a list
  have hview : ∀ p : Use → Bool, p .client = false →
      Chunk.view p (l.av.tiles.split d.addr nb .client .client).heapChunks = Chunk.view p l.av.tiles.heapChunks := by
    intro p hp
    rw [hH', hH]
    simp [Chunk.view, List.filter_append, hp, hdu]
  have hav := hw.arena.withTilesViews _ hts (hview _ rfl) (hview _ rfl) (hview _ rfl)
  have hw' : LocalWF C (withTiles l (l.av.tiles.split d.addr nb .client .client)) := by
    refine hw.withAv' _ hav rfl rfl rfl (by simp [TopSt.split]) ?_
    have hap0 := hw.apart
    unfold Local.spans ArenaSt.spans TopSt.spans at hap0 ⊢
    rw [hH']
    rw [hH] at hap0
    have e1 : (l.av.tiles.split d.addr nb .client .client).start = l.av.tiles.start := rfl
    have e2 : (l.av.tiles.split d.addr nb .client .client).top = l.av.tiles.top := rfl
    have e3 : (l.av.tiles.split d.addr nb .client .client).topSize = l.av.tiles.topSize := rfl
    have e4 : ({ l.av with tiles := l.av.tiles.split d.addr nb .client .client } : ArenaSt).heapSpans = l.av.heapSpans := rfl
    simp only [e1, e2, e3, e4]
    have := Apart.split_mid (L := A.map (fun c => (c.addr, c.size)))
      (X := B.map (fun c => (c.addr, c.size)) ++ (if l.av.tiles.start = 0 then [] else
        [(l.av.tiles.top, l.av.tiles.topSize)]) ++ l.av.heapSpans ++
          l.shared.mm.chunks.map (fun c => (c.addr, c.size)))
      (r := (d.addr, d.size)) (by simpa [List.append_assoc] using hap0) hpos (by omega)
    simpa [List.append_assoc] using this
  have hin : SpansIn (withTiles l (l.av.tiles.split d.addr nb .client .client)).av.spans l.av.spans := by
    show SpansIn ((l.av.tiles.split d.addr nb .client .client).spans ++ l.av.heapSpans)
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
  refine ⟨hw', hin, fun c => ?_, hnew, ?_⟩
  · show c ∈ (l.av.tiles.split d.addr nb .client .client).heapChunks ↔ _
    rw [hmemN c]
    constructor
    · rintro (h | h | h | h)
      · exact .inl ⟨(hmemO c).mpr (.inl h), hnotd c (.inl h)⟩
      · exact .inr (.inl h)
      · exact .inr (.inr h)
      · exact .inl ⟨(hmemO c).mpr (.inr (.inr h)), hnotd c (.inr h)⟩
    · rintro (⟨h, hne⟩ | h | h)
      · rcases (hmemO c).mp h with h | h | h
        · exact .inl h
        · exact absurd h hne
        · exact .inr (.inr (.inr h))
      · exact .inr (.inl h)
      · exact .inr (.inr (.inl h))
  · refine ⟨(Chunk.view (· = .client) A ++ Chunk.view (· = .client) B).map
      (fun c => (c.addr + C.hdr, usable C c false)), ?_, ?_⟩
    · unfold ArenaSt.out ArenaSt.chunks
      rw [hH]
      simp only [Chunk.view, List.filter_append, List.filter_cons, hdu, decide_true, ite_true,
        List.map_append, List.map_cons, usable, Bool.false_eq_true, ite_false]
      exact List.perm_middle
    · unfold ArenaSt.out ArenaSt.chunks
      simp only [withTiles]
      rw [hH']
      simp only [Chunk.view, List.filter_append, List.filter_cons, decide_true, ite_true,
        List.map_append, List.map_cons, usable, Bool.false_eq_true, ite_false]
      have : ∀ (X Y : List (Nat × Nat)) (a b : Nat × Nat), (X ++ a :: b :: Y).Perm (a :: b :: (X ++ Y)) := by
        intro X Y a b
        exact List.perm_middle.trans (List.Perm.cons _ List.perm_middle)
      simpa using this _ _ _ _

/-- **A tcache entry starting inside an arena chunk is that chunk** (the tcache holds client
chunks of the arena or ranges away from it). -/
theorem entry_inside (hC : C.Ok) {l : Local} (hw : LocalWF C l) (hsp : LocalSp C l) {tc : TcacheSt}
    (ht : l.thread.tcache = some tc) {i : Nat} {e : Nat × Nat} (he : e ∈ tc.bins i) {d : Chunk}
    (hd : d ∈ l.av.chunks) (h1 : d.addr ≤ e.1) (h2 : e.1 < d.addr + d.size) :
    e.1 = d.addr ∧ e.2 = d.size := by
  have h0 := entry_pos hC hw ht he
  rcases hsp.entries tc ht i e he with ⟨c, hc, hca, hcs, -⟩ | ⟨ha, -⟩
  · by_cases hcd : c.addr = d.addr
    · have := chunk_unique hw.arena.tiles.nodup hc hd hcd
      subst this; exact ⟨hca.symm.trans hcd, hcs.symm⟩
    · have := Apart.ne_apart hw.apart (mem_spans_of_chunk hc) (mem_spans_of_chunk hd)
        (fun h => hcd (congrArg Prod.fst h))
      simp only at this; omega
  · have := ha _ (mem_spans_of_chunk hd)
    simp only at this; omega

/-- A payload `(a + 16, s - 8)` with `a` inside a chunk `d` and `(a, s) ≠ (d.addr, d.size)` is not
parked. -/
theorem not_parked_inside (hC : C.Ok) {l : Local} (hw : LocalWF C l) (hsp : LocalSp C l) {d : Chunk}
    (hd : d ∈ l.av.chunks) {a s : Nat} (h1 : d.addr ≤ a) (h2 : a < d.addr + d.size)
    (hs : C.sizeSz ≤ s) (hne : ¬ (a = d.addr ∧ s = d.size)) :
    (a + C.hdr, s - C.sizeSz) ∉ l.thread.parked C := by
  intro hp
  obtain ⟨tc, htc, i, -, e, he, hpe⟩ := mem_parked.mp hp
  simp only [epay, Prod.mk.injEq] at hpe
  have hes := ((hw.tcache tc htc).size i e he).2.2
  have := hC.minSize; have := hC.sizeSz
  obtain ⟨e1, e2⟩ := entry_inside hC hw hsp htc he hd (by omega) (by omega)
  exact hne ⟨by omega, by omega⟩

/-- **A frame for an arena-only step whose spans lie inside the old ones.** -/
theorem frame_arena_in {l : Local} {av' : ArenaSt} {f : List (Nat × Nat)} (hsp : LocalSp C l)
    (hin : SpansIn av'.spans l.av.spans) (hheaps : av'.heaps = l.av.heaps)
    (hcl : ∀ c ∈ l.av.chunks, c.use = .client → (c.addr + C.hdr, usable C c false) ∉ f → c ∈ av'.chunks) :
    Frame C l { l with av := av' } f :=
  have hin' := spansIn_local hin
  { avAddr := rfl, isMain := rfl, spatial := fun _ _ hc ha => ⟨hc, hin'.away ha⟩,
    covered := hin'.covers hsp.covered, brkStart := rfl, nonMain := fun _ => ⟨rfl, rfl⟩,
    acct := fun _ => Nat.le_refl _, init := rfl, arenas := ⟨rfl, rfl, rfl⟩, arena := rfl,
    heaps := fun h => by simp only; rw [hheaps]; exact h,
    clients := hcl, fresh := fun tc' i e htc he => .inl ⟨tc', i, htc, he⟩ }

/-- **`_int_realloc`'s split below** of a lent-out, not parked chunk `d` to `nb ≤ d.size` bytes:
the payload stays at `d`, it has at least `nb - SIZE_SZ` bytes and replaces `d`'s in the live set;
a remainder is freed. The new tcache entries are not at `d`. -/
theorem reallocSplit_spec (hC : C.Ok) {l l' : Local} {q : Nat} (hw : LocalWF C l) (hsp : LocalSp C l)
    {d : Chunk} (hd : d ∈ l.av.chunks) (hdu : d.use = .client)
    (hnp : (d.addr + C.hdr, d.size - C.sizeSz) ∉ l.thread.parked C) {nb : Nat}
    (hnb : nb % C.align = 0) (hmin : C.minSize ≤ nb) (hle : nb ≤ d.size)
    (h : reallocSplit C l d.addr d.size nb = .ok (q, l')) :
    q = d.addr + C.hdr ∧ LocalWF C l' ∧ Frame C l l' [(d.addr + C.hdr, d.size - C.sizeSz)] ∧
      KeptAway l l' ∧
      ((l' = l ∧ d.size - nb < C.minSize) ∨
        (nb + C.minSize ≤ d.size ∧ (l'.live C).Perm ((d.addr + C.hdr, nb - C.sizeSz) ::
          (l.live C).erase (d.addr + C.hdr, d.size - C.sizeSz)))) ∧
      (∀ tc' i e, l'.thread.tcache = some tc' → e ∈ tc'.bins i →
        (∃ tc j, l.thread.tcache = some tc ∧ e ∈ tc.bins j) ∨ e.1 ≠ d.addr) := by
  have h8 := hC.sizeSz; have h32 := hC.minSize; have h16 := hC.align
  have hhdr : C.hdr = 16 := by unfold Config.hdr; omega
  unfold reallocSplit at h
  split at h
  · injection h with h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    rename_i hlt
    refine ⟨rfl, hw, Frame.of_eq rfl rfl rfl rfl rfl rfl rfl hsp.covered, keptAway_refl _,
      .inl ⟨rfl, hlt⟩, fun tc' i e ht he => .inl ⟨tc', i, ht, he⟩⟩
  rename_i hrem
  have hrem : nb + C.minSize ≤ d.size := by omega
  obtain ⟨l₂, h2, h⟩ := bind_ok_inv h
  injection h with h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
  -- the split
  obtain ⟨hw₁, hin, hmem, hnew, R, hR, hR'⟩ := splitClient hC hw hd hdu hnb hmin hrem
  obtain ⟨l₁, hl₁⟩ : ∃ l₁, l₁ = withTiles l (l.av.tiles.split d.addr nb .client .client) := ⟨_, rfl⟩
  rw [← hl₁] at hw₁ hmem hR' h2
  have hold' : (d.addr + C.hdr, d.size - C.sizeSz) = (d.addr + C.hdr, usable C d false) := by
    simp [usable]
  have hF₁ : Frame C l l₁ [(d.addr + C.hdr, d.size - C.sizeSz)] := by
    rw [hl₁]
    refine frame_arena_in hsp hin rfl fun c hc hcu hn => ?_
    have := (hmem c).mpr (.inl ⟨hc, by rintro rfl; exact hn (by simp [usable])⟩)
    rw [hl₁] at this; exact this
  have hsp₁ : LocalSp C l₁ := LocalSp.of_frame' hC hw hsp hF₁ (by simpa using hnp)
  have hth : l₁.thread = l.thread := by rw [hl₁]; rfl
  -- the remainder
  have hdx : d.addr ≤ d.addr + nb := by omega
  have hdx' : d.addr + nb < d.addr + d.size := by omega
  have hnp₂ : (d.addr + nb + C.hdr, d.size - nb - C.sizeSz) ∉ l.thread.parked C :=
    not_parked_inside hC hw hsp hd hdx hdx' (by omega) (by omega)
  have hnp₁ : (d.addr + C.hdr, nb - C.sizeSz) ∉ l.thread.parked C :=
    not_parked_inside hC hw hsp hd (Nat.le_refl _) (by omega) (by omega) (by omega)
  have hrc : (⟨d.addr + nb, d.size - nb, .client⟩ : Chunk) ∈ l₁.av.chunks := (hmem _).mpr (.inr (.inr rfl))
  have hx₂ : (d.addr + nb + C.hdr, d.size - nb - C.sizeSz) ∈ l₁.arenaLive C :=
    List.mem_filter.mpr ⟨mem_out.mpr ⟨_, hrc, rfl, rfl⟩, by simpa [contains_false, hth] using hnp₂⟩
  have hfree : intFree C l₁ (d.addr + nb + C.hdr - C.hdr) = .ok l₂ := by
    rw [Nat.add_sub_cancel]; exact h2
  obtain ⟨hw₂, hF₂, hK₂, hlive₂⟩ := bodyFree C hC l₁ l₂ _ _ hw₁ hsp₁ hx₂ hfree
  have hd₁ : (⟨d.addr, nb, .client⟩ : Chunk) ∈ l₁.av.chunks := (hmem _).mpr (.inr (.inl rfl))
  -- no client of `l₁` ... the frame
  have hF : Frame C l l₂ [(d.addr + C.hdr, d.size - C.sizeSz)] := by
    refine Frame.comp hw₁ hF₁ hF₂ (fun c hc hcu hn => ⟨hn, ?_⟩) ?_ (fun e he => .inl he) ?_
    · intro hm
      simp only [List.mem_singleton, usable, Bool.false_eq_true, ite_false, Prod.mk.injEq] at hm
      exact hnew c hc (by omega)
    · intro x hx; simp only [List.mem_singleton] at hx; subst hx
      simpa [hth] using hnp₂
    · intro tc' i e _ _ _ hfr
      rcases hfr with hm | hm
      · right
        intro c hc hca hcu
        simp only [List.mem_singleton, Prod.mk.injEq] at hm
        exact hnew c hc (by omega)
      · right
        intro c hc hca hcu
        by_cases hcd : c = d
        · subst hcd; exact hm _ hd₁ hca rfl
        · exact hm c ((hmem c).mpr (.inl ⟨hc, hcd⟩)) hca hcu
  refine ⟨rfl, hw₂, hF, KeptAway.trans' hC hw hsp hF₁
    (fun tc _ _ ht he _ => ⟨tc, by rw [hth]; exact ht, he⟩) hK₂, .inr ⟨hrem, ?_⟩, ?_⟩
  · -- the live set
    obtain ⟨hL, hL₁⟩ := live_of_out_perm (l := l) (l' := l₁) hth (by rw [hl₁]; rfl) hR hR'
      (by simpa using hnp) (by simp [hnp₁, hnp₂])
    have hne : (d.addr + C.hdr, nb - C.sizeSz) ≠ (d.addr + nb + C.hdr, d.size - nb - C.sizeSz) := by
      simp only [ne_eq, Prod.mk.injEq, not_and]; intro; omega
    refine hlive₂.trans ((hL₁.erase _).trans ?_)
    simp only [List.cons_append, List.nil_append]
    rw [List.erase_cons_tail (by simpa [beq_iff_eq] using hne), List.erase_cons_head]
    refine List.Perm.cons _ ?_
    have := (hL.erase (d.addr + C.hdr, d.size - C.sizeSz)).symm
    simp only [List.cons_append, List.nil_append, List.erase_cons_head] at this
    exact this
  · intro tc' i e ht he
    rcases hF₂.fresh tc' i e ht he with ⟨tc, j, ht', he'⟩ | ⟨-, hfr⟩
    · exact .inl ⟨tc, j, by rw [← hth]; exact ht', he'⟩
    · right
      rcases hfr with hm | hm
      · simp only [List.mem_singleton, Prod.mk.injEq] at hm; omega
      · intro hea; exact hm _ hd₁ hea.symm rfl

/-! ## Growing into top -/

/-- **`_int_realloc`'s growth into top** of the current segment's last chunk `d` (lent out, not
parked) to `nb > d.size` bytes, top keeping at least `MINSIZE`. -/
theorem growTop_spec (hC : C.Ok) {l : Local} (hw : LocalWF C l) (hsp : LocalSp C l)
    {d : Chunk} (hd : d ∈ l.av.chunks) (hdu : d.use = .client)
    (hnp : (d.addr + C.hdr, d.size - C.sizeSz) ∉ l.thread.parked C) {pre : List (Nat × Use)}
    (hc : l.av.tiles.chunks = pre ++ [(d.size, .client)]) (ha : l.av.tiles.start + runLen pre = d.addr)
    {nb : Nat} (hnb : nb % C.align = 0) (hmin : C.minSize ≤ nb) (hgt : d.size < nb)
    (hz : nb + C.minSize ≤ d.size + l.av.tiles.topSize) :
    LocalWF C (withTiles l (l.av.tiles.mergeTop.useTop nb .client)) ∧
      Frame C l (withTiles l (l.av.tiles.mergeTop.useTop nb .client)) [(d.addr + C.hdr, d.size - C.sizeSz)] ∧
      KeptAway l (withTiles l (l.av.tiles.mergeTop.useTop nb .client)) ∧
      ((withTiles l (l.av.tiles.mergeTop.useTop nb .client)).live C).Perm
        ((d.addr + C.hdr, nb - C.sizeSz) :: (l.live C).erase (d.addr + C.hdr, d.size - C.sizeSz)) := by
  have h8 := hC.sizeSz; have h32 := hC.minSize; have h16 := hC.align
  have ht := hw.arena.tiles
  have hs : l.av.tiles.start ≠ 0 := fun h0 => by have := (ht.noHeap h0).1; rw [hc] at this; simp at this
  have htop : l.av.tiles.top = d.addr + d.size := by
    have := ht.topAt hs; rw [hc] at this; rw [this, ← ha]
    simp [runLen]; omega
  obtain ⟨ts', hts'⟩ : ∃ ts' : TopSt, ts' = l.av.tiles.mergeTop.useTop nb .client := ⟨_, rfl⟩
  rw [← hts']
  have heq : ts' = { l.av.tiles with chunks := pre ++ [(nb, .client)], top := l.av.tiles.top - d.size + nb, topSize := l.av.tiles.topSize + d.size - nb } := by
    rw [hts']
    have hm : l.av.tiles.mergeTop = { l.av.tiles with chunks := pre, top := l.av.tiles.top - d.size, topSize := l.av.tiles.topSize + d.size } := by
      simp [TopSt.mergeTop, hc]
    rw [hm]; rfl
  have hts : TopWF C ts' := by rw [heq]; exact ht.grow h16 hc hnb hmin hz (u' := .client) rfl
  have f1 : ts'.start = l.av.tiles.start := by rw [heq]
  have f2 : ts'.chunks = pre ++ [(nb, .client)] := by rw [heq]
  have f3 : ts'.old = l.av.tiles.old := by rw [heq]
  have f4 : ts'.top = d.addr + nb := by rw [heq]; simp only; omega
  have f5 : ts'.topSize = d.size + l.av.tiles.topSize - nb := by rw [heq]; simp only; omega
  have f6 : ts'.noncontig = l.av.tiles.noncontig := by rw [heq]
  have f7 : ts'.systemMem = l.av.tiles.systemMem := by rw [heq]
  -- chunks
  have hH : l.av.tiles.heapChunks = ((l.av.tiles.old.flatMap fun g => layout g.start g.chunks) ++
      layout l.av.tiles.start pre) ++ [d] := by
    have : l.av.tiles.heapChunks = ((l.av.tiles.old.flatMap fun g => layout g.start g.chunks) ++
        layout l.av.tiles.start pre) ++ [⟨l.av.tiles.start + runLen pre, d.size, .client⟩] := by
      simp [TopSt.heapChunks, hc, layout_append, layout]
    rw [this, ha]; obtain ⟨da, ds, du⟩ := d; simp only at hdu ⊢; rw [hdu]
  have hH' : ts'.heapChunks = ((l.av.tiles.old.flatMap fun g => layout g.start g.chunks) ++
      layout l.av.tiles.start pre) ++ [⟨d.addr, nb, .client⟩] := by
    unfold TopSt.heapChunks; rw [f1, f2, f3]; simp [layout_append, layout, ha]
  have hview : ∀ p : Use → Bool, p .client = false →
      Chunk.view p ts'.heapChunks = Chunk.view p l.av.tiles.heapChunks := by
    intro p hp; rw [hH', hH]; simp [Chunk.view, List.filter_append, hp, hdu]
  have hav := hw.arena.withTilesViews _ hts (hview _ rfl) (hview _ rfl) (hview _ rfl)
  have hdpos : 0 < d.size := by have := (ht.sizes d hd).2; omega
  have hzp : 0 < l.av.tiles.topSize := top_pos hw hs
  have hs' : ts'.start ≠ 0 := by rw [f1]; exact hs
  -- the spans
  have hap' : Apart (withTiles l ts').spans := by
    have h0 := hw.apart
    rw [spans_eq_top hs, hH] at h0
    have h1 := Apart.merge_top h0 (by rw [htop])
    rw [Local.spans_eq]
    unfold TopSt.spans
    simp only [withTiles]
    rw [hH', f4, f5]
    simp only [hs', ↓reduceIte]
    show Apart ((List.map (fun c : Chunk => (c.addr, c.size)) _ ++ _) ++ (l.av.heapSpans ++ _))
    have h2 := Apart.split_mid (L := ((l.av.tiles.old.flatMap fun g => layout g.start g.chunks) ++
        layout l.av.tiles.start pre).map (fun c => (c.addr, c.size))) (r := (d.addr, d.size + l.av.tiles.topSize))
      (X := l.av.heapSpans ++ l.shared.mm.chunks.map (fun c => (c.addr, c.size))) (s := nb)
      (by simpa [List.append_assoc] using h1) (by omega) (by simp only; omega)
    simpa [List.append_assoc] using h2
  have hw' : LocalWF C (withTiles l ts') :=
    hw.withAv' _ hav f1 (by rw [f4, f5]; omega) f6 (by rw [f3]) hap' (hsm := by rw [f7]; exact Nat.le_refl _)
  -- the byte cover
  have hcov : SpanCover l (withTiles l ts') := by
    refine spanCover_tiles rfl fun x ⟨sp, hsp', h1, h2⟩ => ?_
    unfold TopSt.spans at hsp'
    simp only [withTiles, hs', ↓reduceIte, List.mem_append, List.mem_singleton] at hsp'
    have hdmem : d ∈ l.av.tiles.heapChunks := hd
    rcases hsp' with hsp' | rfl
    · rw [hH'] at hsp'
      obtain ⟨c, hc', rfl⟩ := List.mem_map.mp hsp'
      rcases List.mem_append.mp hc' with hc' | hc'
      · exact InSpans.chunk (by rw [hH]; exact List.mem_append_left _ hc') h1 h2
      · simp only [List.mem_singleton] at hc'; subst hc'
        simp only at h1 h2
        by_cases hx : x < d.addr + d.size
        · exact InSpans.chunk hdmem h1 hx
        · exact InSpans.top hs (by omega) (by omega)
    · simp only at h1 h2
      rw [f4] at h1; rw [f4, f5] at h2
      exact InSpans.top hs (by omega) (by omega)
  have hnp' : (d.addr + C.hdr, nb - C.sizeSz) ∉ l.thread.parked C :=
    not_parked_inside hC hw hsp hd (Nat.le_refl _) (by omega) (by omega) (by omega)
  refine ⟨hw', ?_, fun tc _ _ ht' he _ => ⟨tc, ht', he⟩, ?_⟩
  · refine frame_of hsp hw'.apart rfl rfl rfl (Shrink.of_arena rfl rfl hcov rfl) ?_
      (fun tc' i e ht' he => .inl ⟨tc', i, ht', he⟩)
    intro c hc' hcu hn
    show c ∈ ts'.heapChunks
    rw [hH']
    have hc'' : c ∈ l.av.tiles.heapChunks := hc'
    rw [hH] at hc''
    rcases List.mem_append.mp hc'' with h | h
    · exact List.mem_append_left _ h
    · simp only [List.mem_singleton] at h; subst h
      exfalso; simp [usable] at hn
  · have ho : (l.av.out C).Perm ([(d.addr + C.hdr, d.size - C.sizeSz)] ++
        (Chunk.view (· = .client) ((l.av.tiles.old.flatMap fun g => layout g.start g.chunks) ++
          layout l.av.tiles.start pre)).map (fun c => (c.addr + C.hdr, usable C c false))) := by
      unfold ArenaSt.out ArenaSt.chunks
      rw [hH]
      simp only [Chunk.view, List.filter_append, List.filter_cons, hdu, decide_true, ite_true,
        List.filter_nil, List.map_append, List.map_cons, List.map_nil, usable, Bool.false_eq_true, ite_false]
      exact List.perm_append_comm
    have ho' : ((withTiles l ts').av.out C).Perm ([(d.addr + C.hdr, nb - C.sizeSz)] ++
        (Chunk.view (· = .client) ((l.av.tiles.old.flatMap fun g => layout g.start g.chunks) ++
          layout l.av.tiles.start pre)).map (fun c => (c.addr + C.hdr, usable C c false))) := by
      unfold ArenaSt.out ArenaSt.chunks
      simp only [withTiles]
      rw [hH']
      simp only [Chunk.view, List.filter_append, List.filter_cons, decide_true, ite_true,
        List.filter_nil, List.map_append, List.map_cons, List.map_nil, usable, Bool.false_eq_true, ite_false]
      exact List.perm_append_comm
    obtain ⟨hL, hL'⟩ := live_of_out_perm (C := C) (l := l) (l' := withTiles l ts') rfl rfl ho ho'
      (by simpa using hnp) (by simpa using hnp')
    refine (hL'.trans ?_)
    have := (hL.erase (d.addr + C.hdr, d.size - C.sizeSz)).symm
    simp only [List.cons_append, List.nil_append, List.erase_cons_head] at this
    simp only [List.cons_append, List.nil_append]
    exact List.Perm.cons _ this

/-! ## Fusing a lent-out chunk with its neighbour -/

theorem perm_mid2 {α : Type} (X Y : List α) (a b : α) : (X ++ a :: b :: Y).Perm (a :: b :: (X ++ Y)) :=
  List.perm_middle.trans (List.Perm.cons _ List.perm_middle)

theorem perm_mid1' {α : Type} (A B Y : List α) (a : α) :
    (A ++ (B ++ a :: Y)).Perm (a :: (A ++ (B ++ Y))) := by
  rw [← List.append_assoc, ← List.append_assoc]; exact List.perm_middle

theorem perm_mid2' {α : Type} (A B Y : List α) (a b : α) :
    (A ++ (B ++ a :: b :: Y)).Perm (a :: b :: (A ++ (B ++ Y))) := by
  rw [← List.append_assoc, ← List.append_assoc]; exact perm_mid2 _ _ _ _

/-- **Fusing a lent-out chunk with the next chunk** (a held or lent-out one) into one lent-out
chunk: well formed, the bytes kept, the other chunks kept, the lent-out payloads the two old ones
replaced by the fused one. -/
theorem fuseClient {l : Local} (hw : LocalWF C l) {R₁ R₂ : List (Nat × List (Nat × Use))} {s : Nat}
    {pre post : List (Nat × Use)} {sz₁ sz₂ : Nat} {v : Use} (hv : v = .client ∨ v = .internal)
    (hr : l.av.tiles.runs = R₁ ++ (s, pre ++ (sz₁, .client) :: (sz₂, v) :: post) :: R₂) :
    LocalWF C (fuse l (s + runLen pre) .client) ∧ SpanCover l (fuse l (s + runLen pre) .client) ∧
    (fuse l (s + runLen pre) .client).av.tiles.runs = R₁ ++ (s, pre ++ (sz₁ + sz₂, .client) :: post) :: R₂ ∧
    (∀ c ∈ l.av.chunks, c.addr ≠ s + runLen pre → c.addr ≠ s + runLen pre + sz₁ →
      c ∈ (fuse l (s + runLen pre) .client).av.chunks) ∧
    (⟨s + runLen pre, sz₁ + sz₂, .client⟩ : Chunk) ∈ (fuse l (s + runLen pre) .client).av.chunks ∧
    ∃ R, (l.av.out C).Perm ([(s + runLen pre + C.hdr, sz₁ - C.sizeSz)] ++
        (if v = .client then [(s + runLen pre + sz₁ + C.hdr, sz₂ - C.sizeSz)] else []) ++ R) ∧
      ((fuse l (s + runLen pre) .client).av.out C).Perm
        ([(s + runLen pre + C.hdr, sz₁ + sz₂ - C.sizeSz)] ++ R) := by
  have ht : TopWF C l.av.tiles := hw.arena.tiles
  have hn := ht.nodup
  have hvu : v.tagFree = false := by rcases hv with rfl | rfl <;> rfl
  have hr' := TopSt.runs_fuse (x := (sz₁, .client)) (y := (sz₂, v)) Use.client hr rfl hn
  have hr1 : l.av.tiles.runs = R₁ ++ (s, pre ++ [(sz₁, .client), (sz₂, v)] ++ post) :: R₂ := by
    rw [hr]; simp
  have hr1' : (l.av.tiles.fuse (s + runLen pre) .client).runs =
      R₁ ++ (s, pre ++ [(sz₁ + sz₂, .client)] ++ post) :: R₂ := by
    rw [hr']; simp
  have hlen : runLen [(sz₁ + sz₂, Use.client)] = runLen [(sz₁, .client), (sz₂, v)] := by
    simp [runLen]
  have h1 := ht.sizes _ (TopSt.mem_of_runs hr)
  have h2 := ht.sizes _ (TopSt.mem_of_runs_next hr)
  have hcoal0 := ht.runs_coal _ (by rw [hr]; exact List.mem_append_right _ (List.mem_cons_self ..))
  simp only at hcoal0
  rw [coalescedB_mid_used _ _ _ rfl] at hcoal0
  have hpost : coalescedB post = true := by
    have := hcoal0.2; rw [← List.nil_append ((sz₂, v) :: post), coalescedB_mid_used _ _ _ hvu] at this
    exact this.2
  have ht' : TopWF C (l.av.tiles.fuse (s + runLen pre) .client) := by
    refine ht.replace hr1 hr1' (by simp) hlen ?_ ?_ ?_ ?_ rfl rfl rfl
    · intro e he
      simp only [List.mem_singleton] at he; subst he
      simp only at h1 h2 ⊢
      refine ⟨?_, by omega⟩
      rw [Nat.add_mod, h1.1, h2.1]; simp
    · show [s + runLen pre].Sublist [s + runLen pre, s + runLen pre + sz₁]
      simp
    · show coalescedB (pre ++ [(sz₁ + sz₂, Use.client)] ++ post) = true
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
  have hv' : ∀ p : Use → Bool, p .client = false → p .internal = false →
      Chunk.view p (l.av.tiles.fuse (s + runLen pre) .client).heapChunks = Chunk.view p l.av.tiles.heapChunks := by
    intro p hp hp'
    refine TopSt.view_replace hr1 hr1' hlen ?_ (by simp [hp])
    intro e he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact hp
    · rcases hv with rfl | rfl
      · exact hp
      · exact hp'
  have hav := hw.arena.withTilesViews _ ht' (hv' _ rfl rfl) (hv' _ rfl rfl) (hv' _ rfl rfl)
  have hH := TopSt.heapChunks_of_runs hr1
  have hH' := TopSt.heapChunks_of_runs hr1'
  rw [hlen] at hH'
  have hlay : layout (s + runLen pre) [(sz₁, Use.client), (sz₂, v)] =
      [⟨s + runLen pre, sz₁, .client⟩, ⟨s + runLen pre + sz₁, sz₂, v⟩] := rfl
  have hlay' : layout (s + runLen pre) [(sz₁ + sz₂, Use.client)] =
      [⟨s + runLen pre, sz₁ + sz₂, .client⟩] := rfl
  rw [hlay] at hH; rw [hlay'] at hH'
  have hap : Apart ({ l with av := { l.av with tiles := l.av.tiles.fuse (s + runLen pre) .client } } : Local).spans := by
    have hold : Apart (l.av.tiles.spans ++ (l.av.heapSpans ++ l.shared.mm.chunks.map (fun c => (c.addr, c.size)))) :=
      (Local.spans_eq l) ▸ hw.apart
    rw [Local.spans_eq]
    show Apart ((l.av.tiles.fuse (s + runLen pre) .client).spans ++ (l.av.heapSpans ++ l.shared.mm.chunks.map (fun c => (c.addr, c.size))))
    unfold TopSt.spans at hold ⊢
    rw [List.append_assoc, hH] at hold
    rw [List.append_assoc, hH',
      show (l.av.tiles.fuse (s + runLen pre) .client).start = l.av.tiles.start from rfl,
      show (l.av.tiles.fuse (s + runLen pre) .client).top = l.av.tiles.top from rfl,
      show (l.av.tiles.fuse (s + runLen pre) .client).topSize = l.av.tiles.topSize from rfl]
    exact Apart.merge_chunks hold rfl rfl rfl
  have hcov : SpanCover l (fuse l (s + runLen pre) .client) := by
    refine spanCover_tiles rfl (TopSt.cover_chunks rfl rfl rfl fun c hc x h1 h2 => ?_)
    have hc' : c ∈ (l.av.tiles.fuse (s + runLen pre) .client).heapChunks := hc
    rw [hH'] at hc'
    have hold : ∀ d ∈ l.av.tiles.heapChunks, d.addr ≤ x → x < d.addr + d.size →
        InSpans l.av.tiles.spans x := fun d hd => InSpans.chunk hd
    rw [hH] at hold
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc' hold
    rcases hc' with (hc' | rfl) | hc'
    · exact hold c (.inl (.inl hc')) h1 h2
    · simp only at h1 h2
      by_cases hx : x < s + runLen pre + sz₁
      · exact hold _ (.inl (.inr (.inl rfl))) h1 hx
      · exact hold _ (.inl (.inr (.inr rfl))) (by simp only; omega) (by simp only; omega)
    · exact hold c (.inr hc') h1 h2
  refine ⟨hw.withAv' _ hav rfl rfl rfl
    (show (l.av.tiles.fuse (s + runLen pre) .client).old = [] ↔ l.av.tiles.old = [] by simp [TopSt.fuse]) hap,
    hcov, hr', ?_, ?_, ?_⟩
  · intro c hc hc1 hc2
    show c ∈ (l.av.tiles.fuse (s + runLen pre) .client).heapChunks
    have hc' : c ∈ l.av.tiles.heapChunks := hc
    rw [hH] at hc'; rw [hH']
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc' ⊢
    rcases hc' with (hc' | rfl | rfl) | hc'
    · exact .inl (.inl hc')
    · exact absurd rfl hc1
    · exact absurd rfl hc2
    · exact .inr hc'
  · show _ ∈ (l.av.tiles.fuse (s + runLen pre) .client).heapChunks
    rw [hH']; simp
  · refine ⟨((Chunk.view (· = .client) (TopSt.flat R₁ ++ layout s pre)) ++
      Chunk.view (· = .client) (layout (s + runLen pre + runLen [(sz₁, Use.client), (sz₂, v)]) post ++ TopSt.flat R₂)).map
        (fun c => (c.addr + C.hdr, usable C c false)), ?_, ?_⟩
    · unfold ArenaSt.out ArenaSt.chunks
      rw [hH]
      rcases hv with rfl | rfl
      · simp only [Chunk.view, List.filter_append, List.filter_cons, decide_true, ite_true,
          List.map_append, List.map_cons, usable, Bool.false_eq_true,
          ite_false, List.append_assoc, List.cons_append, List.nil_append]
        exact perm_mid2' _ _ _ _ _
      · simp only [Chunk.view, List.filter_append, List.filter_cons, decide_true, ite_true,
          List.map_append, List.map_cons, usable, Bool.false_eq_true,
          ite_false, List.append_assoc, List.cons_append, List.nil_append, reduceCtorEq, decide_false]
        exact perm_mid1' _ _ _ _
    · unfold ArenaSt.out ArenaSt.chunks
      simp only [fuse, withTiles]
      rw [hH']
      simp only [Chunk.view, List.filter_append, List.filter_cons, decide_true, ite_true,
        List.map_append, List.map_cons, usable, Bool.false_eq_true,
        ite_false, List.append_assoc, List.cons_append, List.nil_append]
      exact perm_mid1' _ _ _ _

end Algo

end Silmaril.Libc.Ptmalloc
