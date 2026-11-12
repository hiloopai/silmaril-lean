module

public import Silmaril.Proofs.Libc.Ptmalloc.Algo.Consolidate
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.Trim

/-!
# ptmalloc algorithm: `_int_free` (`Task.algo.wfIntFree`)

The three successful paths of `_int_free` on a lent-out, not parked chunk of the arena:

* **tcache** (`Algo.intFree_tcache`, thread only);
* **fastbin** (`Algo.leafFastPush`, components Top + Fastbins);
* **merge** (`freeMerge`): held `internal` (`relabelInternal_step`), coalesced
  (`Algo.coalesce_spec`), then `_int_free_maybe_consolidate`: `malloc_consolidate`
  (`Algo.wfConsolidate`) and `systrim`/`heap_trim` (`Algo.systrim_step`, `Algo.heapTrim_step`).

Each keeps `LocalWF`, the thread (except the tcache path) and the shared part, and the arena's
lent-out payloads lose exactly the freed one (`out_relabel_client`), so the view's live set does
(`live_of_out`).

`Algo.wfIntFree : ∀ C, Task.algo.wfIntFree C (ptmalloc C)`.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

variable {C : Config}

/-! ## The lent-out payloads under a relabelling of a client chunk -/

theorem map_relabelAt_of_not_mem {a : Nat} {u : Use} :
    ∀ {cs : List Chunk}, (∀ c ∈ cs, c.addr ≠ a) → cs.map (Chunk.relabelAt a u) = cs
  | [], _ => rfl
  | c :: cs, h => by
    rw [List.map_cons, Chunk.relabelAt_of_ne (h c (List.mem_cons_self ..)),
      map_relabelAt_of_not_mem fun d hd => h d (List.mem_cons_of_mem _ hd)]

theorem filter_client_relabel {d : Chunk} {u : Use} (hu : u ≠ .client) (hdu : d.use = .client) :
    ∀ {cs : List Chunk}, (cs.map (·.addr)).Nodup → d ∈ cs →
      Chunk.view (· = .client) (cs.map (Chunk.relabelAt d.addr u)) =
        (Chunk.view (· = .client) cs).erase d
  | [], _, h => by cases h
  | c :: cs, hn, hd => by
    rw [List.map_cons, List.nodup_cons] at hn
    by_cases hc : c.addr = d.addr
    · have hcd : c = d := chunk_unique (cs := c :: cs) (by rw [List.map_cons, List.nodup_cons]; exact hn)
        (List.mem_cons_self ..) hd hc
      subst hcd
      have hrest : ∀ e ∈ cs, e.addr ≠ c.addr := fun e he h => hn.1 (h ▸ List.mem_map_of_mem he)
      rw [List.map_cons, Chunk.relabelAt_of_eq rfl, map_relabelAt_of_not_mem hrest]
      simp [Chunk.view, hu, hdu]
    · have hd' : d ∈ cs := by
        rcases List.mem_cons.mp hd with rfl | h
        · exact absurd rfl hc
        · exact h
      rw [List.map_cons, Chunk.relabelAt_of_ne hc]
      have ih := filter_client_relabel hu hdu hn.2 hd'
      simp only [Chunk.view, List.filter_cons] at ih ⊢
      split
      · rw [ih, List.erase_cons_tail]; intro h; exact hc (by rw [beq_iff_eq] at h; rw [h])
      · exact ih

theorem map_erase_of_inj {α β : Type} [BEq α] [LawfulBEq α] [BEq β] [LawfulBEq β] {f : α → β} {x : α} :
    ∀ {L : List α}, (∀ y ∈ L, f y = f x → y = x) → (L.erase x).map f = (L.map f).erase (f x)
  | [], _ => rfl
  | y :: L, h => by
    by_cases hy : y = x
    · subst hy; simp
    · have hf : f y ≠ f x := fun e => hy (h y (List.mem_cons_self ..) e)
      rw [List.erase_cons_tail (by simpa using hy), List.map_cons, List.map_cons,
        List.erase_cons_tail (by simpa using hf), map_erase_of_inj fun z hz => h z (List.mem_cons_of_mem _ hz)]

theorem filter_erase_of {α : Type} [BEq α] [LawfulBEq α] (q : α → Bool) {x : α} (hx : q x = true) :
    ∀ (L : List α), (L.erase x).filter q = (L.filter q).erase x
  | [] => rfl
  | y :: L => by
    by_cases hy : y = x
    · subst hy; simp [hx]
    · rw [List.erase_cons_tail (by simpa using hy), List.filter_cons, List.filter_cons]
      split
      · rw [List.erase_cons_tail (by simpa using hy), filter_erase_of q hx L]
      · exact filter_erase_of q hx L

/-- **Relabelling a lent-out chunk** removes exactly its payload from the arena's lent-out
payloads. -/
theorem out_relabel_client {av av' : ArenaSt} (hn : (av.tiles.heapChunks.map (·.addr)).Nodup)
    {d : Chunk} (hd : d ∈ av.tiles.heapChunks) (hdu : d.use = .client) {u : Use} (hu : u ≠ .client)
    (ht : av'.tiles.heapChunks = av.tiles.heapChunks.map (Chunk.relabelAt d.addr u)) :
    av'.out C = (av.out C).erase (d.addr + C.hdr, usable C d false) := by
  unfold ArenaSt.out ArenaSt.chunks
  rw [ht, filter_client_relabel hu hdu hn hd]
  refine map_erase_of_inj (f := fun c : Chunk => (c.addr + C.hdr, usable C c false)) fun y hy he => ?_
  simp only [Prod.mk.injEq] at he
  exact chunk_unique hn (List.mem_filter.mp hy).1 hd (by omega)

/-- The view's live set after an arena change that removes one lent-out, not parked payload. -/
theorem live_of_out {l l' : Local} {x : Nat × Nat} (hth : l'.thread = l.thread) (hsh : l'.shared = l.shared)
    (hout : (l'.av.out C).Perm ((l.av.out C).erase x)) (hx : x ∈ l.arenaLive C) :
    (l'.live C).Perm ((l.live C).erase x) := by
  unfold Local.live
  rw [hth, hsh]
  have hq : (fun pu => !(l.thread.parked C).contains pu) x = true := (List.mem_filter.mp hx).2
  refine (List.Perm.append_right _ ((hout.filter _).trans (List.Perm.of_eq (filter_erase_of (fun pu => !(l.thread.parked C).contains pu) hq (l.av.out C))))).trans ?_
  have hx' : x ∈ (l.av.out C).filter (fun pu => !(l.thread.parked C).contains pu) := hx
  rw [List.erase_append_left _ hx']

theorem within_empty {l l' : Local} (h1 : l'.avAddr = l.avAddr) (h2 : l'.isMain = l.isMain) :
    Footprint.Within {} l l' :=
  ⟨h1, h2, fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide),
    fun h => absurd h (by decide)⟩

/-! ## The merge path -/

/-- The relation of the merge path's states to the start: same arena address and kind, same
thread and shared part, the lent-out payloads up to order. -/
structure Keeps (C : Config) (l l' : Local) : Prop where
  avAddr : l'.avAddr = l.avAddr
  isMain : l'.isMain = l.isMain
  thread : l'.thread = l.thread
  shared : l'.shared = l.shared
  out : (l'.av.out C).Perm (l.av.out C)

theorem Keeps.trans {l l₁ l₂ : Local} (h₁ : Keeps C l l₁) (h₂ : Keeps C l₁ l₂) : Keeps C l l₂ :=
  ⟨h₂.avAddr.trans h₁.avAddr, h₂.isMain.trans h₁.isMain, h₂.thread.trans h₁.thread,
    h₂.shared.trans h₁.shared, h₂.out.trans h₁.out⟩

theorem Keeps.refl (l : Local) : Keeps C l l := ⟨rfl, rfl, rfl, rfl, List.Perm.refl _⟩

theorem Keeps.of_eq {l l' : Local} (h : l' = { l with av := l'.av, kernel := l'.kernel })
    (hout : l'.av.out C = l.av.out C) : Keeps C l l' := by
  rw [h]; exact ⟨rfl, rfl, rfl, rfl, by rw [hout]⟩

/-- **`_int_free_maybe_consolidate`** keeps `LocalWF` and `Keeps`. -/
theorem maybeConsolidate_spec (hC : C.Ok) {l l' : Local} (hw : LocalWF C l) {size : Nat}
    (h : maybeConsolidate C l size = .ok l') : LocalWF C l' ∧ Keeps C l l' := by
  have tail : ∀ l₂, LocalWF C l₂ → Keeps C l l₂ →
      (if l₂.isMain = true then
        (if l₂.shared.mm.mp.trimThreshold ≤ l₂.av.tiles.topSize then systrim C l₂ C.topPad else pure l₂)
       else heapTrim C l₂ C.topPad) = .ok l' → LocalWF C l' ∧ Keeps C l l' := by
    intro l₂ hw2 hk2 h
    have hflag : ∀ l₃ : Local, l₃.av.fast = l₂.av.fast → LocalWF C l₃.hf → LocalWF C l₃ := by
      intro l₃ hf hw3
      exact hw3.of_hf fun hne => by rw [hf] at hne ⊢; exact hw2.arena.fast.flag hne
    split at h
    · split at h
      · obtain ⟨hw3, he, hav, hch⟩ := systrim_step hC hw2.hf ‹_› h
        have hf3 : l'.av.fast = l₂.av.fast := by rw [hav]
        exact ⟨hflag l' hf3 hw3, hk2.trans (Keeps.of_eq he (ArenaSt.out_congr (by rw [hch])))⟩
      · cases h; exact ⟨hw2, hk2⟩
    · rename_i hm
      have hm' : l₂.isMain = false := by simpa using hm
      obtain ⟨hw3, he, hch, hf3⟩ := heapTrim_step hC hw2.hf hm' h
      exact ⟨hflag l' hf3 hw3, hk2.trans (Keeps.of_eq he (ArenaSt.out_congr (by rw [hch])))⟩
  unfold maybeConsolidate at h
  dsimp only at h
  split at h
  · cases h; exact ⟨hw, Keeps.refl l⟩
  split at h
  · cases hc : consolidate C l with
    | error e => rw [hc] at h; cases h
    | ok l₂ =>
      rw [hc, ok_bind] at h
      obtain ⟨hw2, hfp, hout, -⟩ := wfConsolidate C hC l l₂ hw hc
      obtain ⟨h1, h2', h3, h4, h5, h6⟩ := hfp
      exact tail l₂ hw2 ⟨h1, h2', h4 rfl, h5 rfl, hout⟩ h
  · exact tail l hw (Keeps.refl l) h

/-- **Holding a lent-out chunk** (`internal`) keeps `LocalWF` and removes its payload. -/
theorem relabelInternal_step {l : Local} (hw : LocalWF C l) {d : Chunk} (hd : d ∈ l.av.tiles.heapChunks)
    (hdu : d.use = .client) :
    LocalWF C (l.relabel d.addr .internal) ∧
      (l.relabel d.addr .internal).av.out C = (l.av.out C).erase (d.addr + C.hdr, usable C d false) := by
  have ht := hw.arena.tiles
  have hn := ht.nodup
  have ht' := ht.relabel (a := d.addr) (u := .internal) rfl
  have hav := hw.arena.withTilesViews _ ht' (view_relabel_internal hn hd (by rw [hdu]; rfl) rfl)
    (view_relabel_internal hn hd (by rw [hdu]; rfl) rfl) (view_relabel_internal hn hd (by rw [hdu]; rfl) rfl)
  exact ⟨hw.withAv _ hav rfl rfl rfl rfl (TopSt.relabel_old_nil ..) (TopSt.spans_relabel ..),
    out_relabel_client hn hd hdu (by simp) (TopSt.heapChunks_relabel ..)⟩

/-- **The merge path** (`_int_free_merge_chunk`). -/
theorem freeMerge_spec (hC : C.Ok) {l l' : Local} (hw : LocalWF C l) {d : Chunk}
    (hd : d ∈ l.av.tiles.heapChunks) (hdu : d.use = .client) (h : freeMerge C l d.addr = .ok l') :
    LocalWF C l' ∧ l'.avAddr = l.avAddr ∧ l'.isMain = l.isMain ∧ l'.thread = l.thread ∧
      l'.shared = l.shared ∧ (l'.av.out C).Perm ((l.av.out C).erase (d.addr + C.hdr, usable C d false)) := by
  obtain ⟨hw1, hout1⟩ := relabelInternal_step hw hd hdu
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
    obtain ⟨hw3, hk⟩ := maybeConsolidate_spec hC hw2 h
    have he2 := hst.eq
    refine ⟨hw3, hk.avAddr.trans (by rw [he2]; rfl), hk.isMain.trans (by rw [he2]; rfl),
      hk.thread.trans (by rw [he2]; rfl), hk.shared.trans (by rw [he2]; rfl), ?_⟩
    refine hk.out.trans ?_
    rw [hst.out, hout1]

/-! ## `_int_free` -/

/-- **`Algo.wfIntFree`**. -/
theorem wfIntFree (C : Config) : Task.algo.wfIntFree C (ptmalloc C) := by
  intro hC l l' p u hw hpu h
  -- the chunk
  have hpu' := hpu
  unfold Local.arenaLive at hpu'
  obtain ⟨hout, hnp⟩ := List.mem_filter.mp hpu'
  obtain ⟨ch, hchv, hpe⟩ := List.mem_map.mp hout
  obtain ⟨hch, hcu⟩ := List.mem_filter.mp hchv
  have hcu' : ch.use = .client := by simpa using hcu
  simp only [Prod.mk.injEq] at hpe
  obtain ⟨rfl, rfl⟩ := hpe
  have hpc : ch.addr + C.hdr - C.hdr = ch.addr := by omega
  simp only [ptmalloc] at h
  rw [hpc] at h
  have htw := hw.arena.tiles
  have hsz := htw.sizes ch hch
  have hal := htw.aligned ch hch
  have hb := htw.bound ch hch
  have hf : l.av.tiles.find? ch.addr = some ch := find?_addr htw.nodup hch
  have h1 : ¬ (ch.addr % C.align ≠ 0 ∨ 2 ^ 64 < ch.addr + ch.size) := by omega
  have h2 : ¬ (ch.size < C.minSize ∨ ch.size % C.align ≠ 0) := by omega
  have hnp' : (ch.addr + C.hdr, ch.size - C.sizeSz) ∉ l.thread.parked C := by
    simpa [List.contains_iff_mem, usable] using hnp
  have hx : (ch.addr + C.hdr, usable C ch false) ∈ l.arenaLive C := hpu
  have hus : usable C ch false = ch.size - C.sizeSz := by simp [usable]
  -- the fastbin and merge paths, after the tcache
  have hrest : (if ch.size ≤ C.maxFast then
        (if (l.av.fast.lists (C.fidx ch.size)).head? = some ch.addr then
          (Except.error Abort.doubleFreeFasttop : Res Local)
         else .ok (l.fastPush ch.addr (C.fidx ch.size)))
       else freeMerge C l ch.addr) = .ok l' →
      LocalWF C l' ∧ Footprint.Within {} l l' ∧
        (l'.live C).Perm ((l.live C).erase (ch.addr + C.hdr, usable C ch false)) := by
    intro hr
    split at hr
    · rename_i hmf
      split at hr
      · cases hr
      · cases hr
        have hfi : C.fidx ch.size < C.nFast := by
          have := hC.fast; have h8 := hC.sizeSz; unfold Config.fidx at this ⊢; rw [h8] at this ⊢; omega
        obtain ⟨hw', hfp⟩ := leafFastPush hw hch rfl (.inl hcu') ⟨rfl, hmf, hfi⟩
        refine ⟨hw', within_empty hfp.1 hfp.2.1, ?_⟩
        refine live_of_out rfl rfl (List.Perm.of_eq ?_) hx
        exact out_relabel_client htw.nodup hch hcu' (by simp) (TopSt.heapChunks_relabel ..)
    · obtain ⟨hw', h1, h2, h3, h4, h5⟩ := freeMerge_spec hC hw hch hcu' hr
      exact ⟨hw', within_empty h1 h2, live_of_out h3 h4 h5 hx⟩
  cases htc : l.thread.tcache with
  | none =>
    simp [intFree, hf, hcu', htc, h1, h2] at h
    exact hrest h
  | some tc =>
    by_cases hi : C.tidx ch.size < C.tcacheBins
    · by_cases hin : (ch.addr, ch.size) ∈ tc.bins (C.tidx ch.size)
      · simp [intFree, hf, hcu', htc, h1, h2, hi, hin] at h
        cases h
      · by_cases hroom : (tc.bins (C.tidx ch.size)).length < C.tcacheCount
        · obtain ⟨l₀, h0, hw0, hfp0, hlive0⟩ := intFree_tcache hC hw hch hcu' htc hi hin hroom hnp'
          rw [h0] at h; cases h
          refine ⟨hw0, within_empty hfp0.1 hfp0.2.1, ?_⟩
          rw [hus]; exact hlive0
        · simp [intFree, hf, hcu', htc, h1, h2, hi, hin, hroom] at h
          exact hrest h
    · simp [intFree, hf, hcu', htc, h1, h2, hi] at h
      exact hrest h

end Silmaril.Libc.Ptmalloc.Algo
