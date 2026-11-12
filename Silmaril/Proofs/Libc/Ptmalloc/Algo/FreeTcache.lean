module

public import Silmaril.Libc.Ptmalloc.Algo.Free.Defs
public import Silmaril.Libc.Ptmalloc.Algo.Leaf.Thms
public import Silmaril.Libc.Ptmalloc.Top.Thms

/-!
# ptmalloc algorithm: `_int_free`'s tcache path

`Algo.intFree_tcache`: for a lent-out chunk whose tcache bin has room and does not hold it,
`_int_free` is exactly `tcache_put` (`intFree_tcache_eq`), keeps `LocalWF` (from
`Algo.leafTcachePut`), touches only the thread, and the body's live set loses exactly the freed
payload (`live_tcPut`). This is the tcache case of `Task.algo.wfIntFree`, composed from the leaf
lemma and the live-set lemma; the other cases (fastbin, merge) compose the same way from
`Algo.leafFastPush` and `Task.algo.wfCoalesce`.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

variable {C : Config}

/-- Filtering out the members of `x :: P` erases `x` from a list without duplicates. -/
theorem filter_not_mem_cons {L P P' : List (Nat × Nat)} {x : Nat × Nat} (hL : L.Nodup)
    (hP' : P'.Perm (x :: P)) :
    L.filter (fun y => !P'.contains y) = (L.filter fun y => !P.contains y).erase x := by
  have hnd : (L.filter fun y => !P.contains y).Nodup := hL.filter _
  rw [hnd.erase_eq_filter, List.filter_filter]
  congr 1; funext y
  have : P'.contains y = (y == x || P.contains y) := by
    rw [Bool.eq_iff_iff]; simp only [List.contains_iff_mem, Bool.or_eq_true, beq_iff_eq]
    rw [hP'.mem_iff]; simp
  rw [this]; simp only [bne]; cases (y == x) <;> cases P.contains y <;> rfl

/-- The lent-out payloads of a well-formed arena have distinct entries. -/
theorem out_nodup {av : ArenaSt} (h : TopWF C av.tiles) : (av.out C).Nodup := by
  have hn := h.nodup
  unfold ArenaSt.out ArenaSt.chunks Chunk.view
  generalize av.tiles.heapChunks = cs at hn
  induction cs with
  | nil => exact List.nodup_nil
  | cons c cs ih =>
    rw [List.map_cons, List.nodup_cons] at hn
    simp only [List.filter_cons]
    split
    · rw [List.map_cons, List.nodup_cons]
      refine ⟨fun hm => hn.1 ?_, ih hn.2⟩
      obtain ⟨d, hd, hdc⟩ := List.mem_map.mp hm
      simp only [Prod.mk.injEq] at hdc
      have : d.addr = c.addr := by omega
      rw [← this]; exact List.mem_map_of_mem (List.mem_filter.mp hd).1
    · exact ih hn.2

/-- **The live set after a `tcache_put`** of a lent-out, not yet parked chunk: one payload less. -/
theorem live_tcPut {l : Local} {tc : TcacheSt} {c : Nat × Nat} {i : Nat} (hw : LocalWF C l)
    (ht : l.thread.tcache = some tc) (hi : i < C.tcacheBins)
    (hout : (c.1 + C.hdr, c.2 - C.sizeSz) ∈ l.av.out C)
    (hnp : (c.1 + C.hdr, c.2 - C.sizeSz) ∉ l.thread.parked C) :
    ((tcPut l c i).live C).Perm ((l.live C).erase (c.1 + C.hdr, c.2 - C.sizeSz)) := by
  have hput : tcPut l c i = { l with thread := { l.thread with tcache := some (tc.put c i) } } := by
    simp [tcPut, Local.tcachePut, ht]
  rw [hput]
  unfold Local.live
  have hP : (ThreadSt.parked C { l.thread with tcache := some (tc.put c i) }).Perm
      ((c.1 + C.hdr, c.2 - C.sizeSz) :: l.thread.parked C) := by
    simp only [ThreadSt.parked, ht, Option.map_some, Option.getD_some]
    exact TcacheSt.payloads_put hi
  simp only
  rw [filter_not_mem_cons (out_nodup hw.arena.tiles) hP]
  have hmem : (c.1 + C.hdr, c.2 - C.sizeSz) ∈ (l.av.out C).filter fun y => !(l.thread.parked C).contains y := by
    refine List.mem_filter.mpr ⟨hout, ?_⟩
    simpa [List.contains_iff_mem] using hnp
  rw [List.erase_append_left _ hmem]

/-- With distinct addresses, `find?` by address returns the member at that address. -/
theorem find?_addr {cs : List Chunk} (hn : (cs.map (·.addr)).Nodup) {ch : Chunk} (hch : ch ∈ cs) :
    cs.find? (fun d => decide (d.addr = ch.addr)) = some ch := by
  induction cs with
  | nil => cases hch
  | cons d cs ih =>
    rw [List.map_cons, List.nodup_cons] at hn
    rw [List.find?_cons]
    by_cases h : d.addr = ch.addr
    · have : d = ch := chunk_unique (cs := d :: cs) (by rw [List.map_cons, List.nodup_cons]; exact hn)
        (List.mem_cons_self ..) hch h
      simp [this]
    · simp only [h, decide_false]
      rcases List.mem_cons.mp hch with rfl | hch
      · exact absurd rfl h
      · exact ih hn.2 hch

/-- **`_int_free` on the tcache path is `tcache_put`.** -/
theorem intFree_tcache_eq {l : Local} {ch : Chunk} {tc : TcacheSt}
    (hf : l.av.tiles.find? ch.addr = some ch) (hcu : ch.use = .client)
    (hal : ch.addr % C.align = 0) (hb : ch.addr + ch.size < 2 ^ 64) (hmin : C.minSize ≤ ch.size)
    (hsa : ch.size % C.align = 0) (ht : l.thread.tcache = some tc) (hi : C.tidx ch.size < C.tcacheBins)
    (hnot : (ch.addr, ch.size) ∉ tc.bins (C.tidx ch.size))
    (hroom : (tc.bins (C.tidx ch.size)).length < C.tcacheCount) :
    intFree C l ch.addr = .ok (tcPut l (ch.addr, ch.size) (C.tidx ch.size)) := by
  have h1 : ¬ (ch.addr % C.align ≠ 0 ∨ 2 ^ 64 < ch.addr + ch.size) := by omega
  have h2 : ¬ (ch.size < C.minSize ∨ ch.size % C.align ≠ 0) := by omega
  simp [intFree, hf, hcu, ht, hi, hnot, hroom, h1, h2]; rfl

/-- **`_int_free`'s tcache path** (the tcache case of `Task.algo.wfIntFree`): a lent-out chunk of
the arena, not parked, whose tcache bin has room, is parked; `LocalWF` holds, only the thread
changes, and the live set loses exactly its payload. -/
theorem intFree_tcache (hC : C.Ok) {l : Local} (hw : LocalWF C l) {ch : Chunk}
    (hch : ch ∈ l.av.chunks) (hcu : ch.use = .client) {tc : TcacheSt}
    (ht : l.thread.tcache = some tc) (hi : C.tidx ch.size < C.tcacheBins)
    (hnot : (ch.addr, ch.size) ∉ tc.bins (C.tidx ch.size))
    (hroom : (tc.bins (C.tidx ch.size)).length < C.tcacheCount)
    (hnp : (ch.addr + C.hdr, ch.size - C.sizeSz) ∉ l.thread.parked C) :
    ∃ l', intFree C l ch.addr = .ok l' ∧ LocalWF C l' ∧
      Footprint.Within { arena := false, shared := false, kernel := false } l l' ∧
      (l'.live C).Perm ((l.live C).erase (ch.addr + C.hdr, ch.size - C.sizeSz)) := by
  have htw := hw.arena.tiles
  have hsz := htw.sizes ch hch
  have hal := htw.aligned ch hch
  have hb := htw.bound ch hch
  have hnn := htw.nonNull ch hch
  have hf : l.av.tiles.find? ch.addr = some ch := find?_addr htw.nodup hch
  refine ⟨_, intFree_tcache_eq hf hcu hal hb hsz.2 hsz.1 ht hi hnot hroom, ?_⟩
  have hput : l.tcachePut (ch.addr, ch.size) (C.tidx ch.size) =
      some (tcPut l (ch.addr, ch.size) (C.tidx ch.size)) := by
    simp [tcPut, Local.tcachePut, ht]
  obtain ⟨hw', hfp⟩ := leafTcachePut C l _ (ch.addr, ch.size) (C.tidx ch.size) hC hw hi rfl hsz.1
    hsz.2 hnn hal (fun tc' ht' => by rw [ht] at ht'; cases ht'; exact ⟨hnot, hroom⟩) hput
  refine ⟨hw', hfp, live_tcPut hw ht hi ?_ hnp⟩
  refine List.mem_map.mpr ⟨ch, List.mem_filter.mpr ⟨hch, by simp [hcu]⟩, ?_⟩
  simp [usable]

end Silmaril.Libc.Ptmalloc.Algo
