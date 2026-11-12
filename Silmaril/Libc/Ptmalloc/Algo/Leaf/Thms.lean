module

public import Silmaril.Libc.Ptmalloc.Algo.Defs
public import Silmaril.Libc.Ptmalloc.Tcache.Thms

/-!
# ptmalloc algorithm: the thread-only leaf lemmas

`Algo.leafTcacheGet : Task.algo.leafTcacheGet` and `Algo.leafTcachePut : Task.algo.leafTcachePut`
(what `x86sim` needs first): `tcache_get`/`tcache_put` keep `LocalWF`, touch only the thread,
and move one payload between the thread's parked set and the caller. They follow from the
tcache component's lemmas (`Silmaril.Libc.Ptmalloc.Tcache.Thms`) and `LocalWF.withThread` (a change
of the thread part alone needs only the thread's invariant).
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc

/-- A view's spans: the tiling's, the heaps', the `mmap`ed chunks'. -/
theorem Local.spans_eq (l : Local) : l.spans =
    l.av.tiles.spans ++ (l.av.heapSpans ++ l.shared.mm.chunks.map (fun c => (c.addr, c.size))) := by
  simp only [Local.spans, ArenaSt.spans, List.append_assoc]

/-- `HeapWF` reads only the heaps, the reservation, the start, the end of top and `system_mem`
(bounded above). -/
theorem HeapWF.congr {C : Config} {av av' : ArenaSt} (h : HeapWF C av)
    (hh : av'.heaps = av.heaps) (hr : av'.reserve = av.reserve) (hs : av'.tiles.start = av.tiles.start)
    (he : av'.tiles.top + av'.tiles.topSize = av.tiles.top + av.tiles.topSize)
    (hsm : av'.tiles.systemMem ≤ av.tiles.systemMem) : HeapWF C av' where
  cur := by
    obtain ⟨a, b, rest, h1, h2, h3, h4⟩ := h.cur
    exact ⟨a, b, rest, hh.trans h1, hs ▸ h2, he.trans h3, hr ▸ h4⟩
  addrs hp hm := h.addrs hp (hh ▸ hm)
  sysMem := hh ▸ Nat.le_trans hsm h.sysMem

/-- `HeapWF.cur` at the known current heap. -/
theorem HeapWF.cur_of {C : Config} {av : ArenaSt} (h : HeapWF C av) {hb hs : Nat}
    {rest : List (Nat × Nat)} (hh : av.heaps = (hb, hs) :: rest) :
    hb < av.tiles.start ∧ av.tiles.top + av.tiles.topSize = hb + hs ∧
      hs + av.reserve = C.heapMaxSize := by
  obtain ⟨a, b, r, e, h1, h2, h3⟩ := h.cur
  rw [hh] at e
  injection e with e1 e2
  injection e1 with e3 e4
  subst e3 e4
  exact ⟨h1, h2, h3⟩

/-- **A thread-only change keeps `LocalWF`** given the new tcache's invariant (and, before
`ptmalloc_init`, no tcache). -/
theorem LocalWF.withThread {C : Config} {l : Local} (h : LocalWF C l) (t : ThreadSt)
    (ht : ∀ tc, t.tcache = some tc → TcacheWF C tc)
    (hi : l.shared.init = false → t.tcache = none) : LocalWF C { l with thread := t } where
  arena := h.arena
  shared := h.shared
  tcache := ht
  main := h.main
  init := fun h0 => ⟨(h.init h0).1, (h.init h0).2.1, hi h0⟩
  apart := h.apart
  mmSize := h.mmSize
  heap := h.heap
  sysMain := h.sysMain

namespace Algo

/-- `Local.tcacheGet` unfolded. -/
theorem tcacheGet_eq {C : Config} {l l' : Local} {i p : Nat} (h : l.tcacheGet C i = some (p, l')) :
    ∃ tc tc', l.thread.tcache = some tc ∧ tc.get C i = some (p, tc') ∧
      l' = { l with thread := { l.thread with tcache := some tc' } } := by
  unfold Local.tcacheGet at h
  cases ht : l.thread.tcache with
  | none => rw [ht] at h; cases h
  | some tc =>
    rw [ht] at h
    cases hg : tc.get C i with
    | none => simp [hg] at h
    | some r =>
      obtain ⟨p', tc'⟩ := r
      simp only [Option.bind_some, hg, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨tc, tc', rfl, hg, rfl⟩

/-- **`Algo.leafTcacheGet`**: `tcache_get` keeps `LocalWF`, touches only the thread, and returns
one parked payload (aligned). -/
theorem leafTcacheGet : Task.algo.leafTcacheGet := by
  intro C l l' i p hC hw h
  obtain ⟨tc, tc', ht, hg, rfl⟩ := tcacheGet_eq h
  have htw := hw.tcache tc ht
  refine ⟨hw.withThread _ ?_ ?_, by simp [Footprint.Within], ?_⟩
  · intro x hx; cases hx; exact TcacheSt.wf_get htw hg
  · intro h0; have := (hw.init h0).2.2; rw [ht] at this; cases this
  · obtain ⟨u, hu⟩ := TcacheSt.payloads_get htw hg
    obtain ⟨c, rest, hb, rfl, -⟩ := TcacheSt.get_eq hg
    refine ⟨u, ?_, ?_⟩
    · simpa [ThreadSt.parked, ht] using hu
    · have hc := (htw.nonNull i c (by rw [hb]; exact List.mem_cons_self ..)).2
      simp only [Config.hdr, hC.align, hC.sizeSz] at hc ⊢; omega

/-- **`Algo.leafTcachePut`**: `tcache_put` of a fitting chunk into a bin with room keeps
`LocalWF` and touches only the thread. -/
theorem leafTcachePut : Task.algo.leafTcachePut := by
  intro C l l' c i hC hw hi hidx hal hmin hnn hca hfit h
  unfold Local.tcachePut at h
  cases ht : l.thread.tcache with
  | none => rw [ht] at h; cases h
  | some tc =>
    rw [ht] at h
    simp only [Option.map_some, Option.some.injEq] at h
    subst h
    have htw := hw.tcache tc ht
    obtain ⟨hnot, hroom⟩ := hfit tc ht
    refine ⟨hw.withThread _ ?_ ?_, by simp [Footprint.Within]⟩
    · intro x hx; cases hx
      exact TcacheSt.wf_put htw hi hidx hal hmin hnn hca hnot hroom
    · intro h0; have := (hw.init h0).2.2; rw [ht] at this; cases this

end Algo

end Silmaril.Libc.Ptmalloc
