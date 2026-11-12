module

public import Silmaril.Libc.Ptmalloc.Algo.Tasks.Defs

/-!
# ptmalloc algorithm: the load-time world is well formed

`Algo.initWF : ∀ C, Task.algo.initWF C`: `initWorld` (one thread, `main_arena` without a heap,
`mp_` at its defaults, nothing live) satisfies `WorldWF`. With `Algo.ptmalloc_safeMF` this
discharges the load-time hypotheses of the institution reduction.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

/-- The empty arena of `initWorld`. -/
theorem arenaWF_empty (C : Config) :
    ArenaWF C { tiles := { start := 0, chunks := [], top := 0, topSize := 0, noncontig := false,
                           systemMem := 0, maxSystemMem := 0 }
                fast := { lists := fun _ => [], haveFast := false }
                bins := { lists := fun _ => [], binmap := fun _ => false }
                unsorted := { list := [], lastRem := 0 } } where
  tiles :=
    { sizes := by simp [TopSt.heapChunks, layout]
      aligned := by simp [TopSt.heapChunks, layout]
      nonNull := by simp [TopSt.heapChunks, layout]
      topAt := fun h => absurd rfl h
      topAligned := by simp
      topMin := fun h => absurd rfl h
      coalesced := rfl
      lastUsed := by simp
      coalescedOld := by simp
      sysMem := by simp [TopSt.heapChunks, layout]
      sysMemBound := by decide
      noHeap := fun _ => ⟨rfl, rfl⟩
      nodup := by simp [TopSt.heapChunks, layout]
      bound := by simp [TopSt.heapChunks, layout]
      topBound := fun h => absurd rfl h }
  fast :=
    { exact := fun i x => by simp [ArenaSt.fastView, ArenaSt.chunks, TopSt.heapChunks, layout, Chunk.view]
      nodup := fun _ => List.nodup_nil
      size := by simp [ArenaSt.fastView, ArenaSt.chunks, TopSt.heapChunks, layout, Chunk.view]
      flag := fun ⟨_, h⟩ => absurd rfl h }
  bins :=
    { exact := fun i _ x => by simp [ArenaSt.sortedView, ArenaSt.chunks, TopSt.heapChunks, layout, Chunk.view]
      outside := fun _ _ => rfl
      nodup := fun _ => List.nodup_nil
      size := by simp [ArenaSt.sortedView, ArenaSt.chunks, TopSt.heapChunks, layout, Chunk.view]
      sorted := fun _ _ => List.Pairwise.nil
      binmap := fun _ h => absurd rfl h }
  unsorted :=
    { exact := fun x => by simp [ArenaSt.unsortedView, ArenaSt.chunks, TopSt.heapChunks, layout, Chunk.view]
      nodup := List.nodup_nil
      size := by simp [ArenaSt.unsortedView, ArenaSt.chunks, TopSt.heapChunks, layout, Chunk.view]
      lastRemBound := by decide }
  internal := by simp [ArenaSt.chunks, TopSt.heapChunks, layout]

/-- **`Algo.initWF`**: the load-time world is well formed and has nothing live. -/
theorem initWF (C : Config) : Task.algo.initWF C := by
  intro hC ma tid brk o _ _ _
  have hmax := hC.words
  have hthr := hC.thresholds
  have hdyn := hC.dynThreshold
  refine ⟨?_, ?_⟩
  · refine
      { main := by simp [initWorld]
        arenas := fun a => by
          by_cases h : a = ma <;> simp [initWorld, World.arenaAddrs, h]
        arenaWF := fun a av h => by
          simp only [initWorld] at h
          split at h
          · cases h; exact arenaWF_empty C
          · cases h
        shared :=
          { mm :=
              { mpBound := by simp only [initWorld]; refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
                trimMin := by simp [initWorld]
                use := by simp [initWorld]
                page := by simp [initWorld]
                nonNull := by simp [initWorld]
                nodup := by simp [initWorld]
                mem := by simp [initWorld] }
            narenas := rfl
            freeListSub := by simp [initWorld] }
        locals := fun t a l ht hl => by
          simp only [World.local?, initWorld] at hl
          split at hl
          · rename_i ha
            simp only [Option.map_some, Option.some.injEq] at hl
            subst hl; subst ha
            exact
              { arena := arenaWF_empty C
                shared :=
                  { mm :=
                      { mpBound := by simp only; refine ⟨?_, ?_, ?_, ?_⟩ <;> omega
                        trimMin := by simp
                        use := by simp
                        page := by simp
                        nonNull := by simp
                        nodup := by simp
                        mem := by simp }
                    narenas := rfl
                    freeListSub := by simp }
                tcache := fun tc h => by simp at h
                main := fun _ => ⟨⟨Iff.rfl, fun _ => ⟨rfl, rfl⟩⟩, ⟨‹_›, Nat.le_refl _, ‹_›, fun h => absurd rfl h⟩⟩
                init := fun _ => ⟨rfl, rfl, rfl⟩
                apart := by
                  simp [Apart, Local.spans, ArenaSt.spans, ArenaSt.heapSpans, TopSt.spans, TopSt.heapChunks, layout]
                mmSize := by simp
                heap := fun h => by simp at h
                sysMain := fun _ => by simp }
          · simp at hl
        arenaNodup := by simp [World.arenaAddrs, initWorld]
        apart := ⟨by simp [World.spans, World.arenaAddrs, initWorld, ArenaSt.spans, ArenaSt.heapSpans, TopSt.spans,
            TopSt.heapChunks, layout],
          by simp [World.spans, World.arenaAddrs, initWorld, ArenaSt.spans, ArenaSt.heapSpans, TopSt.spans, TopSt.heapChunks,
            layout]⟩
        mmSize := by simp [initWorld]
        parked := fun t tc ht htc => by simp [initWorld] at htc
        parkedOnce := by simp [initWorld, ThreadSt.parked]
        tidsNodup := by simp [initWorld]
        threadArena := fun t a _ h => by simp [initWorld] at h
        covered := by
          simp [World.spans, World.arenaAddrs, initWorld, ArenaSt.spans, ArenaSt.heapSpans, TopSt.spans,
            TopSt.heapChunks, layout]
        structs := fun a ha => by
          simp only [World.arenaAddrs, initWorld, List.mem_cons, List.not_mem_nil, or_false] at ha
          subst ha
          refine ⟨.inr ⟨(a, C.stateSize), by simp [initWorld], Nat.le_refl _, ?_⟩, ?_⟩
          · have := hC.arena.1; simp only; omega
          · simp [Away, World.spans, World.arenaAddrs, initWorld, ArenaSt.spans, ArenaSt.heapSpans, TopSt.spans,
              TopSt.heapChunks, layout]
        heaps := fun a av h hne => by
          simp only [initWorld] at h hne
          split at h
          · exact absurd ‹_› hne
          · cases h }
  · simp [World.live, initWorld, World.arenaAddrs, ArenaSt.out, ArenaSt.chunks, TopSt.heapChunks,
      layout, Chunk.view, SharedSt.live, ThreadSt.parked]

end Silmaril.Libc.Ptmalloc.Algo
