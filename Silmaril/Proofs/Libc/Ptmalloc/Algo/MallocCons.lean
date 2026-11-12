module

public import Silmaril.Proofs.Libc.Ptmalloc.Algo.FreeBody
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocHeadPaths

/-!
# ptmalloc algorithm: `malloc_consolidate` for `_int_malloc`

`Algo.consolidateBody : Task.algo.consolidateBody C`, `Algo.consolidateTotal :
Task.algo.consolidateTotal C`. `malloc_consolidate` changes the arena alone (`ConsStep`): the
lent-out payloads are the same (`ConsStep.out`), so the live set, the thread's tcache and every
client chunk stay; its bytes are bytes the view owned before (`ConsStep.cover`), so the `Frame`
is `frame_of`'s; and `have_fastchunks`, cleared on entry, is never raised again
(`ConsStep.fastOff`).

Hence `Algo.bodyMalloc_cons`, `Algo.totalMalloc_cons`: `Task.algo.bodyMalloc` and
`Task.algo.totalMalloc` conditional only on `sysmalloc`'s two parts.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

variable {C : Config}

/-- A client chunk survives an arena change that keeps the lent-out payloads. -/
theorem clients_of_out_eq (hC : C.Ok) {l l' : Local} (hw : LocalWF C l) (hw' : LocalWF C l')
    (hout : l'.av.out C = l.av.out C) :
    ∀ c ∈ l.av.chunks, c.use = .client → c ∈ l'.av.chunks := by
  intro c hc hcu
  have hy : (c.addr + C.hdr, c.size - C.sizeSz) ∈ l.av.out C := mem_out.mpr ⟨c, hc, hcu, rfl⟩
  rw [← hout] at hy
  obtain ⟨d, hd, hdu, hde⟩ := mem_out.mp hy
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

/-- **`Algo.consolidateTotal`**: `malloc_consolidate` does not abort. -/
theorem consolidateTotal (C : Config) : Task.algo.consolidateTotal C :=
  fun _ _ hw _ => consolidate_ok hw

/-- **`Algo.consolidateBody`**. -/
theorem consolidateBody (C : Config) : Task.algo.consolidateBody C := by
  intro hC l l' hw hsp h
  have hw' : LocalWF C l' := (wfConsolidate C hC l l' hw h).1
  have hst := consolidate_step hw h
  have hoff : l'.av.fast.haveFast = false := by
    have h0 := h
    unfold consolidate at h0
    have hw0 : LocalWF C ({ l with av := { l.av with fast := { l.av.fast with haveFast := false } } } :
        Local).hf := hw.hf
    exact (consolidate_fold _ hw0 h0).1.fastOff rfl
  have he := hst.eq
  have hth : l'.thread = l.thread := by rw [he]
  have hsh : l'.shared = l.shared := by rw [he]
  have hav : l'.avAddr = l.avAddr := by rw [he]
  have hlive : l'.live C = l.live C := by
    unfold Local.live; rw [hst.out, hth, hsh]
  refine ⟨⟨hw', List.Perm.of_eq hlive,
    frame_of hsp hw'.apart hav hsh (by rw [hth]) hst.shrink
      (fun c hc hcu _ => clients_of_out_eq hC hw hw' hst.out c hc hcu)
      (fun tc' i e htc he' => .inl ⟨tc', i, by rw [← hth]; exact htc, he'⟩),
    fun tc i e htc he' _ => ⟨tc, by rw [hth]; exact htc, he'⟩,
    fun h0 => by rw [hth]; exact h0⟩, hoff⟩

/-- **`Task.algo.bodyMalloc`** from `sysmalloc`'s two parts. -/
theorem bodyMalloc_cons (C : Config) (hmain : Task.algo.sysMainBody C)
    (hheap : Task.algo.sysHeapBody C) : Task.algo.bodyMalloc C :=
  bodyMalloc_rest C (consolidateBody C) hmain hheap

/-- **`Task.algo.totalMalloc`** from `sysmalloc`'s two parts. -/
theorem totalMalloc_cons (C : Config) (hmainT : Task.algo.sysMainTotal C)
    (hheapT : Task.algo.sysHeapTotal C) : Task.algo.totalMalloc C :=
  totalMalloc_rest C (consolidateBody C) (consolidateTotal C) hmainT hheapT

end Silmaril.Libc.Ptmalloc.Algo
