module

public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocMmap

/-!
# ptmalloc algorithm: `sysmalloc` from its parts

`Algo.sysmallocBody_of`, `Algo.sysmallocTotal_of`: `sysmalloc` from the proved `mmap` path and the
main-arena and non-main parts after it (`Task.algo.{sysMainBody, sysMainTotal, sysHeapBody,
sysHeapTotal}`).
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

variable {C : Config}

/-- **`Algo.sysmallocBody_of`**. -/
theorem sysmallocBody_of (C : Config) (hm : Task.algo.sysMainBody C) (hh : Task.algo.sysHeapBody C) :
    Task.algo.sysmallocBody C := by
  intro hC l l' n nb p hw hsp hi hnb hlt h
  unfold sysmalloc at h
  dsimp only at h
  have tailP : ∀ (tried : Bool) (l₁ : Local), MStep C l l₁ → l₁.av = l.av →
      (if l₁.isMain = true then sysmallocMain C l₁ nb else sysmallocHeap C l₁ nb tried) = .ok (p, l') →
      MBody C n l p l' := by
    intro tried l₁ hst hav h
    have hw₁ := hst.1
    have hsp₁ := hst.sp hC hw hsp
    have hi₁ := hst.2.2.1.init.trans hi
    have hlt₁ : topSz l₁.av.tiles < nb + C.minSize := by rw [hav]; exact hlt
    split at h
    · rename_i hmn
      exact MBody.of_step hC hw hsp hst (hm hC l₁ l' n nb p hw₁ hsp₁ hi₁ hmn hnb hlt₁ h)
    · rename_i hmn
      exact MBody.of_step hC hw hsp hst
        (hh hC l₁ l' n nb p tried hw₁ hsp₁ hi₁ (by simpa using hmn) hnb hlt₁ h)
  split at h
  · split at h
    · rename_i q l₁ hmm
      injection h with h; cases h
      exact sysmallocMmap_body hC hw hsp hi hnb hmm
    · rename_i l₁ hmm
      obtain ⟨k, rfl, h1, h2, h3⟩ := sysmallocMmap_none hmm
      exact tailP true _ (kernel_step hw hsp h1 h2 h3) rfl h
  · exact tailP false l (mstep_refl hw hsp) rfl h

/-- **`Algo.sysmallocTotal_of`**. -/
theorem sysmallocTotal_of (C : Config) (hm : Task.algo.sysMainTotal C) (hh : Task.algo.sysHeapTotal C) :
    Task.algo.sysmallocTotal C := by
  intro hC l n nb hw hsp hnb hlt
  unfold sysmalloc
  dsimp only
  have tailP : ∀ (tried : Bool) (l₁ : Local), MStep C l l₁ → l₁.av = l.av →
      ∃ r, (if l₁.isMain = true then sysmallocMain C l₁ nb else sysmallocHeap C l₁ nb tried) = .ok r := by
    intro tried l₁ hst hav
    have hw₁ := hst.1
    have hsp₁ := hst.sp hC hw hsp
    have hlt₁ : topSz l₁.av.tiles < nb + C.minSize := by rw [hav]; exact hlt
    split
    · rename_i hmn; exact hm hC l₁ n nb hw₁ hsp₁ hmn hnb hlt₁
    · rename_i hmn; exact hh hC l₁ n nb tried hw₁ hsp₁ (by simpa using hmn) hnb hlt₁
  split
  · split
    · exact ⟨_, rfl⟩
    · rename_i l₁ hmm
      obtain ⟨k, rfl, h1, h2, h3⟩ := sysmallocMmap_none hmm
      exact tailP true _ (kernel_step hw hsp h1 h2 h3) rfl
  · exact tailP false l (mstep_refl hw hsp) rfl

/-- A frame for a body that keeps the spans, the chunks, the heaps and everything outside the arena. -/
theorem Frame.of_same {l l' : Local} {freed : List (Nat × Nat)} (ha : l'.avAddr = l.avAddr)
    (hm : l'.isMain = l.isMain) (hsp : l'.spans = l.spans) (hch : l'.av.chunks = l.av.chunks)
    (hh : l'.av.heaps = l.av.heaps) (hk : l'.kernel = l.kernel) (hs : l'.shared = l.shared)
    (ht : l'.thread = l.thread) (hcov : ∀ r ∈ l.spans, l.kernel.Covers r) : Frame C l l' freed where
  avAddr := ha
  isMain := hm
  spatial r _ hc hap := by rw [hk, hsp]; exact ⟨hc, hap⟩
  covered r hr := by rw [hsp] at hr; rw [hk]; exact hcov r hr
  brkStart := by rw [hk]
  nonMain _ := by rw [hk, hs]; exact ⟨rfl, rfl⟩
  acct _ := by rw [hk, hs]; exact Nat.le_refl _
  init := by rw [hs]
  arenas := by rw [hs]; exact ⟨rfl, rfl, rfl⟩
  arena := by rw [ht]
  heaps h := by rw [hh]; exact h
  clients c hc _ _ := by rw [hch]; exact hc
  fresh tc' i e ht' he := by
    rw [ht] at ht'
    exact .inl ⟨tc', i, ht', he⟩

/-- Updating `max_system_mem` is an `MStep`. -/
theorem maxSys_step {l : Local} (hw : LocalWF C l) (hsp : LocalSp C l) (m : Nat) :
    MStep C l (withTiles l { l.av.tiles with maxSystemMem := m }) := by
  have hT := hw.arena.tiles
  have hT' : TopWF C { l.av.tiles with maxSystemMem := m } :=
    { sizes := hT.sizes, aligned := hT.aligned, nonNull := hT.nonNull, topAt := hT.topAt,
      topAligned := hT.topAligned, topMin := hT.topMin, coalesced := hT.coalesced,
      lastUsed := hT.lastUsed, coalescedOld := hT.coalescedOld, sysMem := hT.sysMem,
      sysMemBound := hT.sysMemBound, noHeap := hT.noHeap, nodup := hT.nodup, bound := hT.bound,
      topBound := hT.topBound }
  have hA := hw.arena.withTilesViews _ hT' rfl rfl rfl
  have hwl := hw.withAv' _ hA rfl rfl rfl Iff.rfl hw.apart
  exact ⟨hwl, List.Perm.refl _, Frame.of_same rfl rfl rfl rfl rfl rfl rfl rfl hsp.covered,
    fun tc _ _ ht he _ => ⟨tc, ht, he⟩, id⟩

/-- **`sysmalloc`'s final carve** is a body: `use_top`, or `ENOMEM` and 0. -/
theorem sysCarve_body (hC : C.Ok) {l : Local} (hw : LocalWF C l) (hsp : LocalSp C l) {n nb : Nat}
    (hnb : C.checkedRequest2size n = some nb) :
    MBody C n l (sysCarve C l nb).1 (sysCarve C l nb).2 := by
  have S := maxSys_step hw hsp (max l.av.tiles.systemMem l.av.tiles.maxSystemMem)
  have hw₀ := S.1
  have hsp₀ := S.sp hC hw hsp
  unfold sysCarve
  dsimp only
  split
  · rename_i h
    exact MBody.of_step hC hw hsp S (useTop_body hC hw₀ hsp₀ hnb h.1 h.2)
  · exact MBody.of_step hC hw hsp S (setErrno_body hw₀ hsp₀ n)

end Silmaril.Libc.Ptmalloc.Algo
