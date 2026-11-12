module

public import Silmaril.Proofs.Libc.Ptmalloc.Algo.ReallocBody

/-!
# ptmalloc algorithm: `mremap_chunk`

`Algo.mremap_spec` (the kernel's `mremap`) and `Algo.mremap_body`: a moved `mmap`ed chunk is a
body step: well formed, a `Frame` that frees the old payload, the live set the old `mmap`ed
payload replaced by the new one (the new mapping is fresh kernel memory, `fresh_away`).
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

variable {C : Config}

/-- **The kernel's `mremap`**: the break kept; refused (the maps kept), or a new place for the
mapping, placeable once the old mapping is gone. -/
theorem mremap_spec (k : KernelSt) (al a n n' : Nat) :
    (k.mremap al a n n').2.brkStart = k.brkStart ∧ (k.mremap al a n n').2.brk = k.brk ∧
      (((k.mremap al a n n').1 = none ∧ (k.mremap al a n n').2.maps = k.maps) ∨
        ∃ a', (k.mremap al a n n').1 = some a' ∧
          (k.mremap al a n n').2.maps = (a', n') :: (k.munmap a n).maps ∧
          (k.munmap a n).Placeable al a' n') := by
  unfold KernelSt.mremap KernelSt.ask
  cases k.oracle.answer k.asked with
  | refuse => simp
  | ok a' =>
    simp only
    split
    · rename_i hp
      exact ⟨rfl, rfl, .inr ⟨a', rfl, rfl, by
        simpa [KernelSt.Placeable, KernelSt.Free, KernelSt.total, KernelSt.munmap] using hp⟩⟩
    · exact ⟨rfl, rfl, .inl ⟨rfl, rfl⟩⟩

/-- The view after a granted `mremap_chunk` of `ch` to `s` bytes at `a`. -/
def mmMove (l : Local) (k : KernelSt) (ch : Chunk) (a s : Nat) : Local :=
  { l with
    kernel := k
    shared := { l.shared with mm :=
      { chunks := ⟨a, s, ch.use⟩ :: l.shared.mm.chunks.erase ch
        mp := { l.shared.mm.mp with
          mmappedMem := l.shared.mm.mp.mmappedMem + s - ch.size
          maxMmappedMem := max (l.shared.mm.mp.mmappedMem + s - ch.size) l.shared.mm.mp.maxMmappedMem } } } }

/-- **A granted `mremap_chunk`** of a live `mmap`ed chunk `ch` to `s` bytes at `a`. -/
theorem mremap_body (hC : C.Ok) {l : Local} (hw : LocalWF C l) (hsp : LocalSp C l) {ch : Chunk}
    (hch : ch ∈ l.shared.mm.chunks) (hcu : ch.use = .client) {k : KernelSt} {a s : Nat}
    (hk1 : k.brkStart = l.kernel.brkStart) (hk2 : k.brk = l.kernel.brk)
    (hk3 : k.maps = (a, s) :: (l.kernel.munmap ch.addr ch.size).maps)
    (hpl : (l.kernel.munmap ch.addr ch.size).Placeable C.page a s) (hs : s % C.page = 0)
    (hs16 : C.hdr < s) :
    LocalWF C (mmMove l k ch a s) ∧
      Frame C l (mmMove l k ch a s) [(ch.addr + C.hdr, ch.size - 2 * C.sizeSz)] ∧
      KeptAway l (mmMove l k ch a s) ∧
      ((mmMove l k ch a s).live C).Perm
        ((a + C.hdr, s - 2 * C.sizeSz) :: (l.live C).erase (ch.addr + C.hdr, ch.size - 2 * C.sizeSz)) := by
  have hS := hC.sizeSz; have hP := hC.page
  have hhdr : C.hdr = 16 := by unfold Config.hdr; omega
  have hmm := hw.shared.mm
  have hnd := hmm.nodup
  have hs0 : 0 < s := by omega
  obtain ⟨ha0, hal, hatop, -, -, -⟩ := id hpl
  have htopv : KernelSt.userTop = 2 ^ 47 := rfl
  -- the spans without `ch`
  obtain ⟨R, hR⟩ : ∃ R, R = l.av.spans ++ (l.shared.mm.chunks.erase ch).map (fun c => (c.addr, c.size)) :=
    ⟨_, rfl⟩
  have hspl : l.spans.Perm ((ch.addr, ch.size) :: R) := by
    unfold Local.spans
    rw [hR]
    refine (List.Perm.append_left _ ((List.perm_cons_erase hch).map _)).trans ?_
    simp only [List.map_cons]
    exact List.perm_middle
  have hspl' : (mmMove l k ch a s).spans.Perm ((a, s) :: R) := by
    unfold Local.spans mmMove
    rw [hR]
    simp only [List.map_cons]
    exact List.perm_middle
  have hap₂ := hw.apart.perm hspl
  have hchap : ∀ r ∈ R, r.1 + r.2 ≤ ch.addr ∨ ch.addr + ch.size ≤ r.1 := fun r hr =>
    ((List.pairwise_cons.mp hap₂.1).1 r hr).symm
  have hRsub : ∀ r ∈ R, r ∈ l.spans := fun r hr => hspl.symm.subset (List.mem_cons_of_mem _ hr)
  have hcov₀ : ∀ {r : Nat × Nat}, l.kernel.Covers r → (r.1 + r.2 ≤ ch.addr ∨ ch.addr + ch.size ≤ r.1) →
      k.Covers r := by
    intro r hc hap
    exact covers_mono (k := l.kernel.munmap ch.addr ch.size) hk1 hk2
      (fun m hm => by rw [hk3]; exact List.mem_cons_of_mem _ hm) (covers_munmap hc hap)
  have hfar : ∀ r ∈ R, r.1 + r.2 ≤ a ∨ a + s ≤ r.1 := fun r hr =>
    fresh_away hpl hs0 (covers_munmap (hsp.covered r (hRsub r hr)) (hchap r hr)) (hw.apart.2 r (hRsub r hr))
  have hap : Apart (mmMove l k ch a s).spans := by
    refine Apart.perm ?_ hspl'.symm
    have hRap : Apart R := hap₂.sublist (List.sublist_cons_self _ _)
    refine ⟨List.pairwise_cons.mpr ⟨fun r hr => ?_, hRap.1⟩, fun r hr => ?_⟩
    · have := hfar r hr; simp only; omega
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact hs0
      · exact hRap.2 r hr
  -- the new chunk is not an old one
  have hnot : (⟨a, s, ch.use⟩ : Chunk) ∉ l.shared.mm.chunks.erase ch := by
    intro hc
    have := hfar (a, s) (by rw [hR]; exact List.mem_append_right _ (List.mem_map_of_mem hc))
    simp only at this; omega
  have hsumE := sum_erase_size hch
  have hmem := hmm.mem
  -- mmapped_mem stays a word
  have hsum : ((⟨a, s, ch.use⟩ :: l.shared.mm.chunks.erase ch).map (·.size)).sum ≤ 2 ^ 64 - 1 := by
    have happ : Apart ((⟨a, s, ch.use⟩ :: l.shared.mm.chunks.erase ch).map (fun c => (c.addr, c.size))) := by
      have := hap
      unfold Local.spans mmMove at this
      exact this.sublist (List.sublist_append_right _ _)
    have := apart_sum_le _ _ (Nat.le_refl _) 1 (2 ^ 64) happ (fun r hr => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
      rcases List.mem_cons.mp hc with rfl | hc
      · simp only; omega
      · have hc' := List.mem_of_mem_erase hc
        have := hmm.nonNull c hc'; have := (hw.mmSize c hc').2; simp only; omega)
    rw [List.map_map] at this
    exact this
  simp only [List.map_cons, List.sum_cons] at hsum
  have hmmwf : MmapWF C (mmMove l k ch a s).shared.mm :=
    { mpBound := by
        have hb := hmm.mpBound
        simp only [mmMove]
        refine ⟨hb.1, hb.2.1, by omega, ?_⟩
        have := hb.2.2.2; omega
      trimMin := hmm.trimMin
      use := fun c hc => by
        rcases List.mem_cons.mp hc with rfl | hc
        · exact .inl hcu
        · exact hmm.use c (List.mem_of_mem_erase hc)
      page := fun c hc hu => by
        rcases List.mem_cons.mp hc with rfl | hc
        · exact ⟨hal, hs⟩
        · exact hmm.page c (List.mem_of_mem_erase hc) hu
      nonNull := fun c hc => by
        rcases List.mem_cons.mp hc with rfl | hc
        · exact ha0
        · exact hmm.nonNull c (List.mem_of_mem_erase hc)
      nodup := List.nodup_cons.mpr ⟨hnot, hnd.erase _⟩
      mem := by
        simp only [mmMove, List.map_cons, List.sum_cons]; omega }
  have htot₀ := KernelSt.total_munmap l.kernel ch.addr ch.size
  have htot : k.total = (l.kernel.munmap ch.addr ch.size).total + s := by
    unfold KernelSt.total; rw [hk1, hk2, hk3]
    simp only [List.map_cons, List.sum_cons, KernelSt.munmap]; omega
  have hwl : LocalWF C (mmMove l k ch a s) :=
    { arena := hw.arena
      shared := { mm := hmmwf, narenas := hw.shared.narenas, freeListSub := hw.shared.freeListSub }
      tcache := hw.tcache
      main := fun hmn => by
        obtain ⟨h1, h2⟩ := hw.main hmn
        refine ⟨h1, ?_⟩
        simp only [MainBrk, mmMove] at h2 ⊢; rw [hk1, hk2]; exact h2
      init := fun h0 => absurd ((hw.init h0).2.1 ▸ hch) (List.not_mem_nil)
      apart := hap
      mmSize := fun c hc => by
        rcases List.mem_cons.mp hc with rfl | hc
        · simp only; omega
        · exact hw.mmSize c (List.mem_of_mem_erase hc)
      heap := hw.heap
      sysMain := fun hmn => by
        have := hw.sysMain hmn
        show l.av.tiles.systemMem + (l.shared.mm.mp.mmappedMem + s - ch.size) ≤ k.total
        omega }
  refine ⟨hwl, ?_, fun tc _ _ ht he _ => ⟨tc, ht, he⟩, ?_⟩
  · exact
      { avAddr := rfl
        isMain := rfl
        spatial := fun r h0 hc ha => by
          have hrc := ha (ch.addr, ch.size) (hspl.symm.subset (List.mem_cons_self ..))
          refine ⟨hcov₀ hc hrc, fun x hx => ?_⟩
          rcases List.mem_cons.mp (hspl'.subset hx) with rfl | hx
          · exact fresh_away hpl hs0 (covers_munmap hc hrc) h0
          · exact ha x (hRsub x hx)
        covered := fun r hr => by
          rcases List.mem_cons.mp (hspl'.subset hr) with rfl | hr
          · intro x h1 h2
            refine .inr ⟨(a, s), ?_, h1, h2⟩
            show (a, s) ∈ k.maps
            rw [hk3]; exact List.mem_cons_self ..
          · exact hcov₀ (hsp.covered r (hRsub r hr)) (hchap r hr)
        brkStart := hk1
        nonMain := fun _ => ⟨hk2, rfl⟩
        acct := fun _ => by
          show l.kernel.total + (l.shared.mm.mp.mmappedMem + s - ch.size) ≤ k.total + l.shared.mm.mp.mmappedMem
          omega
        init := rfl
        arenas := ⟨rfl, rfl, rfl⟩
        arena := rfl
        heaps := id
        clients := fun c hc _ _ => hc
        fresh := fun tc' i e ht he => .inl ⟨tc', i, ht, he⟩ }
  · -- the live set
    have hold : (ch.addr + C.hdr, ch.size - 2 * C.sizeSz) ∈ l.shared.live C :=
      mem_shlive.mpr ⟨ch, hch, hcu, rfl⟩
    have hsh : (mmMove l k ch a s).shared.live C =
        (a + C.hdr, s - 2 * C.sizeSz) :: (l.shared.live C).erase (ch.addr + C.hdr, ch.size - 2 * C.sizeSz) := by
      unfold SharedSt.live mmMove
      simp only [List.filter_cons, hcu, decide_true, ↓reduceIte, List.map_cons, usable]
      congr 1
      rw [filter_erase_of _ (by simp [hcu])]
      refine map_erase_of_inj (f := fun c : Chunk => (c.addr + C.hdr, if true = true then c.size - 2 * C.sizeSz else c.size - C.sizeSz))
        fun y hy he => ?_
      simp only [↓reduceIte, Prod.mk.injEq] at he
      exact mm_addr_inj hw (List.mem_filter.mp hy).1 hch (by omega)
    have hnA : (ch.addr + C.hdr, ch.size - 2 * C.sizeSz) ∉
        (l.av.out C).filter (fun pu => !(l.thread.parked C).contains pu) := by
      intro hm
      obtain ⟨d, hd, -, hde⟩ := mem_out.mp (List.mem_filter.mp hm).1
      simp only [Prod.mk.injEq] at hde
      exact addr_clash hw.apart (r := (d.addr, d.size)) (span_mem_spans hd)
        (List.mem_map.mpr ⟨ch, hch, rfl⟩) (by simp only; omega)
    unfold Local.live
    rw [hsh, List.erase_append_right _ hnA]
    show (List.filter _ (l.av.out C) ++ _ :: _).Perm _
    exact List.perm_middle

end Silmaril.Libc.Ptmalloc.Algo
