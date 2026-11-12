module

public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocTop

/-!
# ptmalloc algorithm: `sysmalloc_mmap`

`Algo.sysmallocMmap_body`: a granted `sysmalloc_mmap` is a body (`MBody`): the fresh mapping is
apart from every span (the spans are the process's memory, `LocalSp.covered`, and the kernel
places a mapping on none of it, `fresh_away`), so the new `mmap`ed chunk keeps `LocalWF.apart`, its
payload is apart from every live one, and `mmapped_mem` stays a word (`MmapWF.mem`: it is the total
size of the pairwise apart `mmap`ed chunks, all below `2 ^ 64`: `apart_sum_le`).
`Algo.sysmallocMmap_none`: a refused one only consumes the kernel's answer (an `MStep`).
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

variable {C : Config}

/-! ## Apart ranges in a window have a bounded total -/

theorem sum_filter_split (p : Nat × Nat → Bool) (t : List (Nat × Nat)) :
    (t.map (·.2)).sum = ((t.filter p).map (·.2)).sum + ((t.filter (fun x => !p x)).map (·.2)).sum := by
  induction t with
  | nil => rfl
  | cons x t ih =>
    by_cases hx : p x = true
    · simp only [List.filter_cons, hx, ↓reduceIte, Bool.not_true, Bool.false_eq_true, List.map_cons,
        List.sum_cons]; omega
    · simp only [Bool.not_eq_true] at hx
      simp only [List.filter_cons, hx, Bool.false_eq_true, ↓reduceIte, Bool.not_false, List.map_cons,
        List.sum_cons]; omega

/-- **Pairwise apart ranges inside `[lo, hi)` total at most `hi - lo` bytes.** -/
theorem apart_sum_le : ∀ (k : Nat) (rs : List (Nat × Nat)), rs.length ≤ k → ∀ lo hi, Apart rs →
    (∀ r ∈ rs, lo ≤ r.1 ∧ r.1 + r.2 ≤ hi) → (rs.map (·.2)).sum ≤ hi - lo
  | _, [], _, _, _, _, _ => by simp
  | 0, _ :: _, h, _, _, _, _ => by simp at h
  | k + 1, r :: t, hlen, lo, hi, hap, hb => by
    have hp := List.pairwise_cons.mp hap.1
    have hlt : t.length ≤ k := by simp at hlen; omega
    have hapt : Apart t := hap.sublist (List.sublist_cons_self _ _)
    have hB := apart_sum_le k (t.filter fun s => decide (s.1 + s.2 ≤ r.1))
      (Nat.le_trans (List.length_filter_le _ _) hlt) lo r.1 (hapt.sublist (List.filter_sublist))
      (fun s hs => by
        obtain ⟨hs, hsd⟩ := List.mem_filter.mp hs
        have := hb s (List.mem_cons_of_mem _ hs); simp only [decide_eq_true_eq] at hsd; omega)
    have hA := apart_sum_le k (t.filter fun s => !decide (s.1 + s.2 ≤ r.1))
      (Nat.le_trans (List.length_filter_le _ _) hlt) (r.1 + r.2) hi (hapt.sublist (List.filter_sublist))
      (fun s hs => by
        obtain ⟨hs, hsd⟩ := List.mem_filter.mp hs
        have := hb s (List.mem_cons_of_mem _ hs)
        have := hp.1 s hs
        simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hsd; omega)
    have hsplit := sum_filter_split (fun s => decide (s.1 + s.2 ≤ r.1)) t
    have hr := hb r (List.mem_cons_self ..)
    simp only [List.map_cons, List.sum_cons]
    omega

/-! ## The kernel's answers -/

theorem mmap_some {k k' : KernelSt} {al n a : Nat} (h : k.mmap al n = (some a, k')) :
    k'.brkStart = k.brkStart ∧ k'.brk = k.brk ∧ k'.maps = (a, n) :: k.maps ∧ k.Placeable al a n := by
  have := mmap_spec k al n
  rw [h] at this
  obtain ⟨h1, h2, ⟨h3, -⟩ | ⟨a', h3, h4, h5⟩⟩ := this
  · cases h3
  · injection h3 with h3; subst h3; exact ⟨h1, h2, h4, h5⟩

theorem mmap_none {k k' : KernelSt} {al n : Nat} (h : k.mmap al n = (none, k')) :
    k'.brkStart = k.brkStart ∧ k'.brk = k.brk ∧ k'.maps = k.maps := by
  have := mmap_spec k al n
  rw [h] at this
  obtain ⟨h1, h2, ⟨-, h3⟩ | ⟨a', h3, -⟩⟩ := this
  · exact ⟨h1, h2, h3⟩
  · cases h3

/-! ## A kernel answer consumed, nothing else -/

/-- **Only the kernel's answer counter moved**: an `MStep`. -/
theorem kernel_step {l : Local} (hw : LocalWF C l) (hsp : LocalSp C l) {k : KernelSt}
    (hb : k.brkStart = l.kernel.brkStart) (hb2 : k.brk = l.kernel.brk) (hm : k.maps = l.kernel.maps) :
    MStep C l { l with kernel := k } := by
  have hcov : ∀ {r}, l.kernel.Covers r → k.Covers r :=
    covers_mono hb hb2 (fun m h => by rw [hm]; exact h)
  refine ⟨?_, List.Perm.refl _, ?_, fun tc _ _ ht he _ => ⟨tc, ht, he⟩, id⟩
  · exact
      { arena := hw.arena
        shared := hw.shared
        tcache := hw.tcache
        main := fun hmn => by
          obtain ⟨h1, h2⟩ := hw.main hmn
          refine ⟨h1, ?_⟩
          simp only [MainBrk] at h2 ⊢; rw [hb, hb2]; exact h2
        init := hw.init
        apart := hw.apart
        mmSize := hw.mmSize
        heap := hw.heap
        sysMain := fun hmn => by
          have := hw.sysMain hmn
          show _ ≤ k.total
          rw [KernelSt.total_eq hb hb2 hm]; exact this }
  · exact
      { avAddr := rfl
        isMain := rfl
        spatial := fun r _ hc ha => ⟨hcov hc, ha⟩
        covered := fun r hr => hcov (hsp.covered r hr)
        brkStart := hb
        nonMain := fun _ => ⟨hb2, rfl⟩
        acct := fun _ => by
          have := KernelSt.total_eq hb hb2 hm
          show l.kernel.total + l.shared.mm.mp.mmappedMem ≤ k.total + l.shared.mm.mp.mmappedMem; omega
        init := rfl
        arenas := ⟨rfl, rfl, rfl⟩
        arena := rfl
        heaps := id
        clients := fun c hc _ _ => hc
        fresh := fun tc' i e ht he => .inl ⟨tc', i, ht, he⟩ }

/-- **A refused `sysmalloc_mmap`** consumed only the kernel's answer. -/
theorem sysmallocMmap_none {l l' : Local} {nb : Nat} (h : sysmallocMmap C l nb = (none, l')) :
    ∃ k : KernelSt, l' = { l with kernel := k } ∧ k.brkStart = l.kernel.brkStart ∧
      k.brk = l.kernel.brk ∧ k.maps = l.kernel.maps := by
  unfold sysmallocMmap at h
  dsimp only at h
  split at h
  · injection h with h1 h; subst h; exact ⟨l.kernel, rfl, rfl, rfl, rfl⟩
  · split at h
    · rename_i k heq
      injection h with h1 h; subst h
      exact ⟨k, rfl, mmap_none heq⟩
    · cases h

/-! ## A granted `sysmalloc_mmap` -/

theorem alignUp_page' (hC : C.Ok) (x : Nat) :
    x ≤ alignUp x C.page ∧ alignUp x C.page % C.page = 0 := by
  unfold alignUp; rw [hC.page]; omega

/-- The view after a granted `sysmalloc_mmap`. -/
def mmAdd (l : Local) (k : KernelSt) (c : Chunk) : Local :=
  { l with kernel := k, shared := { l.shared with mm := l.shared.mm.add c } }

/-- The spans after a new `mmap`ed chunk. -/
theorem spans_add (l : Local) (k : KernelSt) (c : Chunk) :
    (mmAdd l k c).spans.Perm
      ((c.addr, c.size) :: l.spans) := by
  unfold Local.spans mmAdd
  simp only [MmapSt.add, List.map_cons]
  exact List.perm_middle

theorem live_add (l : Local) (k : KernelSt) (c : Chunk) (hc : c.use = .client) :
    (mmAdd l k c).live C =
      (l.av.out C).filter (fun pu => !(l.thread.parked C).contains pu) ++
        (c.addr + C.hdr, usable C c true) :: l.shared.live C := by
  unfold Local.live SharedSt.live mmAdd
  simp only [MmapSt.add, List.filter_cons, hc, decide_true, ↓reduceIte, List.map_cons]

/-- **A granted `sysmalloc_mmap`** is a body. -/
theorem sysmallocMmap_body (hC : C.Ok) {l : Local} (hw : LocalWF C l) (hsp : LocalSp C l)
    (hi : l.shared.init = true) {n nb : Nat} (hnb : C.checkedRequest2size n = some nb) {p : Nat}
    {l' : Local} (h : sysmallocMmap C l nb = (some p, l')) : MBody C n l p l' := by
  have hnbE : nb = C.request2size n := by
    unfold Config.checkedRequest2size at hnb; split at hnb <;> simp_all
  obtain ⟨hnbA, hnbM, hnbN⟩ := request2size_props hC n
  rw [← hnbE] at hnbA hnbM hnbN
  have hA := hC.align; have hM := hC.minSize; have hS := hC.sizeSz; have hP := hC.page
  have hhdr : C.hdr = 16 := by unfold Config.hdr; omega
  obtain ⟨hsz1, hsz2⟩ := alignUp_page' hC (nb + C.sizeSz)
  unfold sysmallocMmap at h
  dsimp only at h
  split at h
  · cases h
  rename_i hbig
  split at h
  · cases h
  rename_i a k heq
  injection h with hp hl
  injection hp with hp
  change mmAdd l k ⟨a, alignUp (nb + C.sizeSz) C.page, .client⟩ = l' at hl
  subst hp; subst hl
  obtain ⟨hk1, hk2, hk3, hpl⟩ := mmap_some heq
  generalize hs : alignUp (nb + C.sizeSz) C.page = s at hsz1 hsz2 hpl hbig hk3
  have hs0 : 0 < s := by omega
  obtain ⟨ha0, hal, hatop, -, -, -⟩ := id hpl
  have htopv : KernelSt.userTop = 2 ^ 47 := rfl
  -- the old spans are apart from the new mapping
  have hfar : ∀ r ∈ l.spans, r.1 + r.2 ≤ a ∨ a + s ≤ r.1 := fun r hr =>
    fresh_away hpl hs0 (hsp.covered r hr) (hw.apart.2 r hr)
  have hmem' : ∀ r, r ∈ (mmAdd l k ⟨a, s, .client⟩).spans ↔
      r = (a, s) ∨ r ∈ l.spans := fun r => by
    rw [(spans_add l _ ⟨a, s, .client⟩).mem_iff]; simp
  have hap : Apart (mmAdd l k ⟨a, s, .client⟩).spans := by
    refine Apart.perm ?_ (spans_add l _ ⟨a, s, .client⟩).symm
    refine ⟨List.pairwise_cons.mpr ⟨fun r hr => ?_, hw.apart.1⟩, fun r hr => ?_⟩
    · have := hfar r hr; simp only; omega
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact hs0
      · exact hw.apart.2 r hr
  have hmm := hw.shared.mm
  -- the new chunk is not an old one
  have hnot : (⟨a, s, .client⟩ : Chunk) ∉ l.shared.mm.chunks := by
    intro hc
    have := hfar (a, s) (by unfold Local.spans; exact List.mem_append_right _ (List.mem_map_of_mem hc))
    simp only at this; omega
  -- mmapped_mem stays a word
  have hsum : ((⟨a, s, .client⟩ :: l.shared.mm.chunks).map (·.size)).sum ≤ 2 ^ 64 - 1 := by
    have happ : Apart ((⟨a, s, .client⟩ :: l.shared.mm.chunks).map (fun c => (c.addr, c.size))) := by
      have := hap
      unfold Local.spans at this
      exact this.sublist (List.sublist_append_right _ _)
    have := apart_sum_le _ _ (Nat.le_refl _) 1 (2 ^ 64) happ (fun r hr => by
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
      rcases List.mem_cons.mp hc with rfl | hc
      · simp only; omega
      · have := hmm.nonNull c hc; have := (hw.mmSize c hc).2; simp only; omega)
    rw [List.map_map] at this
    exact this
  have hmmwf : MmapWF C (l.shared.mm.add ⟨a, s, .client⟩) :=
    { mpBound := by
        have hb := hmm.mpBound; have he := hmm.mem
        simp only [MmapSt.add, List.map_cons, List.sum_cons] at hsum ⊢
        refine ⟨hb.1, hb.2.1, by omega, ?_⟩
        have := hb.2.2.2; omega
      trimMin := hmm.trimMin
      use := fun c hc => by
        rcases List.mem_cons.mp hc with rfl | hc
        · exact .inl rfl
        · exact hmm.use c hc
      page := fun c hc hu => by
        rcases List.mem_cons.mp hc with rfl | hc
        · exact ⟨hal, hsz2⟩
        · exact hmm.page c hc hu
      nonNull := fun c hc => by
        rcases List.mem_cons.mp hc with rfl | hc
        · exact ha0
        · exact hmm.nonNull c hc
      nodup := List.nodup_cons.mpr ⟨hnot, hmm.nodup⟩
      mem := by
        have := hmm.mem
        simp only [MmapSt.add, List.map_cons, List.sum_cons]; omega }
  have hwl : LocalWF C (mmAdd l k ⟨a, s, .client⟩) :=
    { arena := hw.arena
      shared := { mm := hmmwf, narenas := hw.shared.narenas, freeListSub := hw.shared.freeListSub }
      tcache := hw.tcache
      main := fun hmn => by
        obtain ⟨h1, h2⟩ := hw.main hmn
        refine ⟨h1, ?_⟩
        simp only [MainBrk, mmAdd] at h2 ⊢; rw [hk1, hk2]; exact h2
      init := fun h0 => by change l.shared.init = false at h0; rw [hi] at h0; cases h0
      apart := hap
      mmSize := fun c hc => by
        rcases List.mem_cons.mp hc with rfl | hc
        · simp only; omega
        · exact hw.mmSize c hc
      heap := hw.heap
      sysMain := fun hmn => by
        have := hw.sysMain hmn
        have htot : k.total = l.kernel.total + s := by
          unfold KernelSt.total; rw [hk1, hk2, hk3]; simp only [List.map_cons, List.sum_cons]; omega
        show l.av.tiles.systemMem + (l.shared.mm.add ⟨a, s, .client⟩).mp.mmappedMem ≤ k.total
        simp only [MmapSt.add]; omega }
  have hcov : ∀ {r}, l.kernel.Covers r → k.Covers r :=
    covers_mono hk1 hk2 (fun m h => by rw [hk3]; exact List.mem_cons_of_mem _ h)
  refine ⟨⟨hwl, ⟨rfl, rfl, fun h => absurd h (by decide), fun h => absurd h (by decide),
      fun h => absurd h (by decide), fun h => absurd h (by decide)⟩,
      .inr ⟨by omega, by rw [hhdr, hA]; rw [hP] at hal; omega, s - 2 * C.sizeSz, by omega, ?_, ?_⟩⟩, ?_,
      fun tc _ _ ht he _ => ⟨tc, ht, he⟩, id⟩
  · rw [live_add l _ ⟨a, s, .client⟩ rfl]
    simp only [usable, ↓reduceIte]
    exact List.perm_middle
  · intro q hq
    unfold Local.live at hq
    rcases List.mem_append.mp hq with hq | hq
    · have hq := (List.mem_filter.mp hq).1
      simp only [ArenaSt.out, ArenaSt.chunks, Chunk.view, List.mem_map, List.mem_filter] at hq
      obtain ⟨c, ⟨hc', -⟩, rfl⟩ := hq
      have := hfar _ (mem_spans_of_chunk (l := l) hc')
      have := (hw.arena.tiles.sizes c hc').2
      simp only [usable, Bool.false_eq_true, ↓reduceIte] at this ⊢; omega
    · simp only [SharedSt.live, List.mem_map, List.mem_filter] at hq
      obtain ⟨c, ⟨hc', -⟩, rfl⟩ := hq
      have := hfar (c.addr, c.size) (by unfold Local.spans; exact List.mem_append_right _ (List.mem_map_of_mem hc'))
      have := (hw.mmSize c hc').1
      simp only [usable, ↓reduceIte] at this ⊢; omega
  · exact
      { avAddr := rfl
        isMain := rfl
        spatial := fun r h0 hc ha => by
          refine ⟨hcov hc, fun x hx => ?_⟩
          rcases (hmem' x).mp hx with rfl | hx
          · exact fresh_away hpl hs0 hc h0
          · exact ha x hx
        covered := fun r hr => by
          rcases (hmem' r).mp hr with rfl | hr
          · intro x h1 h2
            refine .inr ⟨(a, s), ?_, h1, h2⟩
            show (a, s) ∈ k.maps
            rw [hk3]; exact List.mem_cons_self ..
          · exact hcov (hsp.covered r hr)
        brkStart := hk1
        nonMain := fun _ => ⟨hk2, rfl⟩
        acct := fun _ => by
          have htot : k.total = l.kernel.total + s := by
            unfold KernelSt.total; rw [hk1, hk2, hk3]; simp only [List.map_cons, List.sum_cons]; omega
          show l.kernel.total + (l.shared.mm.add ⟨a, s, .client⟩).mp.mmappedMem ≤ k.total + _
          simp only [MmapSt.add]; omega
        init := rfl
        arenas := ⟨rfl, rfl, rfl⟩
        arena := rfl
        heaps := id
        clients := fun c hc _ _ => hc
        fresh := fun tc' i e ht he => .inl ⟨tc', i, ht, he⟩ }

end Silmaril.Libc.Ptmalloc.Algo
