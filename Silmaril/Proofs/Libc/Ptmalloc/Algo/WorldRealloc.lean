module

public import Silmaril.Proofs.Libc.Ptmalloc.Algo.Mremap
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.WorldCalls

/-!
# ptmalloc algorithm: `calloc` and `realloc` at world level (`Task.algo.wfCallocRealloc`)

* `Algo.calloc_wf`: `__libc_calloc` is `malloc`'s non-tcache path (`withArena_wf`);
* `Algo.realloc_wf`: `__libc_realloc`'s paths: `realloc (p, 0)` (`free_wf`), an `mmap`ed chunk
  (`mremap_chunk`: kept, refused then kept or `malloc`-copy-`munmap_chunk`, or moved:
  `Algo.mremap_body`), an arena chunk (`_int_realloc`: `Algo.bodyRealloc`; single-threaded or
  done; else `malloc`, copy, `_int_free`);
* **`Algo.wfCallocRealloc`** (= `Task.algo.wfCallocRealloc C (ptmalloc C)`).
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

variable {C : Config}

/-! ## `calloc` -/

theorem calloc_wf (hC : C.Ok) (hB : Task.algo.bodyMalloc C) {w w' : World} {tid k m p : Nat}
    (hw : WorldWF C w) (ht : tid ∈ w.tids) (h : (ptmalloc C).calloc w tid k m = .ok (p, w')) :
    WorldWF C w' ∧ w'.tids = w.tids ∧ MallocLive C (k * m) p (w.live C) (w'.live C) := by
  unfold Ops.calloc at h
  split at h
  · injection h with h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have := setErrno_wf (tid := tid) (e := 12) hw
    exact ⟨this.1, rfl, .inl ⟨rfl, by rw [this.2]⟩⟩
  obtain ⟨w₁, h1, h⟩ := bind_ok_inv h
  obtain ⟨hw1, hl1, ht1, hi1, -, -⟩ := init_wf hw h1
  have ht1' : tid ∈ w₁.tids := ht1 ▸ ht
  obtain ⟨w₂, h2, h⟩ := bind_ok_inv h
  have c2 := tcacheInit_wf hC hB hw1 ht1' hi1 (h2 : tcacheInit C w₁ tid = _)
  have hlive2 : (w₂.live C).Perm (w.live C) := by rw [← hl1]; exact c2.live
  have := withArena_wf hC hB c2.wf (c2.tids ▸ ht1') (c2.init.trans hi1) h
  exact ⟨this.1, ((withArena_tids h).trans c2.tids).trans ht1, MallocLive.perm_left hlive2 this.2⟩

/-! ## A view put back -/

/-- **A body that replaces the live payload `x` by `y`**, put back. -/
theorem put_move (hC : C.Ok) {w : World} {tid a : Nat} {l l' : Local} (hw : WorldWF C w)
    (ht : tid ∈ w.tids) (hl : w.local? tid a = some l) (hwf : LocalWF C l) (hwf' : LocalWF C l')
    {x y : Nat × Nat} (hF : Frame C l l' [x]) (hK : KeptAway l l') (hxw : x ∈ w.live C)
    (hxl : x ∈ l.live C) (hyx : y ≠ x) (hperm : (l'.live C).Perm (y :: (l.live C).erase x)) :
    WorldWF C (w.put tid l') ∧ ((w.put tid l').live C).Perm (y :: (w.live C).erase x) ∧
      ∀ z ∈ (w.live C).erase x, z.1 + z.2 ≤ y.1 ∨ y.1 + y.2 ≤ z.1 := by
  have hw' := worldWF_put hC hw ht hl hwf' hF (by simpa using hxw)
  have hndl := nodup_of_liveApart (llive_apart hC hwf)
  have hndl' := nodup_of_liveApart (llive_apart hC hwf')
  have hnd := live_nodup hC hw
  have hyl' : y ∈ l'.live C := hperm.symm.subset (List.mem_cons_self ..)
  have hyl : y ∉ l.live C := by
    intro hy
    have h1 := (hperm.nodup_iff.mp hndl')
    exact (List.nodup_cons.mp h1).1 (hndl.mem_erase_iff.mpr ⟨hyx, hy⟩)
  have hloc := put_live hw ht hl hwf' hF hK (by simpa using ⟨hxw, hxl⟩) [y] (by simpa using hyl)
    (fun z => by rw [hperm.mem_iff, List.mem_cons, hndl.mem_erase_iff]; simp [and_comm])
  have hyw : y ∉ w.live C := new_not_live hw ht hl hwf' hF hyl' hyl
  have hmem : ∀ z, z ∈ (w.put tid l').live C ↔ z = y ∨ z ∈ (w.live C).erase x := fun z => by
    rw [hloc z, hnd.mem_erase_iff]; simp [and_comm]
  refine ⟨hw', (List.perm_ext_iff_of_nodup (live_nodup hC hw')
    (List.nodup_cons.mpr ⟨fun h => hyw (List.mem_of_mem_erase h), hnd.erase _⟩)).mpr fun z => by
      rw [hmem z]; simp, fun z hz => ?_⟩
  have hap := (liveApart C hC _ hw').1
  exact pairwise_of_mem (fun h => h.symm) hap ((hmem z).mpr (.inr hz)) ((hmem y).mpr (.inl rfl))
    (fun h => hyw (h ▸ List.mem_of_mem_erase hz))

/-- **A body that changes no live payload**, put back. -/
theorem put_same (hC : C.Ok) {w : World} {tid a : Nat} {l l' : Local} (hw : WorldWF C w)
    (ht : tid ∈ w.tids) (hl : w.local? tid a = some l) (hwf' : LocalWF C l') (hF : Frame C l l' [])
    (hK : KeptAway l l') (hperm : (l'.live C).Perm (l.live C)) :
    WorldWF C (w.put tid l') ∧ ((w.put tid l').live C).Perm (w.live C) := by
  obtain ⟨h1, h2⟩ := put_malloc (n := 0) hC hw ht hl hwf' hF hK (.inl ⟨rfl, hperm⟩)
  rcases h2 with ⟨-, h2⟩ | ⟨h2, -⟩
  · exact ⟨h1, h2⟩
  · exact absurd rfl h2

/-- `MallocLive` of a payload that replaces `x`. -/
theorem mallocLive_move {n q u : Nat} {live live' : List (Nat × Nat)} (hq : q ≠ 0) (hal : q % C.align = 0)
    (hn : n ≤ u) {x : Nat × Nat} (hperm : live'.Perm ((q, u) :: live.erase x))
    (hap : ∀ z ∈ live.erase x, z.1 + z.2 ≤ q ∨ q + u ≤ z.1) :
    MallocLive C n q (live.erase x) live' :=
  .inr ⟨hq, hal, u, hn, hperm, hap⟩

/-- The view of a world at one of its arenas, with its spatial facts. -/
theorem view_of {w : World} {tid : Nat} (hw : WorldWF C w) (ht : tid ∈ w.tids) {a : Nat} {l : Local}
    (hl : Ops.localAt w tid a = .ok l) : LocalWF C l ∧ LocalSp C l ∧ w.local? tid a = some l :=
  have hl' := localAt_inv hl
  ⟨hw.locals tid a l ht hl', localSp hw ht hl', hl'⟩

/-- **A live payload at a chunk of arena `a`** is a live payload of `a`'s view. -/
theorem arenaLive_at (hC : C.Ok) {w : World} (hw : WorldWF C w) {tid a : Nat} (ht : tid ∈ w.tids)
    {l : Local} (hl : w.local? tid a = some l) {p u : Nat} (hpu : (p, u) ∈ w.live C)
    {d : Chunk} (hd : d ∈ l.av.chunks) (hda : d.addr = p - C.hdr) : (p, u) ∈ l.arenaLive C := by
  obtain ⟨av, hav, hlav, hla, -, hlt, hls, -⟩ := local?_fields hl
  have h8 := hC.sizeSz
  have hp16 := live_ge_hdr hpu
  rcases mem_live.mp hpu with ⟨⟨b, -, avb, hab, hyb⟩, hnp⟩ | hm
  · obtain ⟨d', hd', -, hde⟩ := mem_out.mp hyb
    simp only [Prod.mk.injEq] at hde
    have hba : b = a := by
      refine Classical.byContradiction fun hne => ?_
      exact clash_arenas hw hne hab hav hd' (by rw [← hlav]; exact hd) (by unfold Config.hdr at *; omega)
    subst hba
    rw [hav] at hab; cases hab
    refine List.mem_filter.mpr ⟨by rw [hlav]; exact hyb, ?_⟩
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, contains_false]
    intro hp'
    exact hnp ((old_allParked ht).mpr (.inl (by rw [← hlt]; exact hp')))
  · exfalso
    obtain ⟨m, hm, -, hme⟩ := mem_shlive.mp hm
    simp only [Prod.mk.injEq] at hme
    exact clash_mm hw hav (by rw [← hlav]; exact hd) hm (by unfold Config.hdr at *; omega)

/-- `_int_free`'s success finds a lent-out chunk at its address. -/
theorem intFree_chunk {l l' : Local} {c : Nat} (h : intFree C l c = .ok l') :
    ∃ d ∈ l.av.chunks, d.addr = c ∧ d.use = .client := by
  unfold intFree at h
  cases hf : l.av.tiles.find? c with
  | none => rw [hf] at h; cases h
  | some d =>
    rw [hf] at h
    have hd : d ∈ l.av.tiles.heapChunks := List.mem_of_find?_eq_some hf
    have hda : d.addr = c := by simpa using List.find?_some hf
    refine ⟨d, hd, hda, ?_⟩
    dsimp only at h
    split at h
    · cases h
    split at h
    · cases h
    split at h
    · cases h
    · cases h
    · cases h
    · assumption

/-- **`munmap_chunk` of a live `mmap`ed chunk `ch`** on the main arena's view (`realloc`'s fallback:
no dynamic threshold): `WorldWF` and the live set without it. -/
theorem mmUnmap_put (hC : C.Ok) {w : World} (hw : WorldWF C w) {tid : Nat} (ht : tid ∈ w.tids)
    {ch : Chunk} (hch : ch ∈ w.shared.mm.chunks) (hcu : ch.use = .client) {l l₂ : Local}
    (hl : w.local? tid w.mainArena = some l)
    (hm : munmapChunk C l
      ch.addr = .ok l₂) :
    WorldWF C (w.put tid l₂) ∧
      ((w.put tid l₂).live C).Perm ((w.live C).erase (ch.addr + C.hdr, ch.size - 2 * C.sizeSz)) := by
  obtain ⟨av, hav, hlav, hla, hlm, hlt, hls, hlk⟩ := local?_fields hl
  have hwl := hw.locals tid _ l ht hl
  have hsp := localSp hw ht hl
  have hch' : ch ∈ l.shared.mm.chunks := by rw [hls]; exact hch
  have hpg := hwl.shared.mm.page ch hch' hcu
  have hfind : mmFind? l ch.addr =
      some ch := by
    unfold mmFind?; exact find?_addr (mm_addrs_nodup hwl) hch'
  unfold munmapChunk at hm
  rw [hfind] at hm
  simp only [hpg.1, hpg.2, ne_eq, not_true_eq_false, or_self, ite_false] at hm
  injection hm with hm; subst hm
  -- the view after
  generalize hl₂ : ({ l with
      kernel := l.kernel.munmap ch.addr ch.size
      shared := { l.shared with mm := l.shared.mm.remove ch } } : Local) = l₂
  have hmm₂ : l₂.shared.mm.chunks = l.shared.mm.chunks.erase ch := by
    rw [← hl₂]; simp [MmapSt.remove]
  have hnd := hwl.shared.mm.nodup
  have hsub : l₂.shared.mm.chunks ⊆ l.shared.mm.chunks := fun d hd => by
    rw [hmm₂] at hd; exact List.mem_of_mem_erase hd
  have hspl : l.spans.Perm ((ch.addr, ch.size) :: l₂.spans) := by
    unfold Local.spans
    rw [hmm₂, show l₂.av = l.av by rw [← hl₂]]
    refine (List.Perm.append_left _ ((List.perm_cons_erase hch').map _)).trans ?_
    simp only [List.map_cons]
    exact List.perm_middle
  have hap₂ := hwl.apart.perm hspl
  have hchap : ∀ s ∈ l₂.spans, s.1 + s.2 ≤ ch.addr ∨ ch.addr + ch.size ≤ s.1 := fun s hs =>
    ((List.pairwise_cons.mp hap₂.1).1 s hs).symm
  have hwl₂ : LocalWF C l₂ := by
    have hmmwf := hwl.shared.mm
    rw [← hl₂]
    refine
      { arena := hwl.arena
        shared :=
          { mm :=
              { mpBound := by
                  have := hmmwf.mpBound
                  simp only [MmapSt.remove]; refine ⟨this.1, this.2.1, ?_, this.2.2.2⟩; omega
                trimMin := hmmwf.trimMin
                use := fun d hd => hmmwf.use d (List.mem_of_mem_erase hd)
                page := fun d hd => hmmwf.page d (List.mem_of_mem_erase hd)
                nonNull := fun d hd => hmmwf.nonNull d (List.mem_of_mem_erase hd)
                nodup := hmmwf.nodup.erase _
                mem := by
                  have hm := hmmwf.mem
                  have he := sum_erase_size hch'
                  simp only [MmapSt.remove]; omega }
            narenas := hwl.shared.narenas
            freeListSub := hwl.shared.freeListSub }
        tcache := hwl.tcache
        main := fun hm => by
          have ⟨h1, h2⟩ := hwl.main hm
          unfold MainSbrk MainBrk at *
          simp only [MmapSt.remove, KernelSt.munmap]
          exact ⟨h1, h2⟩
        init := fun hi => absurd ((hwl.init hi).2.1 ▸ hch') (List.not_mem_nil)
        apart := ?_
        mmSize := fun d hd => hwl.mmSize d (List.mem_of_mem_erase (by simpa [MmapSt.remove] using hd))
        heap := hwl.heap
        sysMain := fun hmn => by
          have h0 := hwl.sysMain hmn
          have h1 := KernelSt.total_munmap l.kernel ch.addr ch.size
          have hm1 := hmmwf.mem
          have hm0 := hwl.shared.mm.mem
          have he := sum_erase_size hch'
          simp only [MmapSt.remove]
          omega }
    have := Apart.right (List.pairwise_cons.mp hap₂.1 |> fun _ => hap₂.perm (List.Perm.refl _) |>
      fun h => (show Apart ([(ch.addr, ch.size)] ++ l₂.spans) from h))
    rw [← hl₂] at this; exact this
  have hF : Frame C l l₂ [(ch.addr + C.hdr, ch.size - 2 * C.sizeSz)] :=
    { avAddr := by rw [← hl₂]
      isMain := by rw [← hl₂]
      spatial := fun r h0 hc haw => by
        have hrc := haw (ch.addr, ch.size) (hspl.symm.subset (List.mem_cons_self ..))
        refine ⟨by rw [← hl₂]; exact covers_munmap hc hrc, fun s hs => haw s (hspl.symm.subset
          (List.mem_cons_of_mem _ hs))⟩
      covered := fun s hs => by
        have hc := hsp.covered s (hspl.symm.subset (List.mem_cons_of_mem _ hs))
        rw [← hl₂]; exact covers_munmap hc (hchap s hs)
      brkStart := by rw [← hl₂]; rfl
      nonMain := fun h => by rw [hlm] at h; simp at h
      acct := fun h => by rw [hlm] at h; simp at h
      init := by rw [← hl₂]
      arenas := by rw [← hl₂]; exact ⟨rfl, rfl, rfl⟩
      arena := by rw [← hl₂]
      heaps := fun h => by rw [← hl₂]; exact h
      clients := fun c hc _ _ => by rw [← hl₂]; exact hc
      fresh := fun tc' i e htc he => .inl ⟨tc', i, by rw [← hl₂] at htc; exact htc, he⟩ }
  have hK : KeptAway l l₂ := fun tc i e htc he _ => ⟨tc, by rw [← hl₂]; exact htc, he⟩
  have hpw : (ch.addr + C.hdr, ch.size - 2 * C.sizeSz) ∈ w.live C :=
    mem_live.mpr (.inr (mem_shlive.mpr ⟨ch, hch, hcu, rfl⟩))
  have hpl : (ch.addr + C.hdr, ch.size - 2 * C.sizeSz) ∈ l.live C :=
    mem_llive.mpr (.inr (mem_shlive.mpr ⟨ch, hch', hcu, rfl⟩))
  have hperm : (l₂.live C).Perm ((l.live C).erase (ch.addr + C.hdr, ch.size - 2 * C.sizeSz)) := by
    have hnl := nodup_of_liveApart (llive_apart hC hwl)
    refine (List.perm_ext_iff_of_nodup (nodup_of_liveApart (llive_apart hC hwl₂)) (hnl.erase _)).mpr
      fun y => ?_
    rw [hnl.mem_erase_iff, mem_llive, mem_llive]
    have hav₂ : l₂.av = l.av := by rw [← hl₂]
    have hth₂ : l₂.thread = l.thread := by rw [← hl₂]
    rw [hav₂, hth₂]
    have hsh : ∀ y, y ∈ l₂.shared.live C ↔ y ∈ l.shared.live C ∧ y ≠ (ch.addr + C.hdr, ch.size - 2 * C.sizeSz) := by
      intro y
      rw [mem_shlive, mem_shlive, hmm₂]
      constructor
      · rintro ⟨d, hd, hdu, rfl⟩
        have ⟨hdne, hd'⟩ := (hnd.mem_erase_iff).mp hd
        refine ⟨⟨d, hd', hdu, rfl⟩, fun he => hdne ?_⟩
        simp only [Prod.mk.injEq] at he
        exact mm_addr_inj hwl hd' hch' (by omega)
      · rintro ⟨⟨d, hd, hdu, rfl⟩, hne⟩
        refine ⟨d, (hnd.mem_erase_iff).mpr ⟨fun h => hne (by rw [h]), hd⟩, hdu, rfl⟩
    constructor
    · rintro (⟨hy, hnp⟩ | hy)
      · refine ⟨fun he => ?_, .inl ⟨hy, hnp⟩⟩
        subst he
        obtain ⟨d, hd, -, hde⟩ := mem_out.mp hy
        simp only [Prod.mk.injEq] at hde
        exact clash_mm hw hav (by rw [← hlav]; exact hd) hch (by omega)
      · exact ⟨((hsh y).mp hy).2, .inr ((hsh y).mp hy).1⟩
    · rintro ⟨hne, (⟨hy, hnp⟩ | hy)⟩
      · exact .inl ⟨hy, hnp⟩
      · exact .inr ((hsh y).mpr ⟨hy, hne⟩)
  exact put_free hC hw ht hl hwl hwl₂ hF hK hpw hpl hperm

/-! ## `free` -/

/-- A live payload of a well-formed world is aligned. -/
theorem live_align' (hC : C.Ok) {w : World} (hw : WorldWF C w) {y : Nat × Nat} (hy : y ∈ w.live C) :
    y.1 % C.align = 0 := by
  have h16 := hC.align; have h8 := hC.sizeSz; have hpg := hC.page
  have hhdr : C.hdr = 16 := by unfold Config.hdr; omega
  rcases mem_live.mp hy with ⟨⟨b, -, av, hab, hyb⟩, -⟩ | hm
  · obtain ⟨c, hc, -, rfl⟩ := mem_out.mp hyb
    have := (hw.arenaWF b av hab).tiles.aligned c hc
    simp only; rw [h16] at this ⊢; omega
  · obtain ⟨m, hm', hmu, rfl⟩ := mem_shlive.mp hm
    have := (hw.shared.mm.page m hm' hmu).1
    simp only; rw [h16]; rw [hpg] at this; omega

/-! ## `mremap_chunk` and `munmap_chunk` -/

/-- **The outcomes of `mremap_chunk`**: the chunk kept (same size), refused (the kernel's answer
consumed), or moved (`mmMove`). -/
theorem mremap_cases {l l₁ : Local} {c nb q : Nat} (h : mremapChunk C l c nb = .ok (q, l₁)) :
    ∃ ch, ch ∈ l.shared.mm.chunks ∧ ch.addr = c ∧ c % C.page = 0 ∧ ch.size % C.page = 0 ∧
      ((alignUp (nb + C.sizeSz) C.page = ch.size ∧ q = c ∧ l₁ = l) ∨
       (alignUp (nb + C.sizeSz) C.page ≠ ch.size ∧ q = 0 ∧ ∃ k : KernelSt, l₁ = { l with kernel := k } ∧
          k.brkStart = l.kernel.brkStart ∧ k.brk = l.kernel.brk ∧ k.maps = l.kernel.maps) ∨
       (alignUp (nb + C.sizeSz) C.page ≠ ch.size ∧ ∃ k : KernelSt,
          l₁ = mmMove l k ch q (alignUp (nb + C.sizeSz) C.page) ∧ k.brkStart = l.kernel.brkStart ∧
          k.brk = l.kernel.brk ∧
          k.maps = (q, alignUp (nb + C.sizeSz) C.page) :: (l.kernel.munmap c ch.size).maps ∧
          (l.kernel.munmap c ch.size).Placeable C.page q (alignUp (nb + C.sizeSz) C.page))) := by
  unfold mremapChunk at h
  cases hf : mmFind? l c with
  | none => rw [hf] at h; cases h
  | some ch =>
    rw [hf] at h
    have hch : ch ∈ l.shared.mm.chunks := List.mem_of_find?_eq_some hf
    have hca : ch.addr = c := by simpa using List.find?_some hf
    dsimp only at h
    split at h
    · cases h
    rename_i hpg
    have hpg' : c % C.page = 0 ∧ ch.size % C.page = 0 := by
      simp only [ne_eq, not_or, Decidable.not_not] at hpg; exact hpg
    refine ⟨ch, hch, hca, hpg'.1, hpg'.2, ?_⟩
    split at h
    · rename_i heq
      injection h with h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      exact .inl ⟨heq, rfl, rfl⟩
    rename_i hne
    obtain ⟨hb1, hb2, hcase⟩ := mremap_spec l.kernel C.page c ch.size (alignUp (nb + C.sizeSz) C.page)
    generalize l.kernel.mremap C.page c ch.size (alignUp (nb + C.sizeSz) C.page) = r at h hb1 hb2 hcase
    obtain ⟨r1, k⟩ := r
    cases r1 with
    | none =>
      dsimp only at h
      injection h with h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      rcases hcase with ⟨-, hm⟩ | ⟨a', ha', -⟩
      · exact .inr (.inl ⟨hne, rfl, k, rfl, hb1, hb2, hm⟩)
      · cases ha'
    | some a' =>
      dsimp only at h
      injection h with h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      rcases hcase with ⟨h0, -⟩ | ⟨a'', ha'', hm, hpl⟩
      · cases h0
      · injection ha'' with ha''; subst ha''
        exact .inr (.inr ⟨hne, k, rfl, hb1, hb2, hm, hpl⟩)

theorem munmap_found {l l' : Local} {c : Nat} (h : munmapChunk C l c = .ok l') :
    ∃ ch ∈ l.shared.mm.chunks, ch.addr = c := by
  unfold munmapChunk at h
  cases hf : mmFind? l c with
  | none => rw [hf] at h; cases h
  | some ch => exact ⟨ch, List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf⟩

/-- A live payload at an `mmap`ed chunk's address is that chunk's. -/
theorem mm_payload (hC : C.Ok) {w : World} (hw : WorldWF C w) {tid : Nat} (ht : tid ∈ w.tids)
    {l : Local} (hl : w.local? tid w.mainArena = some l) {p u : Nat} (hpu : (p, u) ∈ w.live C)
    {ch : Chunk} (hch : ch ∈ w.shared.mm.chunks) (hca : ch.addr = p - C.hdr) :
    (p, u) = (ch.addr + C.hdr, ch.size - 2 * C.sizeSz) ∧ ch.use = .client := by
  have hwl := hw.locals tid _ l ht hl
  obtain ⟨-, -, -, -, -, -, hls, -⟩ := local?_fields hl
  have hp16 := live_ge_hdr hpu
  have h8 := hC.sizeSz
  rcases mem_live.mp hpu with ⟨⟨b, -, av, hab, hyb⟩, -⟩ | hm
  · exfalso
    obtain ⟨d, hd, -, hde⟩ := mem_out.mp hyb
    simp only [Prod.mk.injEq] at hde
    exact clash_mm hw hab hd hch (by unfold Config.hdr at *; omega)
  · obtain ⟨m, hm, hmu, hme⟩ := mem_shlive.mp hm
    simp only [Prod.mk.injEq] at hme
    have : m = ch := mm_addr_inj hwl (by rw [hls]; exact hm) (by rw [hls]; exact hch)
      (by unfold Config.hdr at *; omega)
    subst this
    exact ⟨by rw [hme.1, hme.2], hmu⟩

/-- The payload left after a `malloc` that returned `q ≠ 0`, with the old `(p, u)` then taken out. -/
theorem move_after_malloc {n q : Nat} {L₀ L₁ L₂ L₃ : List (Nat × Nat)} {x : Nat × Nat}
    (hL₁ : L₁.Perm L₀) (hx : x ∈ L₀) (hpos : 0 < x.2) (hML : MallocLive C n q L₁ L₂) (hq : q ≠ 0)
    (hL₃ : L₃.Perm (L₂.erase x)) : MallocLive C n q (L₀.erase x) L₃ ∧ x ∈ L₂ := by
  rcases hML with ⟨h0, -⟩ | ⟨-, hal, u₂, hn, hperm, hdis⟩
  · exact absurd h0 hq
  have hx1 : x ∈ L₁ := hL₁.symm.subset hx
  have hne : (q, u₂) ≠ x := by
    intro he; have := hdis x hx1; rw [← he] at this; simp only at this
    have : 0 < u₂ := by rw [← he] at hpos; exact hpos
    omega
  refine ⟨.inr ⟨hq, hal, u₂, hn, ?_, fun z hz => hdis z (hL₁.symm.subset (List.mem_of_mem_erase hz))⟩,
    hperm.symm.subset (List.mem_cons_of_mem _ hx1)⟩
  refine hL₃.trans ((hperm.erase x).trans ?_)
  rw [List.erase_cons_tail (by simpa [beq_iff_eq] using hne)]
  exact List.Perm.cons _ (hL₁.erase x)

/-! ## `realloc` -/

theorem realloc_wf (hC : C.Ok) (hB : Task.algo.bodyMalloc C) (hFb : Task.algo.bodyFree C)
    {w w' : World} {tid p u n q : Nat} (hw : WorldWF C w) (ht : tid ∈ w.tids)
    (hpu : (p, u) ∈ w.live C) (h : (ptmalloc C).realloc w tid p n = .ok (q, w')) :
    WorldWF C w' ∧ w'.tids = w.tids ∧
      ((n = 0 ∧ q = 0 ∧ (w'.live C).Perm ((w.live C).erase (p, u))) ∨
       (n ≠ 0 ∧ q = 0 ∧ (w'.live C).Perm (w.live C)) ∨
       (n ≠ 0 ∧ q ≠ 0 ∧ MallocLive C n q ((w.live C).erase (p, u)) (w'.live C))) := by
  have h8 := hC.sizeSz; have h16 := hC.align; have hpg := hC.page; have h32 := hC.minSize
  have hhdr : C.hdr = 16 := by unfold Config.hdr; omega
  have hp0 : p ≠ 0 := ((liveApart C hC w hw).2 _ hpu).1
  have hu0 : 0 < u := ((liveApart C hC w hw).2 _ hpu).2.1
  have hp16 := live_ge_hdr hpu
  unfold Ops.realloc at h
  replace h := bind_ok_inv h
  obtain ⟨w₁, h1, h⟩ := h
  try dsimp only at h
  obtain ⟨hw1, hl1, ht1, hi1, -, -⟩ := init_wf hw h1
  have ht1' : tid ∈ w₁.tids := ht1 ▸ ht
  have hpu1 : (p, u) ∈ w₁.live C := by rw [hl1]; exact hpu
  rw [← hl1]
  have hap1 := liveApart C hC _ hw1
  have hnd1 := live_nodup hC hw1
  -- `MallocLive` of an unchanged payload kept, big enough
  have keep : ∀ {w'' : World}, (w''.live C).Perm (w₁.live C) → n ≤ u →
      MallocLive C n p ((w₁.live C).erase (p, u)) (w''.live C) := fun hperm hn =>
    .inr ⟨hp0, live_align' hC hw1 hpu1, u, hn, hperm.trans (List.perm_cons_erase hpu1),
      fun z hz => by
        have ⟨hne, hz'⟩ := hnd1.mem_erase_iff.mp hz
        exact pairwise_of_mem (fun h => h.symm) hap1.1 hz' hpu1 hne⟩
  by_cases hn : n = 0 ∧ p ≠ 0
  · simp only [hn, ne_eq, not_false_eq_true, and_self, ↓reduceIte] at h
    replace h := bind_ok_inv h
    obtain ⟨w₂, h2, h⟩ := h
    try dsimp only at h
    injection h with h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have := free_wf hC hB hFb hw1 ht1' hpu1 h2
    exact ⟨this.1, (free_tids h2).trans ht1, .inl ⟨hn.1, rfl, this.2⟩⟩
  have hn0 : n ≠ 0 := fun h0 => hn ⟨h0, hp0⟩
  simp only [hn, ↓reduceIte, hp0] at h
  cases hmm : Ops.mmapped? w₁ (p - C.hdr) with
  | some ch =>
    simp only [hmm] at h
    -- an `mmap`ed chunk
    obtain ⟨hch, hca⟩ := mmapped?_some hmm
    obtain ⟨l₀, hl₀⟩ : ∃ l₀, w₁.local? tid w₁.mainArena = some l₀ :=
      local?_of_mem hw1 (List.mem_cons_self ..) tid
    obtain ⟨hpch, hcu⟩ := mm_payload hC hw1 ht1' hl₀ hpu1 hch hca
    simp only [Prod.mk.injEq] at hpch
    obtain ⟨hpe, hue⟩ := hpch
    by_cases hbad : (p - C.hdr) % C.align ≠ 0 ∨ 2 ^ 64 < p - C.hdr + ch.size
    · simp only [hbad, ↓reduceIte] at h; cases h
    simp only [hbad, ↓reduceIte] at h
    cases hnb : C.checkedRequest2size n with
    | none =>
      simp only [hnb] at h
      injection h with h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      have := setErrno_wf (tid := tid) (e := 12) hw1
      exact ⟨this.1, ht1, .inr (.inl ⟨hn0, rfl, by rw [this.2]⟩)⟩
    | some nb =>
    simp only [hnb] at h
    obtain ⟨hnb8, hnbA, hnbM⟩ := request2size_spec hC hnb
    replace h := bind_ok_inv h
    obtain ⟨l, hl, h⟩ := h
    try dsimp only at h
    replace h := bind_ok_inv h
    obtain ⟨⟨q₁, l₁⟩, hm, h⟩ := h
    try dsimp only at h
    obtain ⟨hwl, hspl, hl'⟩ := view_of hw1 ht1' hl
    obtain ⟨-, -, -, -, -, -, hls, -⟩ := local?_fields hl'
    have hchl : ch ∈ l.shared.mm.chunks := by rw [hls]; exact hch
    obtain ⟨ch', hch', hca', -, -, hcase⟩ := mremap_cases hm
    have hcc : ch' = ch := mm_addr_inj hwl hch' hchl (by rw [hca', hca])
    subst hcc
    obtain ⟨hal1, hal2⟩ := alignUp_page' hC (nb + C.sizeSz)
    rcases hcase with ⟨hsz, rfl, rfl⟩ | ⟨hsz, rfl, k, rfl, hk1, hk2, hk3⟩ | ⟨hsz, k, rfl, hk1, hk2, hk3, hpl⟩
    · -- kept: the chunk is big enough
      have hc0 : p - C.hdr ≠ 0 := by rw [← hca']; exact (hwl.shared.mm.nonNull ch' hchl)
      simp only [hc0, ne_eq, not_false_eq_true, ↓reduceIte] at h
      injection h with h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hw2, hl2⟩ := put_same hC hw1 ht1' hl' hwl
        (Frame.of_eq rfl rfl rfl rfl rfl rfl rfl hspl.covered) (keptAway_refl _) (List.Perm.refl _)
      refine ⟨hw2, ht1, .inr (.inr ⟨hn0, by omega, ?_⟩)⟩
      rw [show p - C.hdr + C.hdr = p by omega]
      exact keep hl2 (by omega)
    · -- refused
      obtain ⟨hwk, hpk, hFk, hKk, -⟩ := kernel_step hwl hspl hk1 hk2 hk3
      obtain ⟨hw2, hl2⟩ := put_same hC hw1 ht1' hl' hwk hFk hKk hpk
      simp only [ne_eq, not_true_eq_false, ↓reduceIte] at h
      by_cases hle : nb ≤ ch'.size - C.sizeSz
      · simp only [hle, ↓reduceIte] at h
        injection h with h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        exact ⟨hw2, ht1, .inr (.inr ⟨hn0, hp0, keep hl2 (by omega)⟩)⟩
      simp only [hle, ↓reduceIte] at h
      replace h := bind_ok_inv h
      obtain ⟨⟨q₂, w₃⟩, hm2, h⟩ := h
      try dsimp only at h
      have ht2 : tid ∈ (w₁.put tid { l with kernel := k }).tids := ht1'
      obtain ⟨hw3, hML⟩ := malloc_wf hC hB hw2 ht2 hm2
      have ht3 : tid ∈ w₃.tids := (malloc_tids hm2).symm ▸ ht2
      by_cases hq0 : q₂ = 0
      · simp only [hq0, ↓reduceIte] at h
        injection h with h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        rcases hML with ⟨-, hperm⟩ | ⟨h0, -⟩
        · exact ⟨hw3, (malloc_tids hm2).trans ht1, .inr (.inl ⟨hn0, rfl, hperm.trans hl2⟩)⟩
        · exact absurd hq0 h0
      simp only [hq0, ↓reduceIte] at h
      replace h := bind_ok_inv h
      obtain ⟨l₃, hl3, h⟩ := h
      try dsimp only at h
      replace h := bind_ok_inv h
      obtain ⟨l₄, hm4, h⟩ := h
      try dsimp only at h
      injection h with h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      have hl3' := localAt_inv hl3
      obtain ⟨-, -, -, -, -, -, hls3, -⟩ := local?_fields hl3'
      obtain ⟨ch₃, hch₃, hca₃⟩ := munmap_found hm4
      rw [hls3] at hch₃
      have hpu3 : (p, u) ∈ w₃.live C := by
        rcases hML with ⟨h0, -⟩ | ⟨-, -, u₂, -, hperm, -⟩
        · exact absurd h0 hq0
        · exact hperm.symm.subset (List.mem_cons_of_mem _ (hl2.symm.subset hpu1))
      obtain ⟨hpch₃, hcu₃⟩ := mm_payload hC hw3 ht3 hl3' hpu3 hch₃ hca₃
      rw [← hca₃] at hm4
      obtain ⟨hw4, hl4⟩ := mmUnmap_put hC hw3 ht3 hch₃ hcu₃ hl3' hm4
      rw [← hpch₃] at hl4
      exact ⟨hw4, (malloc_tids hm2).trans ht1, .inr (.inr ⟨hn0, hq0, (move_after_malloc hl2 hpu1 hu0 hML hq0 hl4).1⟩)⟩
    · -- moved
      have hs16 : C.hdr < alignUp (nb + C.sizeSz) C.page := by omega
      rw [← hca'] at hk3 hpl
      obtain ⟨hwm, hFm, hKm, hpm⟩ := mremap_body hC hwl hspl hchl hcu hk1 hk2 hk3 hpl hal2 hs16
      obtain ⟨ha0, haal, -, -, -, -⟩ := id hpl
      simp only [ha0, ne_eq, not_false_eq_true, ↓reduceIte] at h
      injection h with h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      have hold : (p, u) = (ch'.addr + C.hdr, ch'.size - 2 * C.sizeSz) := by
        rw [hpe, hue, hca']; try (congr 1; omega)
      rw [← hold] at hFm hpm
      have hpl' : (p, u) ∈ l.live C :=
        mem_llive.mpr (.inr (by rw [hold]; exact mem_shlive.mpr ⟨ch', hchl, hcu, rfl⟩))
      have hne : (q₁ + C.hdr, alignUp (nb + C.sizeSz) C.page - 2 * C.sizeSz) ≠ (p, u) := by
        rw [hold]; simp only [ne_eq, Prod.mk.injEq, not_and]; intro; omega
      obtain ⟨hw2, hl2, hap2⟩ := put_move hC hw1 ht1' hl' hwl hwm hFm hKm hpu1 hpl' hne hpm
      exact ⟨hw2, ht1, .inr (.inr ⟨hn0, by omega, mallocLive_move (by omega)
        (by rw [h16]; rw [hpg] at haal; omega) (by omega) hl2 hap2⟩)⟩
  | none =>
    simp only [hmm] at h
    -- an arena chunk
    replace h := bind_ok_inv h
    obtain ⟨w₂, h2, h⟩ := h
    try dsimp only at h
    have c2 := tcacheInit_wf hC hB hw1 ht1' hi1 (h2 : tcacheInit C w₁ tid = _)
    have ht2 : tid ∈ w₂.tids := c2.tids ▸ ht1'
    have hpu2 : (p, u) ∈ w₂.live C := c2.live.symm.subset hpu1
    cases ha : Ops.arenaOf w₂ (p - C.hdr) with
    | none => simp only [ha] at h; cases h
    | some a =>
    simp only [ha] at h
    obtain ⟨-, av, hav, d, hd, hda⟩ := arenaOf_some ha
    replace h := bind_ok_inv h
    obtain ⟨l, hl, h⟩ := h
    try dsimp only at h
    obtain ⟨hwl, hspl, hl'⟩ := view_of c2.wf ht2 hl
    obtain ⟨av', hav', hlav, -, -, -, hls, -⟩ := local?_fields hl'
    rw [hav] at hav'; cases hav'
    have hdl : d ∈ l.av.chunks := by rw [hlav]; exact hd
    have hal : (p, u) ∈ l.arenaLive C := arenaLive_at hC c2.wf ht2 hl' hpu2 hdl hda
    have hpl : (p, u) ∈ l.live C := arenaLive_sub hal
    by_cases hbad : (p - C.hdr) % C.align ≠ 0 ∨ 2 ^ 64 < p - C.hdr + l.av.tiles.sizeAt (p - C.hdr)
    · simp only [hbad, ↓reduceIte] at h; cases h
    simp only [hbad, ↓reduceIte] at h
    cases hnb : C.checkedRequest2size n with
    | none =>
      simp only [hnb] at h
      injection h with h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      have := setErrno_wf (tid := tid) (e := 12) c2.wf
      exact ⟨this.1, c2.tids.trans ht1, .inr (.inl ⟨hn0, rfl, by rw [this.2]; exact c2.live⟩)⟩
    | some nb =>
    simp only [hnb] at h
    obtain ⟨hnb8, hnbA, hnbM⟩ := request2size_spec hC hnb
    replace h := bind_ok_inv h
    obtain ⟨⟨q₁, l₁⟩, hr, h⟩ := h
    try dsimp only at h
    have hi2 : l.shared.init = true := by rw [hls, c2.init]; exact hi1
    obtain ⟨hwl₁, hKl₁, hres⟩ := bodyRealloc C hC l l₁ p u nb q₁ hwl hspl hi2 hal hnbA hnbM hr
    rcases hres with ⟨rfl, hF, hperm⟩ | ⟨rfl, rfl, hu⟩ | ⟨hq1, hF, u', hu', hne, hperm⟩
    · -- refused
      obtain ⟨hw3, hl3⟩ := put_same hC c2.wf ht2 hl' hwl₁ hF hKl₁ hperm
      have hl3' := hl3.trans c2.live
      by_cases hsg : (w₂.put tid l₁).single = true
      · simp only [hsg, true_or, ↓reduceIte] at h
        injection h with h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        exact ⟨hw3, c2.tids.trans ht1, .inr (.inl ⟨hn0, rfl, hl3'⟩)⟩
      simp only [hsg, ne_eq, not_true_eq_false, or_self, Bool.false_eq_true, ↓reduceIte] at h
      replace h := bind_ok_inv h
      obtain ⟨⟨q₂, w₄⟩, hm2, h⟩ := h
      try dsimp only at h
      have ht3 : tid ∈ (w₂.put tid l₁).tids := ht2
      obtain ⟨hw4, hML⟩ := malloc_wf hC hB hw3 ht3 hm2
      have ht4 : tid ∈ w₄.tids := (malloc_tids hm2).symm ▸ ht3
      by_cases hq0 : q₂ = 0
      · simp only [hq0, ↓reduceIte] at h
        injection h with h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        rcases hML with ⟨-, hperm'⟩ | ⟨h0, -⟩
        · exact ⟨hw4, ((malloc_tids hm2).trans c2.tids).trans ht1, .inr (.inl ⟨hn0, rfl, hperm'.trans hl3'⟩)⟩
        · exact absurd hq0 h0
      simp only [hq0, ↓reduceIte] at h
      replace h := bind_ok_inv h
      obtain ⟨l₅, hl5, h⟩ := h
      try dsimp only at h
      replace h := bind_ok_inv h
      obtain ⟨l₆, hf6, h⟩ := h
      try dsimp only at h
      injection h with h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      obtain ⟨hwl5, hspl5, hl5'⟩ := view_of hw4 ht4 hl5
      obtain ⟨d₅, hd₅, hda₅, -⟩ := intFree_chunk hf6
      have hpu4 : (p, u) ∈ w₄.live C := by
        rcases hML with ⟨h0, -⟩ | ⟨-, -, u₂, -, hperm', -⟩
        · exact absurd h0 hq0
        · exact hperm'.symm.subset (List.mem_cons_of_mem _ (hl3'.symm.subset hpu1))
      have hal5 := arenaLive_at hC hw4 ht4 hl5' hpu4 hd₅ hda₅
      obtain ⟨hwl6, hF6, hK6, hperm6⟩ := hFb hC l₅ l₆ p u hwl5 hspl5 hal5 hf6
      obtain ⟨hw6, hl6⟩ := put_free hC hw4 ht4 hl5' hwl5 hwl6 hF6 hK6 hpu4 (arenaLive_sub hal5) hperm6
      exact ⟨hw6, ((malloc_tids hm2).trans c2.tids).trans ht1, .inr (.inr ⟨hn0, hq0, (move_after_malloc hl3' hpu1 hu0 hML hq0 hl6).1⟩)⟩
    · -- the old chunk kept as it is
      obtain ⟨hw3, hl3⟩ := put_same hC c2.wf ht2 hl' hwl
        (Frame.of_eq rfl rfl rfl rfl rfl rfl rfl hspl.covered) (keptAway_refl _) (List.Perm.refl _)
      simp only [hp0, ne_eq, not_false_eq_true, or_true, ↓reduceIte] at h
      injection h with h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      exact ⟨hw3, c2.tids.trans ht1, .inr (.inr ⟨hn0, hp0, keep (hl3.trans c2.live) (by omega)⟩)⟩
    · -- moved or resized
      obtain ⟨hw3, hl3, hap3⟩ := put_move hC c2.wf ht2 hl' hwl hwl₁ hF hKl₁ hpu2 hpl hne hperm
      simp only [hq1, ne_eq, not_false_eq_true, or_true, ↓reduceIte] at h
      injection h with h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
      have hmem : (q₁, u') ∈ l₁.live C := hperm.symm.subset (List.mem_cons_self ..)
      refine ⟨hw3, c2.tids.trans ht1, .inr (.inr ⟨hn0, hq1, ?_⟩)⟩
      refine mallocLive_move hq1 (live_align hC hwl₁ hmem) (by omega) (hl3.trans
        (List.Perm.cons _ (c2.live.erase _))) fun z hz => hap3 z ((c2.live.erase _).symm.subset hz)

/-- **`Algo.wfCallocRealloc`** (= `Task.algo.wfCallocRealloc C (ptmalloc C)`). -/
theorem wfCallocRealloc (C : Config) : Task.algo.wfCallocRealloc C (ptmalloc C) := fun hC _ _ hw ht =>
  ⟨fun _ _ _ _ h => let r := calloc_wf hC (bodyMalloc_all C) hw ht h; ⟨r.1, r.2.2⟩,
   fun _ _ _ _ _ hpu h => let r := realloc_wf hC (bodyMalloc_all C) (bodyFree C) hw ht hpu h; ⟨r.1, r.2.2⟩⟩

/-- **`Algo.noAbort`** (= `Task.algo.noAbort C (ptmalloc C)`): `_int_malloc` and `_int_free` of a
live arena payload never abort on a view with its spatial facts. -/
theorem noAbort (C : Config) : Task.algo.noAbort C (ptmalloc C) := fun hC l hw hsp =>
  ⟨fun n => totalMalloc_cons C (sysMainTotal C) (sysHeapTotal C) hC l hw hsp n,
   fun p u h => totalFree C hC l hw hsp p u h⟩

end Silmaril.Libc.Ptmalloc.Algo
