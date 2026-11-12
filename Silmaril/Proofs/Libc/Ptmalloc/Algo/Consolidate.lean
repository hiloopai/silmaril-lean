module

public import Silmaril.Proofs.Libc.Ptmalloc.Algo.Coalesce

/-!
# ptmalloc algorithm: `malloc_consolidate` (`Task.algo.wfConsolidate`)

`malloc_consolidate` clears `have_fastchunks`, then pops every fastbin chunk (held `internal`)
and coalesces it. Its intermediate states are well formed up to that flag (`LocalWF C l.hf`), and
each pop + coalesce is a `ConsStep` (well formed up to the flag, only the arena changed, the
lent-out payloads kept): the pop by `consPop_step` (components Fastbins + Top), the coalescing by
`Algo.coalesce_spec`. After the last bin every fastbin is empty, so the flag is irrelevant again.

`Algo.wfConsolidate : ∀ C, Task.algo.wfConsolidate C`.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

variable {C : Config}

/-- A step of `malloc_consolidate`: well formed up to `have_fastchunks`, only the arena changed,
the lent-out payloads kept. -/
structure ConsStep (C : Config) (l l' : Local) : Prop where
  wf : LocalWF C l'.hf
  eq : l' = { l with av := l'.av }
  out : l'.av.out C = l.av.out C
  cover : SpanCover l l'
  heaps : l'.av.heaps = l.av.heaps
  start : l'.av.tiles.start = l.av.tiles.start
  /-- `have_fastchunks` is never raised (`malloc_consolidate` clears it first). -/
  fastOff : l.av.fast.haveFast = false → l'.av.fast.haveFast = false

theorem ConsStep.refl {l : Local} (hw : LocalWF C l.hf) : ConsStep C l l :=
  ⟨hw, rfl, rfl, SpanCover.refl l, rfl, rfl, id⟩

theorem ConsStep.trans {l l₁ l₂ : Local} (h₁ : ConsStep C l l₁) (h₂ : ConsStep C l₁ l₂) :
    ConsStep C l l₂ where
  wf := h₂.wf
  eq := by rw [h₂.eq, h₁.eq]
  out := h₂.out.trans h₁.out
  cover := h₁.cover.trans h₂.cover
  heaps := h₂.heaps.trans h₁.heaps
  start := h₂.start.trans h₁.start
  fastOff h := h₂.fastOff (h₁.fastOff h)

theorem ArenaStep.cons {l l' : Local} (h : ArenaStep C l l') : ConsStep C l l' :=
  ⟨h.wf, h.eq, h.out, h.cover, h.heaps, h.start, fun h0 => by rw [h.fast]; exact h0⟩

theorem FastSt.pop_hf {fs fs' : FastSt} {i p : Nat} (h : fs.pop i = some (p, fs')) :
    ({ fs with haveFast := true } : FastSt).pop i = some (p, { fs' with haveFast := true }) := by
  unfold FastSt.pop at h ⊢
  split at h
  · cases h
  · rename_i b rest hl
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [hl]

theorem FastSt.pop_lists {fs fs' : FastSt} {i p : Nat} (h : fs.pop i = some (p, fs')) :
    fs.lists i = p :: fs'.lists i ∧ (∀ j, j ≠ i → fs'.lists j = fs.lists j) ∧ fs'.haveFast = fs.haveFast := by
  unfold FastSt.pop at h
  split at h
  · cases h
  · rename_i b rest hl
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨by simp [hl], fun j hj => by simp [hj], rfl⟩

/-- **A fastbin pop of `malloc_consolidate`**: the chunk held `internal`. -/
theorem consPop_step {l : Local} (hw : LocalWF C l.hf) {i p : Nat} {fs : FastSt}
    (hp : l.av.fast.pop i = some (p, fs)) :
    ConsStep C l { l with av := { l.av with fast := fs, tiles := l.av.tiles.relabel p .internal } } ∧
      ∃ d ∈ l.av.tiles.heapChunks, d.addr = p ∧
        (⟨p, d.size, .internal⟩ : Chunk) ∈ (l.av.tiles.relabel p .internal).heapChunks := by
  have ht : TopWF C l.av.tiles := hw.arena.tiles
  have hn := ht.nodup
  have hp' := FastSt.pop_hf hp
  have hb : p ∈ l.av.fast.lists i := by rw [(FastSt.pop_lists hp).1]; exact List.mem_cons_self ..
  have hfw : FastWF C l.hf.av.fast l.av.fastView := hw.arena.fast
  obtain ⟨d, hdv, hda, hdu⟩ := (hfw.exact i p).mp hb
  have hd : d ∈ l.av.tiles.heapChunks := (List.mem_filter.mp hdv).1
  have ht' := ht.relabel (a := p) (u := .internal) rfl
  have ha := hw.arena.withFast (l.av.tiles.relabel p .internal) { fs with haveFast := true } ht'
    (by rw [TopSt.heapChunks_relabel]
        exact (FastWF.of_all (fun j => hfw.exact_all j) hfw.nodup
          (fun c hc k hk => hfw.size c (List.mem_filter.mpr ⟨hc, by rw [hk]; rfl⟩) k hk)
          hfw.flag).pop hn hp' rfl)
    (view_relabel_of hn hd hda (by rw [hdu]; rfl) rfl) (TopSt.sizeAt_relabel ..)
    (view_relabel_of hn hd hda (by rw [hdu]; rfl) rfl)
    (fun c hc _ => ht'.minSize_all c hc)
  refine ⟨⟨hw.withAv _ ha rfl rfl rfl rfl (TopSt.relabel_old_nil ..) (TopSt.spans_relabel ..), rfl,
    ArenaSt.out_congr (view_relabel_of hn hd hda (by rw [hdu]; rfl) (by simp)),
    spanCover_relabel rfl rfl, rfl, rfl, fun h0 => (FastSt.pop_lists hp).2.2.trans h0⟩, d, hd, hda, ?_⟩
  rw [TopSt.heapChunks_relabel]
  exact mem_map_relabelAt.mpr (.inl ⟨d, hd, hda, by rw [hda]⟩)

/-- **One fastbin, chunk by chunk.** -/
theorem consolidateBin_spec (i : Nat) : ∀ (fuel : Nat) {l l' : Local}, LocalWF C l.hf →
    consolidateBin i fuel l = .ok l' →
    ConsStep C l l' ∧ ((l.av.fast.lists i).length ≤ fuel → l'.av.fast.lists i = []) ∧
      ∀ j, j ≠ i → l'.av.fast.lists j = l.av.fast.lists j
  | 0, l, l', hw, h => by
    simp only [consolidateBin] at h; cases h
    exact ⟨ConsStep.refl hw, fun hl => List.eq_nil_of_length_eq_zero (by omega), fun _ _ => rfl⟩
  | fuel + 1, l, l', hw, h => by
    simp only [consolidateBin] at h
    cases hp : l.av.fast.pop i with
    | none =>
      rw [hp] at h; cases h
      refine ⟨ConsStep.refl hw, fun _ => ?_, fun _ _ => rfl⟩
      unfold FastSt.pop at hp; split at hp
      · assumption
      · cases hp
    | some v =>
      obtain ⟨p, fs⟩ := v
      rw [hp] at h
      simp only at h
      obtain ⟨hst₁, d, hd, hda, hd'⟩ := consPop_step hw hp
      have ht₁ : TopWF C (l.av.tiles.relabel p .internal) := hst₁.wf.arena.tiles
      obtain ⟨R₁, s, pre, post, R₂, hr, ha⟩ := runs_of_chunk ht₁ hd'
      cases hc : coalesce { l with av := { l.av with fast := fs, tiles := l.av.tiles.relabel p .internal } } p with
      | error e => rw [hc] at h; cases h
      | ok v =>
        obtain ⟨r, l₂⟩ := v
        rw [hc, ok_bind] at h
        simp only at h
        simp only at hr ha
        have hst₂ := coalesce_spec' (l := { l with av := { l.av with fast := fs, tiles := l.av.tiles.relabel p .internal } })
          hst₁.wf hr ha hc
        obtain ⟨hst₃, hlen, hoth⟩ := consolidateBin_spec i fuel hst₂.wf h
        have hpl := FastSt.pop_lists hp
        have hf₂ : l₂.av.fast = fs := hst₂.fast
        refine ⟨hst₁.trans (hst₂.cons.trans hst₃), fun hl => hlen ?_, fun j hj => ?_⟩
        · rw [hf₂]; rw [hpl.1] at hl; simp at hl; omega
        · rw [hoth j hj, hf₂, hpl.2.1 j hj]

theorem consolidate_fold : ∀ (is : List Nat) {l l' : Local}, LocalWF C l.hf →
    is.foldlM (fun l i => consolidateBin i ((l.av.fast.lists i).length) l) l = .ok l' →
    ConsStep C l l' ∧ (∀ j ∈ is, l'.av.fast.lists j = []) ∧ ∀ j, j ∉ is → l'.av.fast.lists j = l.av.fast.lists j
  | [], l, l', hw, h => by
    simp only [List.foldlM_nil] at h; cases h
    exact ⟨ConsStep.refl hw, by simp, fun _ _ => rfl⟩
  | i :: is, l, l', hw, h => by
    rw [List.foldlM_cons] at h
    cases hc : consolidateBin i ((l.av.fast.lists i).length) l with
    | error e => rw [hc] at h; cases h
    | ok l₁ =>
      rw [hc, ok_bind] at h
      obtain ⟨hst₁, hl₁, ho₁⟩ := consolidateBin_spec i _ hw hc
      obtain ⟨hst₂, hl₂, ho₂⟩ := consolidate_fold is hst₁.wf h
      refine ⟨hst₁.trans hst₂, fun j hj => ?_, fun j hj => ?_⟩
      · rcases List.mem_cons.mp hj with rfl | hj
        · by_cases hjs : j ∈ is
          · exact hl₂ j hjs
          · rw [ho₂ j hjs]; exact hl₁ (Nat.le_refl _)
        · exact hl₂ j hj
      · rw [List.mem_cons, not_or] at hj
        rw [ho₂ j hj.2, ho₁ j hj.1]

/-- **`Algo.wfConsolidate`**. -/
theorem wfConsolidate (C : Config) : Task.algo.wfConsolidate C := by
  intro _ l l' hw h
  unfold consolidate at h
  have hw0 : LocalWF C ({ l with av := { l.av with fast := { l.av.fast with haveFast := false } } } : Local).hf :=
    hw.hf
  obtain ⟨hst, hl, ho⟩ := consolidate_fold _ hw0 h
  have hempty : ∀ i, l'.av.fast.lists i = [] := by
    intro i
    by_cases hi : i ∈ List.range C.nFast
    · exact hl i hi
    · rw [ho i hi]
      simp only
      rw [List.mem_range] at hi
      cases hli : l.av.fast.lists i with
      | nil => rfl
      | cons b rest =>
        exfalso
        obtain ⟨c, hc, -, hcu⟩ := (hw.arena.fast.exact i b).mp (by rw [hli]; exact List.mem_cons_self ..)
        exact hi (hw.arena.fast.size c hc i hcu).2.2
  refine ⟨hst.wf.of_hf fun ⟨i, hi⟩ => absurd (hempty i) hi, ?_, ?_, hempty⟩
  · rw [hst.eq]; simp [Footprint.Within]
  · rw [hst.out]; exact List.Perm.refl _
