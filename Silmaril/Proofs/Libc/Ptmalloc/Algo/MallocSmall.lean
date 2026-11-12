module

public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocFast

/-!
# ptmalloc algorithm: the small-bin path of `_int_malloc`

`Algo.mallocSmallBody` (`Task.algo.mallocSmallBody`): `last (bin)` of `smallbin_index (nb)` is
lent out (`Take.body`), then the tcache refill from the same bin parks one chunk per turn
(`Take.park`). Every chunk of small bin `i` has `bin_index (size) = i` (`BinsWF.size`), so its size
is `nb` (a large size has a bin index of 64 or more).
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

variable {C : Config}

theorem largeIndex_ge (s : Nat) (h : 1024 ≤ s) : 64 ≤ Config.largeIndex s := by
  unfold Config.largeIndex
  split
  · omega
  · split
    · omega
    · split
      · omega
      · split
        · omega
        · split <;> omega

/-- A size in small bin `binIndex nb` (a small request) is `nb`. -/
theorem binIndex_small_inj (hC : C.Ok) {s nb : Nat} (hnb : C.inSmallRange nb = true)
    (hs : s % C.align = 0) (hn : nb % C.align = 0) (h : C.binIndex s = C.binIndex nb) : s = nb := by
  obtain ⟨-, -, hml⟩ := hC.bins
  have hA := hC.align
  have hsm : C.minLargeSize = 1024 := by rw [hml, hC.bins.2.1, hA]
  unfold Config.binIndex Config.inSmallRange at *
  simp only [decide_eq_true_eq] at hnb
  simp only [hnb, decide_true, ↓reduceIte] at h
  rw [hA] at hs hn h
  split at h
  · omega
  · rename_i hl
    simp only [decide_eq_true_eq, Nat.not_lt] at hl
    have := largeIndex_ge s (by omega)
    omega

theorem mem_of_last? {bs : BinsSt} {i v : Nat} (h : bs.last? i = some v) : v ∈ bs.lists i := by
  unfold BinsSt.last? at h
  exact List.mem_of_getLast? h

/-- **A small-bin removal** lends out a chunk of the bin. -/
theorem binRemove_take {l : Local} (hw : LocalWF C l) {i v : Nat} (hi : 2 ≤ i)
    (hv : v ∈ l.av.bins.lists i) :
    ∃ d, d.addr = v ∧ d.use = .bin i ∧ Take C l (l.binRemove v i .client) d := by
  have hwl := (leafBinRemove hw hv (.inl rfl)).1
  obtain ⟨d, hdv, hda, hdu⟩ := (hw.arena.bins.exact i hi v).mp hv
  have hd : d ∈ l.av.tiles.heapChunks := (List.mem_filter.mp hdv).1
  refine ⟨d, hda, hdu, ?_⟩
  subst hda
  exact
    { wf := hwl, avAddr := rfl, isMain := rfl, thread := rfl, shared := rfl, kernel := rfl,
      mem := hd, use := by rw [hdu]; exact nofun, tiles := rfl, heaps := rfl }

theorem small_size (hC : C.Ok) {l : Local} (hw : LocalWF C l) {d : Chunk} (hd : d ∈ l.av.chunks)
    {nb : Nat} (hdu : d.use = .bin (C.binIndex nb)) (hnb : C.inSmallRange nb = true)
    (hnbA : nb % C.align = 0) (hi2 : 2 ≤ C.binIndex nb) : d.size = nb := by
  have := (hw.arena.bins.size d (List.mem_filter.mpr ⟨hd, by
    rw [hdu]; simp only [Use.isSorted, decide_eq_true_eq]; exact hi2⟩) _ hdu).2.2
  exact binIndex_small_inj hC hnb (hw.arena.tiles.sizes d hd).1 hnbA this

theorem binIndex_ge2 (hC : C.Ok) {nb : Nat} (hnb : C.inSmallRange nb = true) (hm : C.minSize ≤ nb) :
    2 ≤ C.binIndex nb := by
  unfold Config.binIndex; simp only [hnb, ↓reduceIte]; rw [hC.align]; rw [hC.minSize] at hm; omega

/-- **The tcache refill from a small bin** is an `MStep`. -/
theorem smallRefill_step (hC : C.Ok) {t nb : Nat} (hnb : C.inSmallRange nb = true)
    (hnbA : nb % C.align = 0) (hnbM : C.minSize ≤ nb) (ht : C.tidx nb = t) (htb : t < C.tcacheBins) :
    ∀ fuel l, LocalWF C l → LocalSp C l → l.thread.tcache.isSome →
      MStep C l (smallRefill C (C.binIndex nb) t fuel l)
  | 0, l, hw, hsp, _ => mstep_refl hw hsp
  | fuel + 1, l, hw, hsp, hts => by
    unfold smallRefill
    split
    · rename_i hcnt
      split
      · exact mstep_refl hw hsp
      · rename_i v hv
        obtain ⟨d, hda, hdu, T⟩ := binRemove_take hw (binIndex_ge2 hC hnb hnbM) (mem_of_last? hv)
        subst hda
        have hds := small_size hC hw T.mem hdu hnb hnbA (binIndex_ge2 hC hnb hnbM)
        obtain ⟨tc, htc⟩ := Option.isSome_iff_exists.mp hts
        have htc₁ : (l.binRemove d.addr (C.binIndex nb) .client).thread.tcache = some tc := by
          rw [T.thread]; exact htc
        have hroom : (tc.bins t).length < C.tcacheCount := by
          simp only [tcCount, htc, Option.map_some, Option.getD_some] at hcnt; exact hcnt
        dsimp only
        rw [sizeAt_take hw T]
        have S := T.park hC hw hsp htc₁ htb (by rw [hds]; exact ht) hroom
        exact S.trans hC hw hsp (smallRefill_step hC hnb hnbA hnbM ht htb fuel _ S.1
          (S.sp hC hw hsp) (tcPut_isSome (by rw [htc₁]; rfl)))
    · exact mstep_refl hw hsp

/-- **`Task.algo.mallocSmallBody`**. -/
theorem mallocSmallBody (C : Config) : Task.algo.mallocSmallBody C := by
  intro hC l l' n nb p hw hsp hnb hsm h
  obtain ⟨hnbA, hnbM, hnbN⟩ := nb_props hC hnb
  unfold mallocSmall at h
  dsimp only at h
  split at h
  · cases h
  · rename_i v hv
    injection h with h
    injection h with h1 h2
    subst h1; subst h2
    obtain ⟨d, hda, hdu, T⟩ := binRemove_take hw (binIndex_ge2 hC hsm hnbM) (mem_of_last? hv)
    subst hda
    have hds := small_size hC hw T.mem hdu hsm hnbA (binIndex_ge2 hC hsm hnbM)
    have B := T.body hC hw hsp (n := n) (by omega)
    split
    · rename_i hon
      simp only [tcOn, Bool.and_eq_true, decide_eq_true_eq] at hon
      have hsp₁ := LocalSp.of_frame hC hw hsp (T.frame hw hsp)
      exact B.step hC hw hsp (smallRefill_step hC hsm hnbA hnbM rfl hon.2 _ _ T.wf hsp₁ hon.1)
    · exact B

end Silmaril.Libc.Ptmalloc.Algo
