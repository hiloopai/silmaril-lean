module

public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocTake

/-!
# ptmalloc algorithm: the fastbin path of `_int_malloc`

`Algo.mallocFastBody`, `Algo.mallocFastTotal` (`Task.algo.mallocFastBody`/`mallocFastTotal`): the
head of fastbin `fastbin_index (nb)` is lent out (`Take.body`), then the tcache refill from the
same fastbin parks one chunk per turn (`Take.park`). Every chunk of fastbin `i` has
`fastbin_index (size) = i` (`FastWF.size`), so its size is `nb` and it fits tcache bin
`csize2tidx (nb)`; its address is a chunk address, so aligned: neither check aborts.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

variable {C : Config}

theorem MallocLive.perm_right {n p : Nat} {live live' live'' : List (Nat × Nat)} (hp : live''.Perm live')
    (h : MallocLive C n p live live') : MallocLive C n p live live'' := by
  rcases h with ⟨h0, h1⟩ | ⟨h0, h1, u, hu, h2, h3⟩
  · exact .inl ⟨h0, hp.trans h1⟩
  · exact .inr ⟨h0, h1, u, hu, hp.trans h2, h3⟩

/-- **A body, then a step, is a body.** -/
theorem MBody.step (hC : C.Ok) {n p : Nat} {l l₁ l₂ : Local} (hw : LocalWF C l) (hsp : LocalSp C l)
    (h₁ : MBody C n l p l₁) (h₂ : MStep C l₁ l₂) : MBody C n l p l₂ :=
  ⟨⟨h₂.1, within_trans h₁.1.2.1 (within_of_frame h₂.2.2.1), MallocLive.perm_right h₂.2.1 h₁.1.2.2⟩,
    h₁.2.1.trans h₂.2.2.1,
    KeptAway.trans hC hw hsp h₁.2.1 h₁.2.2.1 h₂.2.2.2.1, fun h => h₂.2.2.2.2 (h₁.2.2.2 h)⟩

/-- The sizes of a request: aligned, at least `MINSIZE`, at least `n + SIZE_SZ`. -/
theorem nb_props (hC : C.Ok) {n nb : Nat} (hnb : C.checkedRequest2size n = some nb) :
    nb % C.align = 0 ∧ C.minSize ≤ nb ∧ n + C.sizeSz ≤ nb := by
  have hnbE : nb = C.request2size n := by
    unfold Config.checkedRequest2size at hnb; split at hnb <;> simp_all
  rw [hnbE]; exact request2size_props hC n

theorem fidx_inj (hC : C.Ok) {a b : Nat} (ha : a % C.align = 0) (hb : b % C.align = 0)
    (ha' : C.minSize ≤ a) (hb' : C.minSize ≤ b) (h : C.fidx a = C.fidx b) : a = b := by
  unfold Config.fidx at h
  rw [hC.sizeSz] at h; rw [hC.align] at ha hb; rw [hC.minSize] at ha' hb'
  omega

/-- **The fastbin pop** lends out a chunk of the bin. -/
theorem fastPop_take {l l₁ : Local} (hw : LocalWF C l) {i a : Nat} (h : l.fastPop i = some (a, l₁)) :
    ∃ d, d.addr = a ∧ d.use = .fast i ∧ Take C l l₁ d := by
  have hwl := (leafFastPop hw h).1
  unfold Local.fastPop at h
  cases hp : l.av.fast.pop i with
  | none => rw [hp] at h; cases h
  | some r =>
    obtain ⟨b, fs'⟩ := r
    rw [hp] at h
    simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hb : b ∈ l.av.fast.lists i := by
      unfold FastSt.pop at hp; split at hp
      · cases hp
      · rename_i c rest hl; simp only [Option.some.injEq, Prod.mk.injEq] at hp
        rw [hl, ← hp.1]; exact List.mem_cons_self ..
    obtain ⟨d, hdv, hda, hdu⟩ := (hw.arena.fast.exact i b).mp hb
    have hd : d ∈ l.av.tiles.heapChunks := (List.mem_filter.mp hdv).1
    refine ⟨d, hda, hdu, ?_⟩
    subst hda
    exact
      { wf := hwl, avAddr := rfl, isMain := rfl, thread := rfl, shared := rfl, kernel := rfl,
        mem := hd, use := by rw [hdu]; exact nofun, tiles := rfl, heaps := rfl }

/-- A chunk of fastbin `i` for the request `nb` (`fastbin_index (nb) = i`) has size `nb`. -/
theorem fast_size (hC : C.Ok) {l : Local} (hw : LocalWF C l) {d : Chunk} (hd : d ∈ l.av.chunks)
    {i : Nat} (hdu : d.use = .fast i) {nb : Nat} (hi : C.fidx nb = i) (hnbA : nb % C.align = 0)
    (hnbM : C.minSize ≤ nb) : d.size = nb := by
  have := (hw.arena.fast.size d (List.mem_filter.mpr ⟨hd, by rw [hdu]; rfl⟩) i hdu).1
  have hs := hw.arena.tiles.sizes d hd
  exact fidx_inj hC hs.1 hnbA hs.2 hnbM (this.trans hi.symm)

theorem sizeAt_take {l l₁ : Local} {d : Chunk} (hw : LocalWF C l) (T : Take C l l₁ d) :
    l₁.av.tiles.sizeAt d.addr = d.size := by
  rw [T.tiles, TopSt.sizeAt_relabel]
  exact TopSt.sizeAt_of_mem hw.arena.tiles.nodup T.mem

theorem fast_head_aligned {l : Local} (hw : LocalWF C l) {i a : Nat} {rest : List Nat}
    (h : l.av.fast.lists i = a :: rest) : a % C.align = 0 := by
  obtain ⟨d, hdv, hda, -⟩ := (hw.arena.fast.exact i a).mp (by rw [h]; exact List.mem_cons_self ..)
  rw [← hda]; exact hw.arena.tiles.aligned d (List.mem_filter.mp hdv).1

theorem fast_pop_some {l : Local} {i a : Nat} {rest : List Nat} (h : l.av.fast.lists i = a :: rest) :
    ∃ l₁, l.fastPop i = some (a, l₁) := by
  unfold Local.fastPop FastSt.pop; rw [h]; exact ⟨_, rfl⟩

theorem tcPut_isSome {l : Local} {c : Nat × Nat} {t : Nat} (h : l.thread.tcache.isSome) :
    (tcPut l c t).thread.tcache.isSome := by
  cases ht : l.thread.tcache with
  | none => rw [ht] at h; cases h
  | some tc => simp [tcPut, Local.tcachePut, ht]

/-- **The tcache refill from a fastbin** is an `MStep`. -/
theorem fastRefill_step (hC : C.Ok) {i t nb : Nat} (hi : C.fidx nb = i) (hnbA : nb % C.align = 0)
    (hnbM : C.minSize ≤ nb) (ht : C.tidx nb = t) (htb : t < C.tcacheBins) :
    ∀ fuel l l', LocalWF C l → LocalSp C l → l.thread.tcache.isSome →
      fastRefill C i t fuel l = .ok l' → MStep C l l'
  | 0, l, l', hw, hsp, _, h => by
    simp only [fastRefill] at h; injection h with h; subst h; exact mstep_refl hw hsp
  | fuel + 1, l, l', hw, hsp, hts, h => by
    unfold fastRefill at h
    split at h
    · rename_i hcnt
      split at h
      · injection h with h; subst h; exact mstep_refl hw hsp
      · rename_i a rest hl
        split at h
        · cases h
        · split at h
          · injection h with h; subst h; exact mstep_refl hw hsp
          · rename_i a' l₁ hpop
            obtain ⟨d, rfl, hdu, T⟩ := fastPop_take hw hpop
            have hds := fast_size hC hw T.mem hdu hi hnbA hnbM
            obtain ⟨tc, htc⟩ := Option.isSome_iff_exists.mp hts
            have htc₁ : l₁.thread.tcache = some tc := by rw [T.thread]; exact htc
            have hroom : (tc.bins t).length < C.tcacheCount := by
              simp only [tcCount, htc, Option.map_some, Option.getD_some] at hcnt; exact hcnt
            rw [sizeAt_take hw T] at h
            have S := T.park hC hw hsp htc₁ htb (by rw [hds]; exact ht) hroom
            have S' := fastRefill_step hC hi hnbA hnbM ht htb fuel _ l' S.1 (S.sp hC hw hsp)
              (tcPut_isSome (by rw [htc₁]; rfl)) h
            exact S.trans hC hw hsp S'
    · injection h with h; subst h; exact mstep_refl hw hsp

/-- The tcache refill from a fastbin does not abort. -/
theorem fastRefill_total (hC : C.Ok) {i t nb : Nat} (hi : C.fidx nb = i) (hnbA : nb % C.align = 0)
    (hnbM : C.minSize ≤ nb) (ht : C.tidx nb = t) (htb : t < C.tcacheBins) :
    ∀ fuel l, LocalWF C l → LocalSp C l → l.thread.tcache.isSome →
      ∃ l', fastRefill C i t fuel l = .ok l'
  | 0, l, _, _, _ => ⟨l, rfl⟩
  | fuel + 1, l, hw, hsp, hts => by
    unfold fastRefill
    split
    · rename_i hcnt
      split
      · exact ⟨_, rfl⟩
      · rename_i a rest hl
        rw [ite_eq_right_of_eq_false _ _ (eq_false (by have := fast_head_aligned hw hl; omega))]
        obtain ⟨l₁, hpop⟩ := fast_pop_some hl
        rw [hpop]
        obtain ⟨d, hda, hdu, T⟩ := fastPop_take hw hpop
        subst hda
        have hds := fast_size hC hw T.mem hdu hi hnbA hnbM
        obtain ⟨tc, htc⟩ := Option.isSome_iff_exists.mp hts
        have htc₁ : l₁.thread.tcache = some tc := by rw [T.thread]; exact htc
        have hroom : (tc.bins t).length < C.tcacheCount := by
          simp only [tcCount, htc, Option.map_some, Option.getD_some] at hcnt; exact hcnt
        dsimp only
        rw [sizeAt_take hw T]
        have S := T.park hC hw hsp htc₁ htb (by rw [hds]; exact ht) hroom
        exact fastRefill_total hC hi hnbA hnbM ht htb fuel _ S.1 (S.sp hC hw hsp)
          (tcPut_isSome (by rw [htc₁]; rfl))
    · exact ⟨_, rfl⟩

/-- **`Task.algo.mallocFastBody`**. -/
theorem mallocFastBody (C : Config) : Task.algo.mallocFastBody C := by
  intro hC l l' n nb p hw hsp hnb _ h
  obtain ⟨hnbA, hnbM, hnbN⟩ := nb_props hC hnb
  unfold mallocFast at h
  dsimp only at h
  split at h
  · cases h
  · rename_i a rest hl
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i a' l₁ hpop
        obtain ⟨d, rfl, hdu, T⟩ := fastPop_take hw hpop
        have hds := fast_size hC hw T.mem hdu rfl hnbA hnbM
        split at h
        · cases h
        · have B := T.body hC hw hsp (n := n) (by omega)
          split at h
          · rename_i hon
            cases hr : fastRefill C (C.fidx nb) (C.tidx nb) C.tcacheCount l₁ with
            | error e => rw [hr] at h; cases h
            | ok l₂ =>
              rw [hr] at h
              injection h with h; injection h with h; injection h with h1 h2
              subst h1; subst h2
              simp only [tcOn, Bool.and_eq_true, decide_eq_true_eq] at hon
              have hw₁ := T.wf
              have hsp₁ := LocalSp.of_frame hC hw hsp (T.frame hw hsp)
              exact B.step hC hw hsp
                (fastRefill_step hC rfl hnbA hnbM rfl hon.2 _ _ _ hw₁ hsp₁ hon.1 hr)
          · injection h with h; injection h with h; injection h with h1 h2
            subst h1; subst h2; exact B

/-- **`Task.algo.mallocFastTotal`**. -/
theorem mallocFastTotal (C : Config) : Task.algo.mallocFastTotal C := by
  intro hC l n nb hw hsp hnb _
  obtain ⟨hnbA, hnbM, hnbN⟩ := nb_props hC hnb
  unfold mallocFast
  dsimp only
  split
  · exact ⟨_, rfl⟩
  · rename_i a rest hl
    rw [ite_eq_right_of_eq_false _ _ (eq_false (by have := fast_head_aligned hw hl; omega))]
    obtain ⟨l₁, hpop⟩ := fast_pop_some hl
    rw [hpop]
    dsimp only
    obtain ⟨d, hda, hdu, T⟩ := fastPop_take hw hpop
    subst hda
    have hds := fast_size hC hw T.mem hdu rfl hnbA hnbM
    rw [sizeAt_take hw T, ite_eq_right_of_eq_false _ _ (eq_false (by rw [hds]; exact fun h => h rfl))]
    split
    · rename_i hon
      simp only [tcOn, Bool.and_eq_true, decide_eq_true_eq] at hon
      have hsp₁ := LocalSp.of_frame hC hw hsp (T.frame hw hsp)
      obtain ⟨l₂, hr⟩ := fastRefill_total hC rfl hnbA hnbM rfl hon.2 C.tcacheCount l₁ T.wf hsp₁ hon.1
      rw [hr]; exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

end Silmaril.Libc.Ptmalloc.Algo
