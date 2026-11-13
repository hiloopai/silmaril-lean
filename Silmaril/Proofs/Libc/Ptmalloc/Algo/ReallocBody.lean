module

public import Silmaril.Proofs.Libc.Ptmalloc.Algo.ReallocSteps
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocCons
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocHeap
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocSysMain

/-!
# ptmalloc algorithm: `_int_realloc` (`Task.algo.bodyRealloc`, `Task.algo.wfIntRealloc`)

`_int_realloc`'s paths on a lent-out, not parked chunk of the arena:

* **keep / shrink** (`nb ≤ oldsize`): `reallocSplit_spec`;
* **grow into top** (the chunk is the current segment's last one): `growTop_spec`;
* **grow into a free next chunk**: `unlink_step`, `fuseClient`, then the split (`path3_spec`);
* **allocate, copy, free** (`reallocCopy_spec`): `_int_malloc` (`Task.algo.bodyMalloc`, proved),
  then either the in-place fusion with the new chunk (glibc's `newp == next`) and the split, or
  `_int_free` of the old chunk (`Algo.bodyFree`).

Each is well formed after, has a `Frame` freeing at most the old payload, and replaces the old
payload by one of at least `nb - SIZE_SZ` bytes (or, `_int_malloc` having failed, keeps the live
set). `Algo.bodyRealloc : Task.algo.bodyRealloc C` and `Algo.wfIntRealloc : Task.algo.wfIntRealloc C`.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

variable {C : Config}

/-- The conclusion of `Task.algo.bodyRealloc` for a run of `_int_realloc` (or one of its paths)
from `l` to `l'` returning `q`, the old payload being `x`. -/
def RBody (C : Config) (l : Local) (x : Nat × Nat) (nb q : Nat) (l' : Local) : Prop :=
  LocalWF C l' ∧ KeptAway l l' ∧
    ((q = 0 ∧ Frame C l l' [] ∧ (l'.live C).Perm (l.live C)) ∨ (q = x.1 ∧ l' = l ∧ nb - C.sizeSz ≤ x.2) ∨
     (q ≠ 0 ∧ Frame C l l' [x] ∧
       ∃ u', nb - C.sizeSz ≤ u' ∧ (q, u') ≠ x ∧ (l'.live C).Perm ((q, u') :: (l.live C).erase x)))

theorem bodyMalloc_all (C : Config) : Task.algo.bodyMalloc C :=
  bodyMalloc_cons C (sysMainBody C) (sysHeapBody C)

/-! ## After a fusion: the split below -/

/-- **The split below after the old chunk grew in place** to a lent-out chunk of `S ≥ nb` bytes at
its address. -/
theorem split_after (hC : C.Ok) {l l₂ l₃ : Local} {q : Nat} (hw : LocalWF C l) (hsp : LocalSp C l)
    {ch : Chunk} (hch : ch ∈ l.av.chunks)
    (hF : Frame C l l₂ [(ch.addr + C.hdr, ch.size - C.sizeSz)]) (hK : KeptAway l l₂)
    (hw₂ : LocalWF C l₂) (hsp₂ : LocalSp C l₂) {S : Nat} (hS : ch.size < S)
    (hD : (⟨ch.addr, S, .client⟩ : Chunk) ∈ l₂.av.chunks)
    (hnpD : (ch.addr + C.hdr, S - C.sizeSz) ∉ l₂.thread.parked C)
    (hlive : (l₂.live C).Perm ((ch.addr + C.hdr, S - C.sizeSz) ::
      (l.live C).erase (ch.addr + C.hdr, ch.size - C.sizeSz)))
    {nb : Nat} (hnb : nb % C.align = 0) (hmin : C.minSize ≤ nb) (hgt : ch.size < nb) (hle : nb ≤ S)
    (h : reallocSplit C l₂ ch.addr S nb = .ok (q, l₃)) :
    RBody C l (ch.addr + C.hdr, ch.size - C.sizeSz) nb q l₃ := by
  have h8 := hC.sizeSz; have h32 := hC.minSize
  have hhdr : C.hdr = 16 := by unfold Config.hdr; omega
  have hcpos := (hw.arena.tiles.sizes ch hch).2
  obtain ⟨hq, hw₃, hF₃, hK₃, hcase, hfresh⟩ :=
    reallocSplit_spec hC hw₂ hsp₂ (d := ⟨ch.addr, S, .client⟩) hD rfl hnpD hnb hmin hle h
  simp only at hq hF₃ hcase hfresh
  subst hq
  have hn := hw.arena.tiles.nodup
  obtain ⟨u', hu', hne', hlive₃⟩ : ∃ u', nb - C.sizeSz ≤ u' ∧ u' ≠ ch.size - C.sizeSz ∧
      (l₃.live C).Perm ((ch.addr + C.hdr, u') :: (l₂.live C).erase (ch.addr + C.hdr, S - C.sizeSz)) := by
    rcases hcase with ⟨rfl, -⟩ | ⟨-, hl⟩
    · exact ⟨S - C.sizeSz, by omega, by omega, List.perm_cons_erase (hlive.symm.subset (List.mem_cons_self ..))⟩
    · exact ⟨nb - C.sizeSz, Nat.le_refl _, by omega, hl⟩
  refine ⟨hw₃, KeptAway.trans' hC hw hsp hF hK hK₃,
    .inr (.inr ⟨by omega, ?_, u', hu', fun he => hne' (by simp only [Prod.mk.injEq] at he; exact he.2), ?_⟩)⟩
  · refine Frame.comp hw₂ hF hF₃ (fun c hc hcu' hn' => ⟨hn', ?_⟩) ?_ (fun e he => .inl he) ?_
    · intro hm
      simp only [List.mem_singleton, usable, Bool.false_eq_true, ite_false, Prod.mk.injEq] at hm
      apply hn'
      have : c = ch := chunk_unique hn hc hch (by omega)
      subst this; simp [usable]
    · intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact hnpD
    · intro tc' i e ht he hnot hfr
      have hea : e.1 ≠ ch.addr := by
        rcases hfresh tc' i e ht he with h' | h'
        · exact absurd h' hnot
        · exact h'
      right
      intro c hc hca hcu'
      rcases hfr with hm | hm
      · simp only [List.mem_singleton, Prod.mk.injEq] at hm; omega
      · have hcne : c ≠ ch := by rintro rfl; exact hea hca.symm
        apply hm c (hF.clients c hc hcu' ?_) hca hcu'
        intro hm'
        simp only [List.mem_singleton, usable, Bool.false_eq_true, ite_false, Prod.mk.injEq] at hm'
        exact hcne (chunk_unique hn hc hch (by omega))
  · refine hlive₃.trans (List.Perm.cons _ ?_)
    have := hlive.erase (ch.addr + C.hdr, S - C.sizeSz)
    rw [List.erase_cons_head] at this
    exact this

/-! ## Growing into a free next chunk -/

/-- **`_int_realloc`'s growth into a free next chunk** (`unlink_chunk`, fuse, split below). -/
theorem path3_spec (hC : C.Ok) {l l' : Local} {q : Nat} (hw : LocalWF C l) (hsp : LocalSp C l)
    {ch : Chunk} (hch : ch ∈ l.av.chunks) (hcu : ch.use = .client)
    (hnp : (ch.addr + C.hdr, ch.size - C.sizeSz) ∉ l.thread.parked C)
    {R₁ R₂ : List (Nat × List (Nat × Use))} {s : Nat} {pre post : List (Nat × Use)} {e : Nat × Use}
    (hr : l.av.tiles.runs = R₁ ++ (s, pre ++ (ch.size, .client) :: e :: post) :: R₂)
    (ha : s + runLen pre = ch.addr) (hfree : e.2.tagFree = true) {nb : Nat}
    (hnb : nb % C.align = 0) (hmin : C.minSize ≤ nb) (hgt : ch.size < nb) (hfit : nb ≤ ch.size + e.1)
    (h : (do
      let l₁ ← unlink l (ch.addr + ch.size) .internal
      reallocSplit C (fuse l₁ ch.addr .client) ch.addr (ch.size + e.1) nb) = .ok (q, l')) :
    RBody C l (ch.addr + C.hdr, ch.size - C.sizeSz) nb q l' := by
  have h8 := hC.sizeSz; have h32 := hC.minSize
  have hn := hw.arena.tiles.nodup
  have hnmem := TopSt.mem_of_runs_next hr
  simp only at hnmem
  rw [ha] at hnmem
  obtain ⟨l₁, hu, hAS, ht₁⟩ := unlink_step (C := C) hw.hf hnmem hfree
  obtain ⟨l₁', h1, h⟩ := bind_ok_inv h
  simp only at hu
  rw [hu] at h1; injection h1 with h1; subst h1
  have hw₁ : LocalWF C l₁ :=
    LocalWF.of_hf hAS.wf (fun hx => by rw [hAS.fast] at hx ⊢; exact hw.arena.fast.flag hx)
  have hth₁ : l₁.thread = l.thread := by rw [hAS.eq]
  have hsh₁ : l₁.shared = l.shared := by rw [hAS.eq]
  have hk₁ : l₁.kernel = l.kernel := by rw [hAS.eq]
  have hm₁ : l₁.isMain = l.isMain := by rw [hAS.eq]
  have hav₁ : l₁.avAddr = l.avAddr := by rw [hAS.eq]
  have har₁ : l₁.thread.arena = l.thread.arena := by rw [hth₁]
  have hr2 : l.av.tiles.runs = R₁ ++ (s, (pre ++ [(ch.size, .client)]) ++ e :: post) :: R₂ := by
    rw [hr]; simp
  have ha2 : s + runLen (pre ++ [(ch.size, .client)]) = ch.addr + ch.size := by
    rw [runLen_append]; simp only [runLen_cons, runLen_nil]; omega
  have hr₁ : l₁.av.tiles.runs = R₁ ++ (s, pre ++ (ch.size, .client) :: (e.1, .internal) :: post) :: R₂ := by
    rw [ht₁, TopSt.runs_relabel .internal hr2 ha2 hn]; simp
  obtain ⟨hw₂, hcov₂, -, hkeep₂, hD₂, R, hR, hR'⟩ := fuseClient hw₁ (v := .internal) (.inr rfl) hr₁
  rw [ha] at hw₂ hcov₂ hkeep₂ hD₂ hR hR'
  simp only [reduceCtorEq, ite_false, List.append_nil] at hR
  rw [hAS.out] at hR
  -- the frame of unlink + fuse
  have hnc : (⟨ch.addr + ch.size, e.1, e.2⟩ : Chunk).use ≠ .client := not_client_of_free hfree
  have hcl : ∀ c ∈ l.av.chunks, c.use = .client →
      (c.addr + C.hdr, usable C c false) ∉ [(ch.addr + C.hdr, ch.size - C.sizeSz)] →
      c ∈ (fuse l₁ ch.addr .client).av.chunks := by
    intro c hc hcu' hn'
    have hc₁ : c ∈ l₁.av.chunks := by
      show c ∈ l₁.av.tiles.heapChunks
      rw [ht₁, TopSt.heapChunks_relabel]
      exact keep_clients hn hnmem rfl hnc c hc hcu'
    refine hkeep₂ c hc₁ (fun hca => hn' ?_) (fun hca => ?_)
    · have : c = ch := chunk_unique hn hc hch hca
      subst this; simp [usable]
    · have := chunk_unique hn hc hnmem hca
      rw [this] at hcu'; exact hnc hcu'
  have hthr₂ : (fuse l₁ ch.addr .client).thread = l.thread := hth₁
  have hF₁₂ : Frame C l (fuse l₁ ch.addr .client) [(ch.addr + C.hdr, ch.size - C.sizeSz)] :=
    frame_of hsp hw₂.apart hav₁ hsh₁ har₁
      (Shrink.of_arena hk₁ hm₁ (hAS.cover.trans hcov₂) hAS.heaps) hcl
      (fun tc' i e' ht he => .inl ⟨tc', i, by rw [← hthr₂]; exact ht, he⟩)
  have hK₁₂ : KeptAway l (fuse l₁ ch.addr .client) :=
    fun tc _ _ ht he _ => ⟨tc, by rw [hthr₂]; exact ht, he⟩
  have hsp₂ := LocalSp.of_frame' hC hw hsp hF₁₂ (by simpa using hnp)
  have hepos : 0 < e.1 := by have := (hw.arena.tiles.sizes _ hnmem).2; simp only at this; omega
  have hcpos : 0 < ch.size := by have := (hw.arena.tiles.sizes _ hch).2; omega
  have hnpD : (ch.addr + C.hdr, ch.size + e.1 - C.sizeSz) ∉ (fuse l₁ ch.addr .client).thread.parked C := by
    rw [hthr₂]
    exact not_parked_inside hC hw hsp hch (Nat.le_refl _) (by omega) (by omega) (by omega)
  have hlive : ((fuse l₁ ch.addr .client).live C).Perm ((ch.addr + C.hdr, ch.size + e.1 - C.sizeSz) ::
      (l.live C).erase (ch.addr + C.hdr, ch.size - C.sizeSz)) := by
    obtain ⟨hL, hL'⟩ := live_of_out_perm (C := C) (l := l) (l' := fuse l₁ ch.addr .client) hthr₂
      (show (fuse l₁ ch.addr .client).shared = l.shared from hsh₁) hR hR'
      (by simpa using hnp) (by simpa [hthr₂] using hnpD)
    refine hL'.trans ?_
    have := (hL.erase (ch.addr + C.hdr, ch.size - C.sizeSz)).symm
    simp only [List.cons_append, List.nil_append, List.erase_cons_head] at this ⊢
    exact List.Perm.cons _ this
  exact split_after hC hw hsp hch hF₁₂ hK₁₂ hw₂ hsp₂ (by omega) hD₂ hnpD hlive hnb hmin hgt hfit h

/-! ## Allocate, copy, free -/

/-- **`_int_realloc`'s fallback** (`reallocCopy`): `_int_malloc`, then the in-place fusion with
glibc's `next` or the copy and `_int_free` of the old chunk. -/
theorem reallocCopy_spec (hC : C.Ok) {l l' : Local} {q : Nat} (hw : LocalWF C l) (hsp : LocalSp C l)
    (hi : l.shared.init = true) {ch : Chunk} (hch : ch ∈ l.av.chunks) (hcu : ch.use = .client)
    (hnp : (ch.addr + C.hdr, ch.size - C.sizeSz) ∉ l.thread.parked C) {nb : Nat}
    (hnb : nb % C.align = 0) (hmin : C.minSize ≤ nb) (hgt : ch.size < nb)
    (h : reallocCopy C l ch.addr ch.size nb = .ok (q, l')) :
    RBody C l (ch.addr + C.hdr, ch.size - C.sizeSz) nb q l' := by
  have h8 := hC.sizeSz; have h32 := hC.minSize; have h16 := hC.align
  have hhdr : C.hdr = 16 := by unfold Config.hdr; omega
  have hold : (ch.addr + C.hdr, ch.size - C.sizeSz) ∈ l.live C :=
    mem_llive.mpr (.inl ⟨mem_out.mpr ⟨ch, hch, hcu, rfl⟩, hnp⟩)
  unfold reallocCopy at h
  obtain ⟨⟨p, l₁⟩, hm, h⟩ := bind_ok_inv h
  obtain ⟨⟨hw₁, -, hML⟩, hF₁, hK₁, -⟩ := bodyMalloc_all C hC l l₁ _ p hw hsp hi hm
  have hsp₁ := LocalSp.of_frame hC hw hsp hF₁
  have hch₁ : ch ∈ l₁.av.chunks := hF₁.clients ch hch hcu (by simp)
  dsimp only at h
  split at h
  next hp0 =>
    injection h with h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    rcases hML with ⟨-, hperm⟩ | ⟨hp, -⟩
    · exact ⟨hw₁, hK₁, .inl ⟨rfl, hF₁, hperm⟩⟩
    · exact absurd hp0 hp
  rename_i hp0
  obtain ⟨u₁, hu₁, hperm₁, hdis₁⟩ : ∃ u₁, nb - C.alignMask ≤ u₁ ∧ (l₁.live C).Perm ((p, u₁) :: l.live C) ∧
      ∀ q ∈ l.live C, q.1 + q.2 ≤ p ∨ p + u₁ ≤ q.1 := by
    rcases hML with ⟨h0, -⟩ | ⟨-, -, u₁, h1, h2, h3⟩
    · exact absurd h0 hp0
    · exact ⟨u₁, h1, h2, h3⟩
  have hp_live : (p, u₁) ∈ l₁.live C := hperm₁.symm.subset (List.mem_cons_self ..)
  have hold₁ : (ch.addr + C.hdr, ch.size - C.sizeSz) ∈ l₁.live C :=
    hperm₁.symm.subset (List.mem_cons_of_mem _ hold)
  have hold₁a : (ch.addr + C.hdr, ch.size - C.sizeSz) ∈ l₁.arenaLive C :=
    arenaLive_of hw₁ hold₁ (mem_out.mpr ⟨ch, hch₁, hcu, rfl⟩)
  have hu0 : 0 < u₁ := ((llive_apart hC hw₁).2 _ hp_live).2.1
  have hpne : (p, u₁) ≠ (ch.addr + C.hdr, ch.size - C.sizeSz) := by
    intro he
    have := hdis₁ _ hold
    rw [← he] at this
    simp only at this; omega
  have hmod := live_mod hC hw₁ hp_live
  have hu₁' : nb - C.sizeSz ≤ u₁ := by
    have hm15 : C.alignMask = 15 := by unfold Config.alignMask; omega
    have hnb16 : nb % 16 = 0 := by rw [← h16]; exact hnb
    rw [hm15] at hu₁
    simp only at hmod
    omega
  have hn₁ := hw₁.arena.tiles.nodup
  split at h
  next hadj₀ =>
    -- glibc's `newp == next`: fuse in place, then split below
    have hadj : p - C.hdr = ch.addr + ch.size := hadj₀
    split at h
    next => cases h
    rename_i hguard
    obtain ⟨R₁, s, pre, post, R₂, hr, ha⟩ := runs_of_chunk hw₁.arena.tiles hch₁
    rw [hcu] at hr
    have hloc := TopSt.locate_of_runs hr ha hn₁
    rw [hloc] at h
    rcases post with _ | ⟨e, post⟩
    · by_cases hR : R₂ = [] <;> simp [hR] at h
    simp only [List.head?_cons, Option.map_some, Option.getD_some] at h
    split at h
    rotate_left
    · cases h
    have hnmem := TopSt.mem_of_runs_next hr
    simp only at hnmem
    rw [ha] at hnmem
    -- the new chunk is `next`, lent out
    have hne : e.2 = .client ∧ e.1 - C.sizeSz = u₁ := by
      rcases mem_llive.mp hp_live with ⟨hpo, -⟩ | hps
      · obtain ⟨c, hc, hcu', hce⟩ := mem_out.mp hpo
        simp only [Prod.mk.injEq] at hce
        have : c = ⟨ch.addr + ch.size, e.1, e.2⟩ := chunk_unique hn₁ hc hnmem (by simp only; omega)
        subst this
        exact ⟨hcu', hce.2.symm⟩
      · exfalso
        obtain ⟨m, hm', -, hme⟩ := mem_shlive.mp hps
        simp only [Prod.mk.injEq] at hme
        exact addr_clash hw₁.apart (r := (ch.addr + ch.size, e.1)) (span_mem_spans hnmem)
          (List.mem_map.mpr ⟨m, hm', rfl⟩) (by simp only; omega)
    obtain ⟨e1, e2⟩ := e
    simp only at hne hnmem h
    obtain ⟨rfl, rfl⟩ := hne
    have hpe : p = ch.addr + ch.size + C.hdr := by
      have := (hw.arena.tiles.sizes _ hch).2; omega
    subst hpe
    obtain ⟨hw₂, hcov₂, -, hkeep₂, hD₂, R, hR, hR'⟩ := fuseClient hw₁ (v := .client) (.inl rfl) hr
    rw [ha] at hw₂ hcov₂ hkeep₂ hD₂ hR hR'
    simp only [ite_true] at hR
    have hnpay₁ : (ch.addr + ch.size + C.hdr, e1 - C.sizeSz) ∈ l₁.arenaLive C :=
      arenaLive_of hw₁ hp_live (mem_out.mpr ⟨_, hnmem, rfl, rfl⟩)
    -- the frame of the fusion
    have hF₁₂ : Frame C l₁ (fuse l₁ ch.addr .client)
        [(ch.addr + C.hdr, ch.size - C.sizeSz), (ch.addr + ch.size + C.hdr, e1 - C.sizeSz)] := by
      refine frame_of hsp₁ hw₂.apart rfl rfl rfl (Shrink.of_arena rfl rfl hcov₂ rfl) ?_
        (fun tc' i e' ht he => .inl ⟨tc', i, ht, he⟩)
      intro c hc hcu' hn'
      refine hkeep₂ c hc (fun hca => hn' ?_) (fun hca => hn' ?_)
      · have : c = ch := chunk_unique hn₁ hc hch₁ hca
        subst this; simp [usable]
      · have : c = ⟨ch.addr + ch.size, e1, .client⟩ := chunk_unique hn₁ hc hnmem hca
        subst this; simp [usable]
    have hFl₂ : Frame C l (fuse l₁ ch.addr .client)
        [(ch.addr + ch.size + C.hdr, e1 - C.sizeSz), (ch.addr + C.hdr, ch.size - C.sizeSz)] := by
      refine Frame.comp hw₁ hF₁ hF₁₂ (fun c _ _ hn' => ⟨by simp, fun hm => hn' ?_⟩) ?_
        (fun e he => by simp at he) ?_
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm ⊢; exact hm.symm
      · intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl
        · exact arenaLive_not_parked hold₁a
        · exact arenaLive_not_parked hnpay₁
      · intro tc' i e' ht he hnot _
        exact absurd ⟨tc', i, ht, he⟩ hnot
    have hFl₂' : Frame C l (fuse l₁ ch.addr .client) [(ch.addr + C.hdr, ch.size - C.sizeSz)] := by
      refine Frame.drop hFl₂ fun c hc hcu' hca => hguard ?_
      simp only at hca
      simp only [List.any_eq_true, decide_eq_true_eq]
      exact ⟨c, hc, by omega, hcu'⟩
    have hKl₂ : KeptAway l (fuse l₁ ch.addr .client) :=
      KeptAway.trans' hC hw hsp hF₁ hK₁ fun tc _ _ ht he _ => ⟨tc, ht, he⟩
    have hsp₂ := LocalSp.of_frame' hC hw hsp hFl₂' (by simpa using hnp)
    have hepos : 0 < e1 := by have := (hw₁.arena.tiles.sizes _ hnmem).2; simp only at this; omega
    have hnpD : (ch.addr + C.hdr, ch.size + e1 - C.sizeSz) ∉ (fuse l₁ ch.addr .client).thread.parked C :=
      not_parked_inside hC hw₁ hsp₁ hch₁ (Nat.le_refl _)
        (by have := (hw.arena.tiles.sizes _ hch).2; omega) (by omega) (by omega)
    have hlive : ((fuse l₁ ch.addr .client).live C).Perm ((ch.addr + C.hdr, ch.size + e1 - C.sizeSz) ::
        (l.live C).erase (ch.addr + C.hdr, ch.size - C.sizeSz)) := by
      obtain ⟨hL, hL'⟩ := live_of_out_perm (C := C) (l := l₁) (l' := fuse l₁ ch.addr .client) rfl rfl hR hR'
        (by simp [arenaLive_not_parked hold₁a, arenaLive_not_parked hnpay₁])
        (by simpa using (show (ch.addr + C.hdr, ch.size + e1 - C.sizeSz) ∉ l₁.thread.parked C from hnpD))
      refine hL'.trans (List.Perm.cons _ ?_)
      simp only [List.cons_append, List.nil_append] at hL
      have h3 := hperm₁.symm.trans hL
      have h4 : (l.live C).Perm ((ch.addr + C.hdr, ch.size - C.sizeSz) ::
          (List.filter (fun pu => !(l₁.thread.parked C).contains pu) R ++ l₁.shared.live C)) := by
        have := h3.trans (List.Perm.swap _ _ _).symm
        exact (List.perm_cons _).mp this
      have := h4.erase (ch.addr + C.hdr, ch.size - C.sizeSz)
      rw [List.erase_cons_head] at this
      exact this.symm
    exact split_after hC hw hsp hch hFl₂' hKl₂ hw₂ hsp₂ (by omega) hD₂ hnpD hlive hnb hmin hgt (by omega) h
  next =>
    -- copy and free
    obtain ⟨l₂, hfr, h⟩ := bind_ok_inv h
    injection h with h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
    have hfr' : intFree C l₁ (ch.addr + C.hdr - C.hdr) = .ok l₂ := by rw [Nat.add_sub_cancel]; exact hfr
    obtain ⟨hw₂, hF₂, hK₂, hlive₂⟩ := bodyFree C hC l₁ l₂ _ _ hw₁ hsp₁ hold₁a hfr'
    refine ⟨hw₂, KeptAway.trans' hC hw hsp hF₁ hK₁ hK₂, .inr (.inr ⟨hp0, ?_, u₁, hu₁', hpne, ?_⟩)⟩
    · refine Frame.comp hw₁ hF₁ hF₂ (fun c _ _ hn' => ⟨by simp, hn'⟩) ?_ (fun e he => by simp at he) ?_
      · intro x hx; simp only [List.mem_singleton] at hx; subst hx; exact arenaLive_not_parked hold₁a
      · intro tc' i e _ _ _ hfr
        rcases hfr with hm | hm
        · exact .inl hm
        · right; intro c hc hca hcu'; exact hm c (hF₁.clients c hc hcu' (by simp)) hca hcu'
    · refine hlive₂.trans ?_
      have := hperm₁.erase (ch.addr + C.hdr, ch.size - C.sizeSz)
      rw [List.erase_cons_tail (by simpa [beq_iff_eq] using hpne)] at this
      exact this

/-! ## `_int_realloc` -/

/-- **`Algo.bodyRealloc`** (= `Task.algo.bodyRealloc`). -/
theorem bodyRealloc (C : Config) : Task.algo.bodyRealloc C := by
  intro hC l l' p u nb q hw hsp hi hpu hnb hmin h
  have h8 := hC.sizeSz; have h32 := hC.minSize
  obtain ⟨ch, hch, hcu, rfl, rfl, hnp, -, -, -⟩ := intFree_open hC hw hpu
  have hpc : ch.addr + C.hdr - C.hdr = ch.addr := by omega
  rw [hpc] at h
  have hn := hw.arena.tiles.nodup
  have hsz : l.av.tiles.sizeAt ch.addr = ch.size := TopSt.sizeAt_of_mem hn hch
  rw [hsz] at h
  have hu : usable C ch false = ch.size - C.sizeSz := by simp [usable]
  rw [hu]
  obtain ⟨R₁, s, pre, post, R₂, hr, ha⟩ := runs_of_chunk hw.arena.tiles hch
  rw [hcu] at hr
  have hloc := TopSt.locate_of_runs hr ha hn
  unfold intRealloc at h
  rw [hloc] at h
  simp only [ne_eq, not_true_eq_false, or_self, ↓reduceIte] at h
  split at h
  next hle =>
    obtain ⟨hq, hw', hF, hK, hcase, -⟩ :=
      reallocSplit_spec hC hw hsp hch hcu hnp hnb hmin hle h
    subst hq
    rcases hcase with ⟨rfl, -⟩ | ⟨hrem, hlive⟩
    · exact ⟨hw', hK, .inr (.inl ⟨rfl, rfl, by show nb - C.sizeSz ≤ ch.size - C.sizeSz; omega⟩)⟩
    · exact ⟨hw', hK, .inr (.inr ⟨by unfold Config.hdr; omega, hF, _, Nat.le_refl _,
        by simp only [ne_eq, Prod.mk.injEq, not_and]; intro; omega, hlive⟩)⟩
  next hgt =>
    have hgt : ch.size < nb := by omega
    rcases post with _ | ⟨e, post⟩
    · by_cases hR : R₂ = []
      · subst hR
        simp only [List.head?_nil, Option.map_none, Option.getD_none, ↓reduceIte] at h
        split at h
        next hz =>
          injection h with h; simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
          obtain ⟨-, hc⟩ := TopSt.runs_eq_append_singleton hr
          simp only [Prod.mk.injEq] at hc
          obtain ⟨hs, hc⟩ := hc
          rw [← hs] at ha
          obtain ⟨hw', hF, hK, hlive⟩ := growTop_spec hC hw hsp hch hcu hnp hc ha hnb hmin hgt hz
          exact ⟨hw', hK, .inr (.inr ⟨by unfold Config.hdr; omega, hF, _, Nat.le_refl _,
            by simp only [ne_eq, Prod.mk.injEq, not_and]; intro; omega, hlive⟩)⟩
        next => exact reallocCopy_spec hC hw hsp hi hch hcu hnp hnb hmin hgt h
      · simp only [List.head?_nil, Option.map_none, Option.getD_none, hR, ↓reduceIte] at h
        exact reallocCopy_spec hC hw hsp hi hch hcu hnp hnb hmin hgt h
    · simp only [List.head?_cons, Option.map_some, Option.getD_some] at h
      split at h
      next hfit =>
        exact path3_spec hC hw hsp hch hcu hnp hr ha hfit.1 hnb hmin hgt hfit.2 h
      next => exact reallocCopy_spec hC hw hsp hi hch hcu hnp hnb hmin hgt h

/-- A live payload is aligned. -/
theorem live_align (hC : C.Ok) {l : Local} (hw : LocalWF C l) {y : Nat × Nat} (hy : y ∈ l.live C) :
    y.1 % C.align = 0 := by
  have h16 := hC.align; have h8 := hC.sizeSz; have hpg := hC.page
  have hhdr : C.hdr = 16 := by unfold Config.hdr; omega
  rcases mem_llive.mp hy with ⟨hyo, -⟩ | hys
  · obtain ⟨c, hc, -, rfl⟩ := mem_out.mp hyo
    have := hw.arena.tiles.aligned c hc
    simp only; rw [h16] at this ⊢; omega
  · obtain ⟨m, hm, hmu, rfl⟩ := mem_shlive.mp hys
    have := (hw.shared.mm.page m hm hmu).1
    simp only; rw [h16]; rw [hpg] at this; omega

/-- **`Algo.wfIntRealloc`** (= `Task.algo.wfIntRealloc`). -/
theorem wfIntRealloc (C : Config) : Task.algo.wfIntRealloc C := by
  intro hC l l' oldp oldsize nb q u hw hsp hi hpu hsz hnb hmin h
  have hpc : oldp + C.hdr - C.hdr = oldp := by omega
  rw [← hsz, ← hpc] at h
  obtain ⟨hw', -, hres⟩ := bodyRealloc C hC l l' _ u nb q hw hsp hi hpu hnb hmin h
  rcases hres with ⟨rfl, hF, hperm⟩ | ⟨hq', hl', hu⟩ | ⟨hq, hF, u', hu', -, hperm⟩
  · exact ⟨hw', within_of_frame hF, .inl ⟨rfl, by simpa using hperm.erase _⟩⟩
  · refine ⟨hw', by rw [hl']; exact within_empty rfl rfl, ?_⟩
    rw [hl', hq']
    have hmem : (oldp + C.hdr, u) ∈ l.live C := arenaLive_sub hpu
    have hq : oldp + C.hdr ≠ 0 := ((llive_apart hC hw).2 _ hmem).1
    simp only [hq, ↓reduceIte]
    have hap := llive_apart hC hw
    have hnd := nodup_of_liveApart hap
    refine .inr ⟨hq, live_align hC hw hmem, u, hu, List.perm_cons_erase hmem, fun y hy => ?_⟩
    have ⟨hne, hy'⟩ := hnd.mem_erase_iff.mp hy
    exact pairwise_of_mem (fun h => h.symm) hap.1 hy' hmem hne
  · refine ⟨hw', within_of_frame hF, ?_⟩
    simp only [hq, ↓reduceIte]
    have hap := llive_apart hC hw'
    have hnd := nodup_of_liveApart hap
    have hmem : (q, u') ∈ l'.live C := hperm.symm.subset (List.mem_cons_self ..)
    refine .inr ⟨hq, live_align hC hw' hmem, u', hu', hperm, fun y hy => ?_⟩
    have hy' : y ∈ l'.live C := hperm.symm.subset (List.mem_cons_of_mem _ hy)
    have hne : y ≠ (q, u') := by
      intro he; subst he
      have := (List.nodup_cons.mp (hperm.nodup_iff.mp hnd)).1
      exact this hy
    exact pairwise_of_mem (fun h => h.symm) hap.1 hy' hmem hne

end Silmaril.Libc.Ptmalloc.Algo
