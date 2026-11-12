module

public import Silmaril.Libc.Ptmalloc.Algo.MallocBody.Defs
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.Malloc

/-!
# ptmalloc algorithm: `_int_malloc`'s body obligations from its paths

The `Frame` algebra (`Frame.trans`, `LocalSp.of_frame`, `KeptAway.trans`), `MStep` and `MBody`
composition, and the combination of `intMalloc`'s path obligations
(`Silmaril.Libc.Ptmalloc.Algo.MallocBody.Defs`) into `Task.algo.bodyMalloc` and
`Task.algo.totalMalloc`.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

variable {C : Config}

/-! ## The frame algebra -/

theorem Frame.trans {l l₁ l₂ : Local} (h₁ : Frame C l l₁ []) (h₂ : Frame C l₁ l₂ []) :
    Frame C l l₂ [] where
  avAddr := h₂.avAddr.trans h₁.avAddr
  isMain := h₂.isMain.trans h₁.isMain
  spatial r h0 hc ha :=
    let h := h₁.spatial r h0 hc ha
    h₂.spatial r h0 h.1 h.2
  covered := h₂.covered
  brkStart := h₂.brkStart.trans h₁.brkStart
  nonMain hm := by
    have a := h₁.nonMain hm
    have b := h₂.nonMain (by rw [h₁.isMain]; exact hm)
    exact ⟨b.1.trans a.1, b.2.trans a.2⟩
  acct hm := by
    have a := h₁.acct hm
    have b := h₂.acct (by rw [h₁.isMain]; exact hm)
    omega
  init := h₂.init.trans h₁.init
  arenas := ⟨h₂.arenas.1.trans h₁.arenas.1, h₂.arenas.2.1.trans h₁.arenas.2.1,
    h₂.arenas.2.2.trans h₁.arenas.2.2⟩
  arena := h₂.arena.trans h₁.arena
  heaps h := h₂.heaps (h₁.heaps h)
  clients c hc hu _ := h₂.clients c (h₁.clients c hc hu (by simp)) hu (by simp)
  fresh tc'' i e ht he := by
    rcases h₂.fresh tc'' i e ht he with ⟨tc', j, ht', he'⟩ | ⟨hc, hfr⟩
    · rcases h₁.fresh tc' j e ht' he' with h | ⟨⟨c, hc, h1, h2, h3⟩, hfr'⟩
      · exact .inl h
      · exact .inr ⟨⟨c, h₂.clients c hc h3 (by simp), h1, h2, h3⟩, hfr'⟩
    · rcases hfr with hfr | hfr
      · simp at hfr
      · exact .inr ⟨hc, .inr fun c hc' hca hcu => hfr c (h₁.clients c hc' hcu (by simp)) hca hcu⟩

/-- A frame for a body that changes nothing the frame speaks of. -/
theorem Frame.of_eq {l l' : Local} {freed : List (Nat × Nat)} (ha : l'.avAddr = l.avAddr)
    (hm : l'.isMain = l.isMain) (hav : l'.av = l.av) (hk : l'.kernel = l.kernel)
    (hs : l'.shared = l.shared) (ht : l'.thread.tcache = l.thread.tcache)
    (har : l'.thread.arena = l.thread.arena) (hcov : ∀ r ∈ l.spans, l.kernel.Covers r) :
    Frame C l l' freed where
  avAddr := ha
  isMain := hm
  spatial r _ hc hap := by
    unfold Local.spans; rw [hk, hav, hs]; exact ⟨hc, hap⟩
  covered r hr := by
    unfold Local.spans at hr; rw [hav, hs] at hr; rw [hk]; exact hcov r hr
  brkStart := by rw [hk]
  nonMain _ := by rw [hk, hs]; exact ⟨rfl, rfl⟩
  acct _ := by rw [hk, hs]; exact Nat.le_refl _
  init := by rw [hs]
  arenas := by rw [hs]; exact ⟨rfl, rfl, rfl⟩
  arena := har
  heaps h := by rw [hav]; exact h
  clients c hc _ _ := by rw [hav]; exact hc
  fresh tc' i e ht' he := by
    rw [ht] at ht'
    exact .inl ⟨tc', i, ht', he⟩

theorem mem_spans_of_chunk {l : Local} {c : Chunk} (hc : c ∈ l.av.chunks) :
    (c.addr, c.size) ∈ l.spans := by
  unfold Local.spans ArenaSt.spans TopSt.spans
  exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem hc)))

theorem not_away_self {rs : List (Nat × Nat)} {r : Nat × Nat} (hr : r ∈ rs) (h0 : 0 < r.2) :
    ¬ Away rs r := by
  intro h; have := h r hr; omega

theorem entry_pos (hC : C.Ok) {l : Local} (hw : LocalWF C l) {tc : TcacheSt}
    (ht : l.thread.tcache = some tc) {i : Nat} {e : Nat × Nat} (he : e ∈ tc.bins i) : 0 < e.2 := by
  have := ((hw.tcache tc ht).size i e he).2.2
  have := hC.minSize
  omega

/-- **`LocalSp` is carried by a frame.** -/
theorem LocalSp.of_frame (hC : C.Ok) {l l' : Local} (hw : LocalWF C l) (hsp : LocalSp C l)
    (hF : Frame C l l' []) : LocalSp C l' where
  covered := hF.covered
  entries tc' ht' i e he := by
    rcases hF.fresh tc' i e ht' he with ⟨tc, j, ht, he0⟩ | ⟨hc, -⟩
    · rcases hsp.entries tc ht j e he0 with ⟨c, hc, h1, h2, h3⟩ | ⟨ha, hcv⟩
      · exact .inl ⟨c, hF.clients c hc h3 (by simp), h1, h2, h3⟩
      · have h := hF.spatial e (entry_pos hC hw ht he0) hcv ha
        exact .inr ⟨h.2, h.1⟩
    · exact .inl hc
  heaps hm := hF.heaps (hsp.heaps (by rw [← hF.isMain]; exact hm))

/-- **`KeptAway` composes** over a frame. -/
theorem KeptAway.trans (hC : C.Ok) {l l₁ l₂ : Local} (hw : LocalWF C l) (hsp : LocalSp C l)
    (hF : Frame C l l₁ []) (k₁ : KeptAway l l₁) (k₂ : KeptAway l₁ l₂) : KeptAway l l₂ := by
  intro tc i e ht he ha
  obtain ⟨tc₁, ht₁, he₁⟩ := k₁ tc i e ht he ha
  apply k₂ tc₁ i e ht₁ he₁
  have h0 := entry_pos hC hw ht he
  rcases hsp.entries tc ht i e he with ⟨c, hc, h1, h2, -⟩ | ⟨-, hcv⟩
  · exfalso
    have hm := mem_spans_of_chunk hc
    rw [h1, h2] at hm
    exact not_away_self hm h0 ha
  · exact (hF.spatial e h0 hcv ha).2

/-! ## Steps and bodies -/

theorem within_trans {l l₁ l₂ : Local} (h₁ : Footprint.Within {} l l₁) (h₂ : Footprint.Within {} l₁ l₂) :
    Footprint.Within {} l l₂ :=
  ⟨h₂.1.trans h₁.1, h₂.2.1.trans h₁.2.1, fun h => absurd h (by decide),
    fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide)⟩

theorem within_of_frame {l l' : Local} {freed : List (Nat × Nat)} (h : Frame C l l' freed) :
    Footprint.Within {} l l' :=
  ⟨h.avAddr, h.isMain, fun h => absurd h (by decide),
    fun h => absurd h (by decide), fun h => absurd h (by decide), fun h => absurd h (by decide)⟩

theorem MStep.sp (hC : C.Ok) {l l' : Local} (hw : LocalWF C l) (hsp : LocalSp C l)
    (h : MStep C l l') : LocalSp C l' :=
  LocalSp.of_frame hC hw hsp h.2.2.1

theorem MStep.trans (hC : C.Ok) {l l₁ l₂ : Local} (hw : LocalWF C l) (hsp : LocalSp C l)
    (h₁ : MStep C l l₁) (h₂ : MStep C l₁ l₂) : MStep C l l₂ :=
  ⟨h₂.1, h₂.2.1.trans h₁.2.1, h₁.2.2.1.trans h₂.2.2.1,
    KeptAway.trans hC hw hsp h₁.2.2.1 h₁.2.2.2.1 h₂.2.2.2.1,
    fun h => h₂.2.2.2.2 (h₁.2.2.2.2 h)⟩

/-- **A step, then a body, is a body.** -/
theorem MBody.of_step (hC : C.Ok) {n p : Nat} {l l₁ l₂ : Local} (hw : LocalWF C l)
    (hsp : LocalSp C l) (h₁ : MStep C l l₁) (h₂ : MBody C n l₁ p l₂) : MBody C n l p l₂ :=
  ⟨⟨h₂.1.1, within_trans (within_of_frame h₁.2.2.1) h₂.1.2.1, MallocLive.perm_left h₁.2.1 h₂.1.2.2⟩,
    h₁.2.2.1.trans h₂.2.1, KeptAway.trans hC hw hsp h₁.2.2.1 h₁.2.2.2.1 h₂.2.2.1,
    fun h => h₂.2.2.2 (h₁.2.2.2.2 h)⟩

theorem mstep_refl {l : Local} (hw : LocalWF C l) (hsp : LocalSp C l) : MStep C l l :=
  ⟨hw, List.Perm.refl _, Frame.of_eq rfl rfl rfl rfl rfl rfl rfl hsp.covered,
    fun tc _ _ ht he _ => ⟨tc, ht, he⟩, id⟩

/-- **The request check**: `ENOMEM` sets `errno` only. -/
theorem setErrno_body {l : Local} (hw : LocalWF C l) (hsp : LocalSp C l) (n : Nat) :
    MBody C n l 0 (setErrno l 12) :=
  ⟨setErrno_ok hw n, Frame.of_eq rfl rfl rfl rfl rfl rfl rfl hsp.covered,
    fun tc _ _ ht he _ => ⟨tc, ht, he⟩, id⟩

end Silmaril.Libc.Ptmalloc.Algo
