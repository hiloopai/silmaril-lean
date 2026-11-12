module

public import Silmaril.Proofs.Libc.Ptmalloc.Algo.MallocBody
public import Silmaril.Proofs.Libc.Ptmalloc.Algo.WorldCalls

/-!
# ptmalloc algorithm: arena steps of `_int_malloc` as `MStep`s and `MBody`s

Generic glue for the `_int_malloc` paths: an arena-only change (thread, shared part and kernel
kept) that keeps `LocalWF`, puts every new span inside an old one and keeps the client chunks is
an `MStep` (`MStep.of_arena`) when the lent-out payloads are kept, and an `MBody` lending one
chunk out (`MBody.of_arena`) when they gain exactly that chunk's payload.
-/

@[expose] public section

namespace Silmaril.Libc.Ptmalloc.Algo

variable {C : Config}

theorem pairwise_ne {rs : List (Nat × Nat)}
    (hp : rs.Pairwise (fun r r' => r.1 + r.2 ≤ r'.1 ∨ r'.1 + r'.2 ≤ r.1)) {r s : Nat × Nat}
    (hr : r ∈ rs) (hs : s ∈ rs) (hne : r ≠ s) : r.1 + r.2 ≤ s.1 ∨ s.1 + s.2 ≤ r.1 := by
  induction rs with
  | nil => cases hr
  | cons x xs ih =>
    rw [List.pairwise_cons] at hp
    rcases List.mem_cons.mp hr with rfl | hr' <;> rcases List.mem_cons.mp hs with rfl | hs'
    · exact absurd rfl hne
    · exact hp.1 s hs'
    · exact (hp.1 r hr').symm
    · exact ih hp.2 hr' hs'

/-- Two different ranges of an `Apart` list are apart. -/
theorem Apart.ne_apart {rs : List (Nat × Nat)} (h : Apart rs) {r s : Nat × Nat} (hr : r ∈ rs)
    (hs : s ∈ rs) (hne : r ≠ s) : r.1 + r.2 ≤ s.1 ∨ s.1 + s.2 ≤ r.1 :=
  pairwise_ne h.1 hr hs hne

/-- Each new range lies inside an old one. -/
def SpansIn (rs' rs : List (Nat × Nat)) : Prop :=
  ∀ r ∈ rs', ∃ s ∈ rs, s.1 ≤ r.1 ∧ r.1 + r.2 ≤ s.1 + s.2

theorem SpansIn.away {rs' rs : List (Nat × Nat)} (h : SpansIn rs' rs) {x : Nat × Nat}
    (hx : Away rs x) : Away rs' x := by
  intro r hr
  obtain ⟨s, hs, h1, h2⟩ := h r hr
  rcases hx s hs with h3 | h3 <;> omega

theorem SpansIn.covers {rs' rs : List (Nat × Nat)} (h : SpansIn rs' rs) {k : KernelSt}
    (hk : ∀ s ∈ rs, k.Covers s) : ∀ r ∈ rs', k.Covers r := by
  intro r hr x h1 h2
  obtain ⟨s, hs, h3, h4⟩ := h r hr
  exact hk s hs x (by omega) (by omega)

theorem SpansIn.refl (rs : List (Nat × Nat)) : SpansIn rs rs :=
  fun r hr => ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩

theorem SpansIn.append_right {rs' rs : List (Nat × Nat)} (h : SpansIn rs' rs) (H : List (Nat × Nat)) :
    SpansIn (rs' ++ H) (rs ++ H) := by
  intro r hr
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨s, hs, h1⟩ := h r hr; exact ⟨s, List.mem_append_left _ hs, h1⟩
  · exact ⟨r, List.mem_append_right _ hr, Nat.le_refl _, Nat.le_refl _⟩

theorem spansIn_local {l : Local} {av' : ArenaSt} (h : SpansIn av'.spans l.av.spans) :
    SpansIn ({ l with av := av' } : Local).spans l.spans := by
  intro r hr
  unfold Local.spans at hr ⊢
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨s, hs, h1⟩ := h r hr; exact ⟨s, List.mem_append_left _ hs, h1⟩
  · exact ⟨r, List.mem_append_right _ hr, Nat.le_refl _, Nat.le_refl _⟩

/-- **An arena-only internal step** is an `MStep`. -/
theorem MStep.of_arena {l : Local} {av' : ArenaSt} (hw' : LocalWF C { l with av := av' })
    (hs : LocalSp C l) (hin : SpansIn av'.spans l.av.spans) (hheaps : av'.heaps = l.av.heaps)
    (hout : (av'.out C).Perm (l.av.out C))
    (hcl : ∀ c ∈ l.av.chunks, c.use = .client → c ∈ av'.chunks) :
    MStep C l { l with av := av' } := by
  have hin' := spansIn_local hin
  have hcov := hin'.covers hs.covered
  refine ⟨hw', live_perm_of_out rfl rfl hout, ?_, fun tc i e htc he _ => ⟨tc, htc, he⟩, id⟩
  exact
    { avAddr := rfl, isMain := rfl, spatial := fun _ _ hc ha => ⟨hc, hin'.away ha⟩,
      covered := hcov, brkStart := rfl, nonMain := fun _ => ⟨rfl, rfl⟩, acct := fun _ => Nat.le_refl _, init := rfl,
      arenas := ⟨rfl, rfl, rfl⟩, arena := rfl, heaps := fun h => by simp only; rw [hheaps]; exact h,
      clients := fun c hc hu _ => hcl c hc hu,
      fresh := fun tc' i e htc he => .inl ⟨tc', i, htc, he⟩ }

/-- The payload facts of an arena chunk of a well-formed view. -/
theorem kok_arena {l : Local} (hw : LocalWF C l) {c : Chunk} (hc : c ∈ l.av.chunks) :
    KOk C (c, false) := by
  have ht := hw.arena.tiles
  unfold KOk
  simp only [Bool.false_eq_true, ite_false]
  exact ⟨(ht.sizes c hc).2, ht.aligned c hc, (ht.sizes c hc).1, ht.bound c hc⟩

theorem kok_mm {l : Local} (hw : LocalWF C l) {c : Chunk} (hc : c ∈ l.shared.mm.chunks) :
    KOk C (c, true) := by
  unfold KOk
  simp only [ite_true]
  exact hw.mmSize c hc

/-- **An arena-only step lending one chunk out** is an `MBody`. -/
theorem MBody.of_arena (hC : C.Ok) {n : Nat} {l : Local} {av' : ArenaSt}
    (hw' : LocalWF C { l with av := av' })
    (hs : LocalSp C l) (hin : SpansIn av'.spans l.av.spans) (hheaps : av'.heaps = l.av.heaps)
    (hcl : ∀ c ∈ l.av.chunks, c.use = .client → c ∈ av'.chunks)
    {d : Chunk} (hd : d ∈ av'.chunks)
    (hnot : ∀ c ∈ l.av.chunks, c.addr = d.addr → c.use ≠ .client)
    (hout : (av'.out C).Perm ((d.addr + C.hdr, d.size - C.sizeSz) :: l.av.out C))
    (hn : n + C.sizeSz ≤ d.size) :
    MBody C n l (d.addr + C.hdr) { l with av := av' } := by
  have hin' := spansIn_local hin
  have hcov := hin'.covers hs.covered
  have h8 := hC.sizeSz; have h16 := hC.align
  have hkd := kok_arena hw' hd
  have hdal : d.addr % C.align = 0 := hw'.arena.tiles.aligned d hd
  -- the new payload is not parked
  have hnp : (d.addr + C.hdr, d.size - C.sizeSz) ∉ l.thread.parked C := by
    intro hp
    obtain ⟨tc, htc, i, -, e, he, hpe⟩ := mem_parked.mp hp
    simp only [epay, Prod.mk.injEq] at hpe
    have hea : e.1 = d.addr := by omega
    rcases hs.entries tc htc i e he with ⟨c, hc, h1, -, h3⟩ | ⟨ha, -⟩
    · exact hnot c hc (h1.trans hea) h3
    · obtain ⟨s, hs', h1, h2⟩ := hin _ (span_mem_spans hd)
      have hdpos : 0 < d.size := by have := (hw'.arena.tiles.sizes d hd).2; have := hC.minSize; omega
      have hepos : 0 < e.2 := by
        have := ((hw'.tcache tc htc).size i e he).2.2; have := hC.minSize; omega
      rcases ha s (List.mem_append_left _ hs') with h3 | h3 <;> simp only at h1 h2 <;> omega
  refine ⟨⟨hw', within_empty rfl rfl, .inr ⟨by unfold Config.hdr; omega,
    by unfold Config.hdr; rw [h8, h16] at *; omega, d.size - C.sizeSz, by omega, ?_, ?_⟩⟩, ?_, ?_, id⟩
  · -- the live set
    unfold Local.live
    simp only
    rw [← List.cons_append]
    refine List.Perm.append_right _ ?_
    refine ((hout.filter _).trans ?_)
    rw [List.filter_cons_of_pos (by simpa [contains_false] using hnp)]
  · -- apart from every live payload
    intro q hq
    rcases mem_llive.mp hq with ⟨hqo, -⟩ | hqm
    · obtain ⟨c, hc, hcu, rfl⟩ := mem_out.mp hqo
      have hc' := hcl c hc hcu
      have hne : c.addr ≠ d.addr := fun h => hnot c hc h hcu
      have hap := Apart.ne_apart hw'.apart
        (List.mem_append_left _ (span_mem_spans hc')) (List.mem_append_left _ (span_mem_spans hd))
        (fun h => hne (congrArg Prod.fst h))
      have := pay_apart hC (kok_arena hw' hc') hkd hap
      simpa [kpay, usable] using this
    · obtain ⟨m, hm, -, rfl⟩ := mem_shlive.mp hqm
      have hm' : (m.addr, m.size) ∈ ({ l with av := av' } : Local).shared.mm.chunks.map
          (fun c => (c.addr, c.size)) := List.mem_map.mpr ⟨m, hm, rfl⟩
      have hap := Apart.cross hw'.apart (span_mem_spans hd) hm'
      have := pay_apart hC hkd (kok_mm hw' hm) hap
      simp only [kpay, usable, ite_true, Bool.false_eq_true, ite_false] at this
      omega
  · exact
    { avAddr := rfl, isMain := rfl, spatial := fun _ _ hc ha => ⟨hc, hin'.away ha⟩,
      covered := hcov, brkStart := rfl, nonMain := fun _ => ⟨rfl, rfl⟩, acct := fun _ => Nat.le_refl _, init := rfl,
      arenas := ⟨rfl, rfl, rfl⟩, arena := rfl, heaps := fun h => by simp only; rw [hheaps]; exact h,
      clients := fun c hc hu _ => hcl c hc hu,
      fresh := fun tc' i e htc he => .inl ⟨tc', i, htc, he⟩ }
  · exact fun tc i e htc he _ => ⟨tc, htc, he⟩

end Silmaril.Libc.Ptmalloc.Algo
