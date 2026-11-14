module

public import Silmaril.X86.MemoryModel.OpAx.Defs
public import Silmaril.X86.MemoryModel.Axiomatic.Thms

/-!
# Timed candidates are x86-TSO-consistent: proofs

`tso_of_timedOk`: a candidate with a `TimedOk` timing satisfies `Exec.Tso`. `ghb` is ranked by
`rankG` (twice the execution time for reads and fences, twice the memory time plus one for
writes); `uniproc` by the lexicographic `rankU`, in which a read that forwards from its
thread's buffer sits just after the memory time of its source; atomicity because a write that a locked read's `fr` reaches enters memory after the read, hence
not before the locked write, which enters memory one tick after the read.
-/

@[expose] public section

namespace Silmaril.X86.MemoryModel.OpAx.Proofs

open Silmaril.X86.MemoryModel.Axiomatic
open Silmaril.X86.MemoryModel.OpAx
open Relation

/-! ## Generic facts -/

theorem acyclic_of_rank {n : Nat} {β : Type} (lt : β → β → Prop)
    (trans : ∀ a b c, lt a b → lt b c → lt a c) (irr : ∀ a, ¬ lt a a)
    {r : BRel n} (t : Fin n → β) (h : ∀ a b, r a b = true → lt (t a) (t b)) : r.Acyclic := by
  intro a hc
  have : ∀ a b, TransGen r.Holds a b → lt (t a) (t b) := by
    intro a b hab
    induction hab with
    | single h1 => exact h _ _ h1
    | tail _ h2 ih => exact trans _ _ _ ih (h _ _ h2)
  exact irr _ (this a a hc)

/-- Lexicographic order on triples. -/
def lt3 (a b : Nat × Nat × Nat) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ (a.2.1 < b.2.1 ∨ (a.2.1 = b.2.1 ∧ a.2.2 < b.2.2)))

theorem lt3_trans (a b c : Nat × Nat × Nat) (h1 : lt3 a b) (h2 : lt3 b c) : lt3 a c := by
  obtain ⟨a1, a2, a3⟩ := a; obtain ⟨b1, b2, b3⟩ := b; obtain ⟨c1, c2, c3⟩ := c
  simp only [lt3] at *
  omega

theorem lt3_irrefl (a : Nat × Nat × Nat) : ¬ lt3 a a := by
  obtain ⟨a1, a2, a3⟩ := a
  simp only [lt3, true_and]
  omega

theorem before_mem : ∀ {l : List Nat} {a b : Nat}, before l a b = true → a ∈ l ∧ b ∈ l
  | [], _, _, h => by simp [before] at h
  | c :: l, a, b, h => by
    simp only [before] at h
    split at h
    · rename_i hc
      simp only [beq_iff_eq] at hc
      subst hc
      exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ (List.contains_iff_mem.mp h)⟩
    · have := before_mem h
      exact ⟨List.mem_cons_of_mem _ this.1, List.mem_cons_of_mem _ this.2⟩

theorem before_pairwise {R : Nat → Nat → Prop} :
    ∀ {l : List Nat}, l.Pairwise R → ∀ {a b : Nat}, before l a b = true → R a b
  | [], _, _, _, h => by simp [before] at h
  | c :: l, hp, a, b, h => by
    simp only [before] at h
    rw [List.pairwise_cons] at hp
    split at h
    · rename_i hc
      simp only [beq_iff_eq] at hc
      subst hc
      exact hp.1 b (List.contains_iff_mem.mp h)
    · exact before_pairwise hp.2 h

theorem isR_not_isW {e : Ev} (hr : e.isR = true) : e.isW = false := by
  simp only [Ev.isR, Ev.isW, beq_iff_eq] at hr ⊢
  simp [hr]

theorem isW_not_isR {e : Ev} (hw : e.isW = true) : e.isR = false := by
  simp only [Ev.isR, Ev.isW, beq_iff_eq] at hw ⊢
  simp [hw]

theorem isFence_not_isW {e : Ev} {k} (h : e.isFence k = true) : e.isW = false := by
  simp only [Ev.isFence, Ev.isW, beq_iff_eq] at h ⊢
  simp [h]

theorem isM_cases {e : Ev} (h : e.isM = true) : e.isR = true ∨ e.isW = true := by
  simpa [Ev.isM] using h

theorem isA_locked {e : Ev} (h : e.isA = true) : e.locked = true := by
  simp only [Ev.isA, Bool.and_eq_true] at h
  exact h.1

theorem mem_bytes {e : Ev} {y : Nat} : y ∈ e.bytes ↔ e.covers y = true := by
  simp only [Ev.bytes, List.mem_range'_1, Ev.covers, Bool.and_eq_true, decide_eq_true_eq]

theorem overlap_iff {a b : Ev} : Ev.overlap a b = true ↔ ∃ y, a.covers y = true ∧ b.covers y = true := by
  simp only [Ev.overlap, List.any_eq_true, mem_bytes]

theorem covers_of_same {a b : Ev} (h1 : a.addr = b.addr) (h2 : a.size = b.size) (y : Nat) :
    a.covers y = b.covers y := by
  simp [Ev.covers, h1, h2]

/-! ## The candidate -/

section
variable {x : Exec} {T : Timing}

theorem ev_eq (a : Fin x.n) : x.ev a = x.evN a.val := by
  simp [Exec.ev, Exec.evN]

theorem sm_eq (H : TimedOk x T) {a b : Fin x.n} (h : x.sm a b = true) : a = b := by
  simp only [Exec.sm, Bool.and_eq_true, beq_iff_eq, ev_eq] at h
  exact Fin.ext (H.uniq _ a.2 _ b.2 h.1 h.2)

theorem co_before (H : TimedOk x T) {y a b : Nat} (h : before (x.co y) a b = true) : T.f a < T.f b := by
  rw [H.coDef] at h
  exact before_pairwise (H.woSorted.filter _) h

theorem co_isW (H : TimedOk x T) {y a b : Nat} (h : before (x.co y) a b = true) :
    a < x.n ∧ (x.evN a).isW = true := by
  rw [H.coDef] at h
  exact H.woW a (List.mem_filter.mp (before_mem h).1).1

/-- Same-thread memory units that share a byte cover the same bytes. -/
theorem cells_cov (H : TimedOk x T) {a b : Nat} (ha : a < x.n) (hb : b < x.n) (ht : (x.evN a).tid = (x.evN b).tid)
    (hma : (x.evN a).isM = true) (hmb : (x.evN b).isM = true) {y : Nat}
    (hya : (x.evN a).covers y = true) (hyb : (x.evN b).covers y = true) (z : Nat) :
    (x.evN a).covers z = (x.evN b).covers z := by
  obtain ⟨h1, h2⟩ := H.cells a ha b hb ht hma hmb (overlap_iff.mpr ⟨y, hya, hyb⟩)
  exact covers_of_same h1 h2 z

/-- A read reaches memory no later than a write that `fr` reaches. -/
theorem fr_le (H : TimedOk x T) {r w y : Nat} (hr : r < x.n) (hR : (x.evN r).isR = true) (hy : y ∈ (x.evN r).bytes)
    (hw : w < x.n) (hW : (x.evN w).isW = true) (hc : (x.evN w).covers y = true)
    (hfr : match x.rf r y with
      | none => true
      | some v => before (x.co y) v w) : T.e r ≤ T.f w := by
  have hs := H.rfOk r hr hR y hy
  unfold RfSpec at hs
  revert hfr hs
  cases x.rf r y with
  | none =>
    intro _ hs
    have := (hs w hw hW hc).1
    omega
  | some v =>
    intro hfr hs
    have hvw := co_before H hfr
    rcases hs with ⟨-, -, -, ⟨⟨-, -, h⟩, -⟩ | ⟨h, hmax, -⟩⟩
    · omega
    · by_contra hlt
      have := hmax w hw hW hc (by omega)
      omega

/-! ## `ghb` -/

/-- The `ghb` rank. -/
noncomputable def rankG (x : Exec) (T : Timing) (a : Fin x.n) : Nat :=
  if (x.evN a.val).isW then 2 * T.f a.val + 1 else 2 * T.e a.val

theorem rankG_W {a : Fin x.n} (h : (x.evN a.val).isW = true) : rankG x T a = 2 * T.f a.val + 1 := by
  simp [rankG, h]

theorem rankG_nW {a : Fin x.n} (h : (x.evN a.val).isW = false) : rankG x T a = 2 * T.e a.val := by
  simp [rankG, h]

/-- An edge from `a` to `b` in `po` increases the rank when `a` is not a write. -/
theorem rankG_po_from_nW (H : TimedOk x T) {a b : Fin x.n} (hpo : x.po a b = true) (ha : (x.evN a.val).isW = false) :
    rankG x T a < rankG x T b := by
  simp only [Exec.po, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, ev_eq] at hpo
  have he := H.poE _ a.2 _ b.2 hpo.1 hpo.2
  rw [rankG_nW ha]
  cases hb : (x.evN b.val).isW
  · rw [rankG_nW hb]; omega
  · rw [rankG_W hb]; have := H.eLeF _ b.2 hb; omega

theorem ghb_rank (H : TimedOk x T) {a b : Fin x.n} (h : x.ghb a b = true) : rankG x T a < rankG x T b := by
  simp only [Exec.ghb, BRel.union_iff] at h
  rcases h with h | h | h | h
  · -- mfence
    simp only [Exec.mfence, Exec.fencerel, List.any_eq_true, Bool.and_eq_true] at h
    obtain ⟨g, -, ⟨hg, h1⟩, h2⟩ := h
    rw [ev_eq] at hg
    have hgW := isFence_not_isW hg
    have hb := rankG_po_from_nW H h2 hgW
    suffices rankG x T a < rankG x T g by omega
    cases ha : (x.evN a.val).isW
    · exact rankG_po_from_nW H h1 ha
    · simp only [Exec.po, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, ev_eq] at h1
      have := H.drain _ g.2 _ a.2 ha h1.1 h1.2 (.inl hg)
      rw [rankG_W ha, rankG_nW hgW]; omega
  · -- implied
    simp only [Exec.implied, Bool.and_eq_true, Bool.or_eq_true, ev_eq] at h
    obtain ⟨⟨⟨hpo, hW⟩, hR⟩, hA⟩ := h
    have hpo' := hpo
    simp only [Exec.po, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, ev_eq] at hpo'
    rw [rankG_W hW, rankG_nW (isR_not_isW hR)]
    rcases hA with hA | hA
    · have := H.lockedW _ a.2 hW (isA_locked hA)
      have := H.poE _ a.2 _ b.2 hpo'.1 hpo'.2
      omega
    · have := H.drain _ b.2 _ a.2 hW hpo'.1 hpo'.2 (.inr hA)
      omega
  · -- ppo
    simp only [Exec.ppo, Bool.and_eq_true, Bool.or_eq_true, ev_eq] at h
    obtain ⟨hpo, hk⟩ := h
    rcases hk with ⟨hWa, hWb⟩ | ⟨hRa, -⟩
    · simp only [Exec.po, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, ev_eq] at hpo
      have := H.fifo _ a.2 _ b.2 hWa hWb hpo.1 hpo.2
      rw [rankG_W hWa, rankG_W hWb]; omega
    · exact rankG_po_from_nW H hpo (isR_not_isW hRa)
  · -- (rfe | fr | co); sm
    obtain ⟨c, hc, hs⟩ := BRel.seq_elim h
    rw [sm_eq H hs] at hc
    simp only [BRel.union_iff] at hc
    rcases hc with hc | hc | hc
    · -- rfe
      simp only [Exec.rfe, BRel.inter_iff, Exec.rfR, Exec.ext, Bool.and_eq_true,
        List.any_eq_true, bne_iff_ne, ne_eq, ev_eq] at hc
      obtain ⟨⟨⟨hW, hR⟩, y, hy, hrf, -⟩, hext⟩ := hc
      have hs := H.rfOk _ b.2 hR y hy
      unfold RfSpec at hs
      simp only [beq_iff_eq] at hrf
      rw [hrf] at hs
      rcases hs with ⟨-, -, -, ⟨⟨htid, -⟩, -⟩ | ⟨hlt, -⟩⟩
      · exact absurd htid hext
      · rw [rankG_W hW, rankG_nW (isR_not_isW hR)]; omega
    · -- fr
      simp only [Exec.frR, Bool.and_eq_true, List.any_eq_true, ev_eq] at hc
      obtain ⟨⟨hR, hW⟩, y, hy, hcov, hfr⟩ := hc
      have := fr_le H a.2 hR hy b.2 hW hcov (by revert hfr; cases x.rf a y <;> simp)
      rw [rankG_W hW, rankG_nW (isR_not_isW hR)]; omega
    · -- co
      simp only [Exec.coR, Bool.and_eq_true, List.any_eq_true, ev_eq] at hc
      obtain ⟨⟨hWa, hWc⟩, y, -, -, hb⟩ := hc
      have := co_before H hb
      rw [rankG_W hWa, rankG_W hWc]; omega

theorem ghb_acyclic (H : TimedOk x T) : x.ghb.Acyclic :=
  acyclic_of_rank (· < ·) (fun _ _ _ => Nat.lt_trans) (fun a => Nat.lt_irrefl a) (rankG x T)
    (fun _ _ h => ghb_rank H h)

/-! ## Forwarding -/

/-- Read `r` forwards from its thread's buffered write `s`. -/
def Fw (x : Exec) (T : Timing) (r s : Nat) : Prop :=
  s < x.n ∧ (x.evN s).isW = true ∧ (x.evN s).tid = (x.evN r).tid ∧ (x.evN s).pos < (x.evN r).pos ∧
    Ev.overlap (x.evN r) (x.evN s) = true ∧ T.e r < T.f s ∧
    ∀ w < x.n, (x.evN w).isW = true → (x.evN w).tid = (x.evN r).tid →
      (x.evN w).pos < (x.evN r).pos → Ev.overlap (x.evN r) (x.evN w) = true → T.e r < T.f w →
        (x.evN w).pos ≤ (x.evN s).pos

/-- Own write `w` of read `r` covering byte `y` of `r` overlaps `r` and covers all its bytes. -/
theorem own_cov (H : TimedOk x T) {r w y : Nat} (hr : r < x.n) (hR : (x.evN r).isR = true) (hy : y ∈ (x.evN r).bytes)
    (hw : w < x.n) (hW : (x.evN w).isW = true) (ht : (x.evN w).tid = (x.evN r).tid)
    (hc : (x.evN w).covers y = true) :
    Ev.overlap (x.evN r) (x.evN w) = true ∧ ∀ z, (x.evN w).covers z = (x.evN r).covers z := by
  have hmr : (x.evN r).isM = true := by simp [Ev.isM, hR]
  have hmw : (x.evN w).isM = true := by simp [Ev.isM, hW]
  exact ⟨overlap_iff.mpr ⟨y, mem_bytes.mp hy, hc⟩,
    cells_cov H hw hr ht hmw hmr hc (mem_bytes.mp hy)⟩

theorem fw_rf (H : TimedOk x T) {r s y : Nat} (hr : r < x.n) (hR : (x.evN r).isR = true) (hy : y ∈ (x.evN r).bytes)
    (hfw : Fw x T r s) : x.rf r y = some s := by
  obtain ⟨hs, hW, ht, hpos, hov, hlt, hmax⟩ := hfw
  have hsy : (x.evN s).covers y = true := by
    obtain ⟨z, hz1, hz2⟩ := overlap_iff.mp hov
    have hmr : (x.evN r).isM = true := by simp [Ev.isM, hR]
    have hms : (x.evN s).isM = true := by simp [Ev.isM, hW]
    rw [cells_cov H hs hr ht hms hmr hz2 hz1 y]; exact mem_bytes.mp hy
  have hspec := H.rfOk r hr hR y hy
  unfold RfSpec at hspec
  revert hspec
  cases hrf : x.rf r y with
  | none =>
    intro hspec
    exact absurd ⟨ht, hpos⟩ (hspec s hs hW hsy).2
  | some s' =>
    intro hspec
    obtain ⟨hs', hW', hc', hcase⟩ := hspec
    rcases hcase with ⟨⟨ht', hpos', hlt'⟩, hmax'⟩ | ⟨-, -, hall⟩
    · have h1 := hmax' s hs hW hsy ht hpos hlt
      have h2 := hmax s' hs' hW' ht' hpos' (own_cov H hr hR hy hs' hW' ht' hc').1 hlt'
      have := H.uniq _ hs _ hs' (ht.trans ht'.symm) (by omega)
      rw [this]
    · have := hall s hs hW hsy ht hpos
      omega

/-- Without forwarding, every earlier own write that overlaps the read reached memory before it,
and each read byte comes from memory. -/
theorem nofw_rf (H : TimedOk x T) {r y : Nat} (hr : r < x.n) (hR : (x.evN r).isR = true) (hy : y ∈ (x.evN r).bytes)
    (hnf : ¬ ∃ s, Fw x T r s) :
    (∀ w < x.n, (x.evN w).isW = true → (x.evN w).tid = (x.evN r).tid →
      (x.evN w).pos < (x.evN r).pos → Ev.overlap (x.evN r) (x.evN w) = true → T.f w < T.e r) ∧
    ∀ v, x.rf r y = some v → T.f v < T.e r ∧
      ∀ w < x.n, (x.evN w).isW = true → (x.evN w).covers y = true → T.f w < T.e r →
        T.f w ≤ T.f v := by
  have hspec := H.rfOk r hr hR y hy
  unfold RfSpec at hspec
  revert hspec
  cases hrf : x.rf r y with
  | none =>
    intro hspec
    refine ⟨fun w hw hW ht hpos hov => ?_, fun v hv => by cases hv⟩
    obtain ⟨z, hz1, hz2⟩ := overlap_iff.mp hov
    have hmr : (x.evN r).isM = true := by simp [Ev.isM, hR]
    have hmw : (x.evN w).isM = true := by simp [Ev.isM, hW]
    have hwy : (x.evN w).covers y = true := by
      rw [cells_cov H hw hr ht hmw hmr hz2 hz1 y]; exact mem_bytes.mp hy
    exact absurd ⟨ht, hpos⟩ (hspec w hw hW hwy).2
  | some s =>
    intro hspec
    obtain ⟨hs, hW, hc, hcase⟩ := hspec
    rcases hcase with ⟨⟨ht, hpos, hlt⟩, hmax⟩ | ⟨hlt, hmax, hall⟩
    · exfalso
      apply hnf
      refine ⟨s, hs, hW, ht, hpos, (own_cov H hr hR hy hs hW ht hc).1, hlt, ?_⟩
      intro w hw hW' ht' hpos' hov' hlt'
      have hwy : (x.evN w).covers y = true := by
        rw [(own_cov H hr hR hy hw hW' ht' (by
          obtain ⟨z, hz1, hz2⟩ := overlap_iff.mp hov'
          have hmr : (x.evN r).isM = true := by simp [Ev.isM, hR]
          have hmw : (x.evN w).isM = true := by simp [Ev.isM, hW']
          rw [cells_cov H hw hr ht' hmw hmr hz2 hz1 y]; exact mem_bytes.mp hy)).2 y]
        exact mem_bytes.mp hy
      exact hmax w hw hW' hwy ht' hpos' hlt'
    · refine ⟨fun w hw hW' ht' hpos' hov' => ?_, fun v hv => ?_⟩
      · obtain ⟨z, hz1, hz2⟩ := overlap_iff.mp hov'
        have hmr : (x.evN r).isM = true := by simp [Ev.isM, hR]
        have hmw : (x.evN w).isM = true := by simp [Ev.isM, hW']
        have hwy : (x.evN w).covers y = true := by
          rw [cells_cov H hw hr ht' hmw hmr hz2 hz1 y]; exact mem_bytes.mp hy
        exact hall w hw hW' hwy ht' hpos'
      · cases hv
        exact ⟨hlt, hmax⟩

/-! ## `uniproc` -/

open Classical in
/-- The `uniproc` rank: memory time for writes; for a read that forwards from `s`, just after
`s`'s memory time; otherwise execution time. -/
noncomputable def rankU (x : Exec) (T : Timing) (a : Fin x.n) : Nat × Nat × Nat :=
  if (x.evN a.val).isW then (T.f a.val, 1, 0)
  else if h : ∃ s, Fw x T a.val s then (T.f (Classical.choose h), 2, T.e a.val)
  else (T.e a.val, 0, 0)

theorem rankU_W {a : Fin x.n} (h : (x.evN a.val).isW = true) : rankU x T a = (T.f a.val, 1, 0) := by
  simp [rankU, h]

theorem rankU_fw (H : TimedOk x T) {a : Fin x.n} (h : (x.evN a.val).isR = true) {s : Nat} (hs : Fw x T a.val s) :
    rankU x T a = (T.f s, 2, T.e a.val) := by
  have hne : ∃ s, Fw x T a.val s := ⟨s, hs⟩
  have hch := Classical.choose_spec hne
  simp only [rankU, isR_not_isW h, Bool.false_eq_true, ↓reduceIte, hne, ↓reduceDIte]
  -- the forwarding source is unique
  obtain ⟨hs1, hW1, ht1, hp1, -, hl1, hm1⟩ := hch
  obtain ⟨hs2, hW2, ht2, hp2, ho2, hl2, hm2⟩ := hs
  have := hm1 s hs2 hW2 ht2 hp2 ho2 hl2
  have := hm2 _ hs1 hW1 ht1 hp1 (by
    obtain ⟨-, -, -, -, ho, -⟩ := Classical.choose_spec hne; exact ho) hl1
  have heq := H.uniq _ hs1 _ hs2 (ht1.trans ht2.symm) (by omega)
  rw [heq]

theorem rankU_nofw {a : Fin x.n} (h : (x.evN a.val).isW = false) (hn : ¬ ∃ s, Fw x T a.val s) :
    rankU x T a = (T.e a.val, 0, 0) := by
  simp [rankU, h, hn]

theorem fw_lt {r s : Nat} (h : Fw x T r s) : T.e r < T.f s := h.2.2.2.2.2.1

/-- Facts about two same-thread memory units, `a` before `b`, that share a byte. -/
theorem poLoc_facts {a b : Fin x.n} (h : x.poLoc a b = true) :
    (x.evN a.val).tid = (x.evN b.val).tid ∧ (x.evN a.val).pos < (x.evN b.val).pos ∧
      (x.evN a.val).isM = true ∧ (x.evN b.val).isM = true ∧
      Ev.overlap (x.evN a.val) (x.evN b.val) = true := by
  simp only [Exec.poLoc, BRel.inter_iff, Exec.po, Exec.loc, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq, ev_eq] at h
  exact ⟨h.1.1, h.1.2, h.2.1.1, h.2.1.2, h.2.2⟩

theorem overlap_symm {a b : Ev} (h : Ev.overlap a b = true) : Ev.overlap b a = true := by
  obtain ⟨y, h1, h2⟩ := overlap_iff.mp h
  exact overlap_iff.mpr ⟨y, h2, h1⟩

/-- Overlap transfers along same-footprint units. -/
theorem overlap_trans_cells (H : TimedOk x T) {a b c : Nat} (ha : a < x.n) (hb : b < x.n)
    (htab : (x.evN a).tid = (x.evN b).tid) (hma : (x.evN a).isM = true)
    (hmb : (x.evN b).isM = true) (hab : Ev.overlap (x.evN a) (x.evN b) = true)
    (hbc : Ev.overlap (x.evN b) (x.evN c) = true) : Ev.overlap (x.evN a) (x.evN c) = true := by
  obtain ⟨y, h1, h2⟩ := overlap_iff.mp hab
  obtain ⟨z, h3, h4⟩ := overlap_iff.mp hbc
  refine overlap_iff.mpr ⟨z, ?_, h4⟩
  rw [cells_cov H ha hb htab hma hmb h1 h2 z]; exact h3

theorem uniproc_rank (H : TimedOk x T) {a b : Fin x.n} (h : x.uniproc a b = true) :
    lt3 (rankU x T a) (rankU x T b) := by
  simp only [Exec.uniproc, BRel.union_iff] at h
  rcases h with h | h
  · obtain ⟨ht, hpos, hma, hmb, hov⟩ := poLoc_facts h
    have he := H.poE _ a.2 _ b.2 ht hpos
    rcases isM_cases hma with hRa | hWa <;> rcases isM_cases hmb with hRb | hWb
    · -- R → R
      by_cases hfa : ∃ s, Fw x T a.val s
      · obtain ⟨s, hs⟩ := hfa
        rw [rankU_fw H hRa hs]
        obtain ⟨hs1, hW1, ht1, hp1, ho1, hl1, -⟩ := hs
        have hsb : Ev.overlap (x.evN b.val) (x.evN s) = true :=
          overlap_trans_cells H b.2 a.2 ht.symm hmb hma (overlap_symm hov) ho1
        by_cases hfb : ∃ s, Fw x T b.val s
        · obtain ⟨s', hs'⟩ := hfb
          rw [rankU_fw H hRb hs']
          have hl' := fw_lt hs'
          obtain ⟨hs2, hW2, ht2, hp2, -, -, hm2⟩ := hs'
          simp only [lt3, true_and]
          by_cases hlt : T.e b.val < T.f s
          · have hle := hm2 s hs1 hW1 (ht1.trans ht) (by omega) hsb hlt
            rcases Nat.lt_or_eq_of_le hle with hlt' | heq
            · have := H.fifo _ hs1 _ hs2 hW1 hW2 (ht1.trans (ht.trans ht2.symm)) hlt'
              omega
            · have := H.uniq _ hs1 _ hs2 (ht1.trans (ht.trans ht2.symm)) heq
              subst this; omega
          · omega
        · rw [rankU_nofw (isR_not_isW hRb) hfb]
          obtain ⟨y, hy, -⟩ := overlap_iff.mp hsb
          have := (nofw_rf H b.2 hRb (mem_bytes.mpr hy) hfb).1 s hs1 hW1 (ht1.trans ht)
            (by omega) hsb
          simp only [lt3]; omega
      · rw [rankU_nofw (isR_not_isW hRa) hfa]
        by_cases hfb : ∃ s, Fw x T b.val s
        · obtain ⟨s', hs'⟩ := hfb
          rw [rankU_fw H hRb hs']
          have := fw_lt hs'
          simp only [lt3]; omega
        · rw [rankU_nofw (isR_not_isW hRb) hfb]
          simp only [lt3, true_and]; omega
    · -- R → W
      rw [rankU_W hWb]
      have := H.eLeF _ b.2 hWb
      by_cases hfa : ∃ s, Fw x T a.val s
      · obtain ⟨s, hs⟩ := hfa
        rw [rankU_fw H hRa hs]
        obtain ⟨hs1, hW1, ht1, hp1, -, -, -⟩ := hs
        have := H.fifo _ hs1 _ b.2 hW1 hWb (ht1.trans ht) (by omega)
        simp only [lt3]; omega
      · rw [rankU_nofw (isR_not_isW hRa) hfa]
        simp only [lt3]; omega
    · -- W → R
      rw [rankU_W hWa]
      by_cases hfb : ∃ s, Fw x T b.val s
      · obtain ⟨s, hs⟩ := hfb
        rw [rankU_fw H hRb hs]
        have hl := fw_lt hs
        obtain ⟨hs1, hW1, ht1, hp1, -, -, hm⟩ := hs
        simp only [lt3]
        by_cases hlt : T.e b.val < T.f a.val
        · have hle := hm _ a.2 hWa ht hpos (overlap_symm hov) hlt
          rcases Nat.lt_or_eq_of_le hle with hlt' | heq
          · have := H.fifo _ a.2 _ hs1 hWa hW1 (ht.trans ht1.symm) hlt'
            omega
          · have := H.uniq _ a.2 _ hs1 (ht.trans ht1.symm) heq
            rw [this]; omega
        · omega
      · rw [rankU_nofw (isR_not_isW hRb) hfb]
        obtain ⟨y, -, hy⟩ := overlap_iff.mp hov
        have := (nofw_rf H b.2 hRb (mem_bytes.mpr hy) hfb).1 _ a.2 hWa ht hpos (overlap_symm hov)
        simp only [lt3]; omega
    · -- W → W
      rw [rankU_W hWa, rankU_W hWb]
      have := H.fifo _ a.2 _ b.2 hWa hWb ht hpos
      simp only [lt3, true_and]; omega
  · obtain ⟨c, hc, hs⟩ := BRel.seq_elim h
    rw [sm_eq H hs] at hc
    simp only [Exec.com, BRel.union_iff] at hc
    rcases hc with hc | hc | hc
    · -- rf
      simp only [Exec.rfR, Bool.and_eq_true, List.any_eq_true, ev_eq, beq_iff_eq] at hc
      obtain ⟨⟨hW, hR⟩, y, hy, hrf, -⟩ := hc
      rw [rankU_W hW]
      by_cases hf : ∃ s, Fw x T b.val s
      · obtain ⟨s, hs⟩ := hf
        rw [rankU_fw H hR hs, fw_rf H b.2 hR hy hs] at *
        cases hrf
        simp only [lt3, true_and]; omega
      · rw [rankU_nofw (isR_not_isW hR) hf]
        have := ((nofw_rf H b.2 hR hy hf).2 _ hrf).1
        simp only [lt3]; omega
    · -- co
      simp only [Exec.coR, Bool.and_eq_true, List.any_eq_true, ev_eq] at hc
      obtain ⟨⟨hWa, hWc⟩, y, -, -, hb⟩ := hc
      have := co_before H hb
      rw [rankU_W hWa, rankU_W hWc]
      simp only [lt3, true_and]; omega
    · -- fr
      simp only [Exec.frR, Bool.and_eq_true, List.any_eq_true, ev_eq] at hc
      obtain ⟨⟨hR, hW⟩, y, hy, hcov, hfr⟩ := hc
      rw [rankU_W hW]
      by_cases hf : ∃ s, Fw x T a.val s
      · obtain ⟨s, hs⟩ := hf
        rw [rankU_fw H hR hs]
        rw [fw_rf H a.2 hR hy hs] at hfr
        have := co_before H hfr
        simp only [lt3]; omega
      · rw [rankU_nofw (isR_not_isW hR) hf]
        have := fr_le H a.2 hR hy b.2 hW hcov (by revert hfr; cases x.rf a y <;> simp)
        simp only [lt3]; omega

theorem uniproc_acyclic (H : TimedOk x T) : x.uniproc.Acyclic :=
  acyclic_of_rank lt3 lt3_trans lt3_irrefl (rankU x T) (fun _ _ h => uniproc_rank H h)

/-! ## Atomicity -/

theorem atomic (H : TimedOk x T) : x.atomicB = true := by
  unfold Exec.atomicB
  rw [BRel.emptyB_iff]
  intro r w
  by_contra hne
  simp only [Bool.not_eq_false, BRel.inter_iff, Exec.rmwR, List.contains_iff_mem] at hne
  obtain ⟨hrmw, hseq⟩ := hne
  obtain ⟨c, hfre, hcoe⟩ := BRel.seq_elim hseq
  obtain ⟨-, -, hR, -, -, hfe⟩ := H.rmwOk _ hrmw
  simp only at hR hfe
  simp only [Exec.fre, Exec.coe, BRel.inter_iff, Exec.frR, Exec.coR, Exec.ext, Bool.and_eq_true,
    List.any_eq_true, bne_iff_ne, ne_eq, ev_eq] at hfre hcoe
  obtain ⟨⟨⟨-, hWc⟩, y, hy, hcov, hfr⟩, hext⟩ := hfre
  obtain ⟨⟨-, z, -, -, hb⟩, -⟩ := hcoe
  have hle := fr_le H r.2 hR hy c.2 hWc hcov (by revert hfr; cases x.rf r y <;> simp)
  have hlt := co_before H hb
  have hne : T.f c.val ≠ T.e r.val := H.clash _ r.2 _ c.2 hR hWc
  omega

theorem tso (H : TimedOk x T) : x.Tso := ⟨atomic H, uniproc_acyclic H, ghb_acyclic H⟩

end

end Silmaril.X86.MemoryModel.OpAx.Proofs
