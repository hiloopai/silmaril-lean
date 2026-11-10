module

public import Silmaril.Proofs.X86.Concurrency.Cir.Seq.Mem

/-!
# The single-threaded lift on candidate executions

For a list of units of **one thread** (`Shape`: one `tid`, positions
non-decreasing along the list, and two units at the same position touch disjoint bytes):

* `rf_lastW`, `coLast_lastW` (**soundness**): in a well-formed candidate whose `po-loc | com`
  is acyclic (XL's coherence axiom, so this holds under SC, TSO and XL), every read byte comes
  from the last earlier write of that byte (or the initial value), and the coherence-last write
  of a byte is its last write in the list;
* `seqExec_*` (**completeness**): conversely the candidate `seqExec` that takes exactly these
  `rf` and `co` is SC-consistent, and well-formed under the unit facts of `ShapeWf`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Seq

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Seq
open Silmaril.X86.MemoryModel.Litmus (Byte dummyEv)
open Silmaril.X86.MemoryModel.Axiomatic (Ev Exec before BRel)
open Relation (TransGen)

/-- The units of one thread, in an order compatible with program order. -/
structure Shape (evs : List Ev) : Prop where
  tid : ∀ e ∈ evs, e.tid = 0
  mono : ∀ i j (hi : i < evs.length) (hj : j < evs.length), i ≤ j → evs[i].pos ≤ evs[j].pos
  disj : ∀ i j (hi : i < evs.length) (hj : j < evs.length), i ≠ j → evs[i].pos = evs[j].pos →
    ∀ y, ¬ (evs[i].covers y = true ∧ evs[j].covers y = true)

theorem mem_bytes {e : Ev} {y : Nat} : y ∈ e.bytes ↔ e.covers y = true := by
  simp only [Ev.bytes, List.mem_range'_1, Ev.covers, Bool.and_eq_true, decide_eq_true_eq]

theorem any_bytes {e : Ev} {p : Nat → Bool} : e.bytes.any p = true ↔ ∃ y, e.covers y = true ∧ p y = true := by
  simp only [List.any_eq_true, mem_bytes]

section
variable {x : Exec}

theorem ev_eq (a : Fin x.n) : x.ev a = x.evs[a.val] := rfl

theorem evN_eq {i : Nat} (h : i < x.n) : x.evN i = x.evs[i] := getD_eq h _

/-- Distinct units sharing a byte have distinct positions; with `Shape`, an earlier one is
`po`-before. -/
theorem po_of_lt (hS : Shape x.evs) {a b : Fin x.n} (hab : a.val < b.val) {y : Nat}
    (ha : (x.ev a).covers y = true) (hb : (x.ev b).covers y = true) : x.po a b = true := by
  simp only [Exec.po, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
  refine ⟨(hS.tid _ (List.getElem_mem a.2)).trans (hS.tid _ (List.getElem_mem b.2)).symm, ?_⟩
  have h1 := hS.mono a b a.2 b.2 (le_of_lt hab)
  have h2 : (x.ev a).pos ≠ (x.ev b).pos := fun h => hS.disj a b a.2 b.2 (by omega) h y ⟨ha, hb⟩
  exact lt_of_le_of_ne h1 h2

theorem isM_of_covers {e : Ev} (hR : e.isR = true ∨ e.isW = true) : e.isM = true := by
  simp only [Ev.isM, Bool.or_eq_true]; exact hR

theorem poLoc_of (hS : Shape x.evs) {a b : Fin x.n} (hab : a.val < b.val) {y : Nat}
    (haM : (x.ev a).isM = true) (hbM : (x.ev b).isM = true)
    (ha : (x.ev a).covers y = true) (hb : (x.ev b).covers y = true) : x.poLoc a b = true := by
  simp only [Exec.poLoc, BRel.inter_iff]
  refine ⟨po_of_lt hS hab ha hb, ?_⟩
  simp only [Exec.loc, haM, hbM, Bool.true_and]
  exact any_bytes.mpr ⟨y, ha, hb⟩

theorem smT_refl (a : Fin x.n) : x.smT a a = true := by simp [Exec.smT]

theorem uni_of_com {a b : Fin x.n} (h : x.com a b = true) : x.uniprocXl a b = true :=
  BRel.union_iff.mpr (.inr (BRel.seq_of_left smT_refl h))

theorem uni_of_poLoc {a b : Fin x.n} (h : x.poLoc a b = true) : x.uniprocXl a b = true :=
  BRel.union_iff.mpr (.inl h)

theorem cyc2 (hu : BRel.Acyclic x.uniprocXl) {a b : Fin x.n} (h1 : x.uniprocXl a b = true)
    (h2 : x.uniprocXl b a = true) : False :=
  hu a (TransGen.tail (TransGen.single h1) h2)

theorem com_of_rfR {a b : Fin x.n} (h : x.rfR a b = true) : x.com a b = true := by
  simp [Exec.com, BRel.union, h]

theorem com_of_coR {a b : Fin x.n} (h : x.coR a b = true) : x.com a b = true := by
  simp [Exec.com, BRel.union, h]

theorem com_of_frR {a b : Fin x.n} (h : x.frR a b = true) : x.com a b = true := by
  simp [Exec.com, BRel.union, h]

/-! ## Well-formedness, unpacked -/

theorem wf_rf (hwf : x.Wf = true) (r : Fin x.n) (hr : (x.ev r).isR = true) {y : Nat}
    (hy : (x.ev r).covers y = true) {w : Nat} (h : x.rf r.val y = some w) :
    ∃ hw : w < x.n, (x.evs[w]).isW = true ∧ (x.evs[w]).covers y = true := by
  simp only [Exec.Wf, Bool.and_eq_true, List.all_eq_true] at hwf
  have := hwf.1.1.1.1 r (List.mem_finRange r)
  simp only [hr, Bool.not_true, Bool.false_or, List.all_eq_true] at this
  have := this y (mem_bytes.mpr hy)
  rw [h] at this
  simp only [Exec.valid, Bool.and_eq_true, decide_eq_true_eq] at this
  obtain ⟨⟨hv, hW⟩, hC⟩ := this
  exact ⟨hv, by rwa [evN_eq hv] at hW, by rwa [evN_eq hv] at hC⟩

theorem touched_of {y : Nat} (w : Fin x.n) (hW : (x.ev w).isW = true) (hC : (x.ev w).covers y = true) :
    y ∈ x.touched := by
  simp only [Exec.touched, List.mem_flatMap, List.mem_filter]
  exact ⟨x.ev w, ⟨List.getElem_mem _, isM_of_covers (.inr hW)⟩, mem_bytes.mpr hC⟩

theorem wf_co (hwf : x.Wf = true) {y : Nat} (hy : y ∈ x.touched) :
    (x.co y).Nodup ∧ (∀ w ∈ x.co y, ∃ hw : w < x.n, (x.evs[w]).isW = true ∧ (x.evs[w]).covers y = true) ∧
      ∀ w : Fin x.n, (x.ev w).isW = true → (x.ev w).covers y = true → w.val ∈ x.co y := by
  simp only [Exec.Wf, Bool.and_eq_true, List.all_eq_true] at hwf
  have := hwf.1.1.1.2 y hy
  simp only [decide_eq_true_eq] at this
  obtain ⟨⟨hnd, hall⟩, hcov⟩ := this
  refine ⟨hnd, fun w hw => ?_, fun w hW hC => ?_⟩
  · have := hall w hw
    simp only [Exec.valid, decide_eq_true_eq] at this
    obtain ⟨⟨hv, hW⟩, hC⟩ := this
    exact ⟨hv, by rwa [evN_eq hv] at hW, by rwa [evN_eq hv] at hC⟩
  · have := hcov w (List.mem_finRange w)
    simp only [Bool.not_and, Bool.or_eq_true, Bool.not_eq_true', List.contains_iff_mem] at this
    rcases this with (h | h) | h
    · exact absurd (show (x.ev w).isW = false from h) (by simp [hW])
    · exact absurd (show (x.ev w).covers y = false from h) (by simp [hC])
    · exact h

/-! ## Soundness -/

theorem W_ne_R {e : Ev} (hW : e.isW = true) (hR : e.isR = true) : False := by
  simp only [Ev.isW, Ev.isR, beq_iff_eq] at hW hR; rw [hW] at hR; cases hR

/-- **Reads take the last earlier write.** -/
theorem rf_lastW (hS : Shape x.evs) (hwf : x.Wf = true) (hu : BRel.Acyclic x.uniprocXl)
    (r : Fin x.n) (hr : (x.ev r).isR = true) {y : Nat} (hy : (x.ev r).covers y = true) :
    x.rf r.val y = lastW x.evs y r.val := by
  have hrM : (x.ev r).isM = true := isM_of_covers (.inl hr)
  cases hrf : x.rf r.val y with
  | some w =>
    obtain ⟨hw, hW, hC⟩ := wf_rf hwf r hr hy hrf
    let w' : Fin x.n := ⟨w, hw⟩
    have hwM : (x.ev w').isM = true := isM_of_covers (.inr hW)
    have hrfR : x.rfR w' r = true := by
      simp only [Exec.rfR, Bool.and_eq_true]
      refine ⟨⟨hW, hr⟩, any_bytes.mpr ⟨y, hy, ?_⟩⟩
      simp only [hrf, Bool.and_eq_true, beq_iff_eq]; exact ⟨rfl, hC⟩
    -- `w` is before `r`
    have hwr : w < r.val := by
      rcases Nat.lt_trichotomy w r.val with c | c | c
      · exact c
      · exact absurd (by simpa [ev_eq, ← c] using hr) (fun h => W_ne_R hW h)
      · exact (cyc2 hu (uni_of_com (com_of_rfR hrfR))
          (uni_of_poLoc (poLoc_of hS (a := r) (b := w') c hrM hwM hy hC))).elim
    obtain ⟨i, hi, hwi⟩ := lastW_exists hwr ⟨hw, hW, hC⟩
    obtain ⟨hir, ⟨hil, hiW, hiC⟩, -⟩ := lastW_some hi
    rw [hi]
    rcases Nat.lt_or_ge w i with c | c
    · exfalso
      let i' : Fin x.n := ⟨i, hil⟩
      have hiM : (x.ev i').isM = true := isM_of_covers (.inr hiW)
      have hty : y ∈ x.touched := touched_of w' hW hC
      obtain ⟨hnd, -, hcov⟩ := wf_co hwf hty
      rcases before_total (hcov w' hW hC) (hcov i' hiW hiC) (by simp [w', i']; omega) with hb | hb
      · -- `r` reads `y` from `w`, and `i` is coherence-after `w`: `fr r i`, `po-loc i r`
        have hfr : x.frR r i' = true := by
          simp only [Exec.frR, Bool.and_eq_true]
          refine ⟨⟨hr, hiW⟩, any_bytes.mpr ⟨y, hy, ?_⟩⟩
          simp only [hrf, Bool.and_eq_true]; exact ⟨hiC, hb⟩
        exact cyc2 hu (uni_of_com (com_of_frR hfr))
          (uni_of_poLoc (poLoc_of hS (a := i') (b := r) hir hiM hrM hiC hy))
      · have hco : x.coR i' w' = true := by
          simp only [Exec.coR, Bool.and_eq_true]
          exact ⟨⟨hiW, hW⟩, any_bytes.mpr ⟨y, hiC, by simp only [Bool.and_eq_true]; exact ⟨hC, hb⟩⟩⟩
        exact cyc2 hu (uni_of_com (com_of_coR hco))
          (uni_of_poLoc (poLoc_of hS (a := w') (b := i') c hwM hiM hC hiC))
    · congr 1; omega
  | none =>
    cases hl : lastW x.evs y r.val with
    | none => rfl
    | some i =>
      exfalso
      obtain ⟨hir, ⟨hil, hiW, hiC⟩, -⟩ := lastW_some hl
      let i' : Fin x.n := ⟨i, hil⟩
      have hfr : x.frR r i' = true := by
        simp only [Exec.frR, Bool.and_eq_true]
        refine ⟨⟨hr, hiW⟩, any_bytes.mpr ⟨y, hy, ?_⟩⟩
        simp only [hrf, Bool.and_true]; exact hiC
      exact cyc2 hu (uni_of_com (com_of_frR hfr))
        (uni_of_poLoc (poLoc_of hS (a := i') (b := r) hir (isM_of_covers (.inr hiW)) hrM hiC hy))

/-- A byte some write unit covers. -/
theorem written_iff {y : Nat} :
    Silmaril.X86.MemoryModel.Litmus.writtenByte x y = true ↔ ∃ w : Fin x.n, (x.ev w).isW = true ∧ (x.ev w).covers y = true := by
  simp only [Silmaril.X86.MemoryModel.Litmus.writtenByte, List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨e, he, h1, h2⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    exact ⟨⟨i, hi⟩, h1, h2⟩
  · rintro ⟨w, h1, h2⟩
    exact ⟨_, List.getElem_mem _, h1, h2⟩

/-- **The coherence-last write is the last write.** -/
theorem coLast_lastW (hS : Shape x.evs) (hwf : x.Wf = true) (hu : BRel.Acyclic x.uniprocXl)
    {y : Nat} (w0 : Fin x.n) (hW0 : (x.ev w0).isW = true) (hC0 : (x.ev w0).covers y = true) :
    (x.co y).getLast? = lastW x.evs y x.n := by
  have hty : y ∈ x.touched := touched_of w0 hW0 hC0
  obtain ⟨hnd, hall, hcov⟩ := wf_co hwf hty
  have hne : x.co y ≠ [] := fun h => by simpa [h] using hcov w0 hW0 hC0
  obtain ⟨w, hw⟩ : ∃ w, (x.co y).getLast? = some w :=
    ⟨(x.co y).getLast hne, List.getLast?_eq_some_getLast hne⟩
  rw [hw]
  obtain ⟨hwn, hwW, hwC⟩ := hall w (List.mem_of_getLast? hw)
  let w' : Fin x.n := ⟨w, hwn⟩
  symm
  refine lastW_eq hwn ⟨hwn, hwW, hwC⟩ fun j hj hjn ⟨hjl, hjW, hjC⟩ => ?_
  let j' : Fin x.n := ⟨j, hjl⟩
  have hb := before_last hnd hw (hcov j' hjW hjC) (by simp [j']; omega)
  have hco : x.coR j' w' = true := by
    simp only [Exec.coR, Bool.and_eq_true]
    exact ⟨⟨hjW, hwW⟩, any_bytes.mpr ⟨y, hjC, by simp only [Bool.and_eq_true]; exact ⟨hwC, hb⟩⟩⟩
  exact cyc2 hu (uni_of_com (com_of_coR hco))
    (uni_of_poLoc (poLoc_of hS (a := w') (b := j') hj (isM_of_covers (.inr hwW))
      (isM_of_covers (.inr hjW)) hwC hjC))

/-! ## Reads and final bytes -/

/-- If every byte of read unit `r` comes from its last earlier write, it reads the `memAt`
bytes. -/
theorem readBytes_of (m0 : Mem) {r : Nat} (hr : r < x.n)
    (h : ∀ y, (x.evs[r]).covers y = true → x.rf r y = lastW x.evs y r) :
    x.readBytes (fun y => (m0 y).getD 0) r = bytesAt (memAt x.evs m0 r) (x.evs[r]).addr (x.evs[r]).size := by
  simp only [Exec.readBytes, bytesAt, evN_eq hr, Ev.bytes]
  refine List.map_congr_left fun y hy => ?_
  have hc : (x.evs[r]).covers y = true := mem_bytes.mp hy
  simp only [Exec.readByte, memAt, h y hc]
  cases lastW x.evs y r with
  | none => rfl
  | some w => simp only [Exec.evN]; rfl

/-- If the coherence-last write of every written byte is its last write, the final memory is
`memAt` at the end. -/
theorem finalMem_of (m0 : Mem)
    (h : ∀ y (w : Fin x.n), (x.ev w).isW = true → (x.ev w).covers y = true →
      (x.co y).getLast? = lastW x.evs y x.n) (y : Nat) :
    (if Silmaril.X86.MemoryModel.Litmus.writtenByte x y then
        some (x.finalByte (fun y => (m0 y).getD 0) y) else m0 y) = memAt x.evs m0 x.n y := by
  by_cases hw : Silmaril.X86.MemoryModel.Litmus.writtenByte x y = true
  · obtain ⟨w, hW, hC⟩ := written_iff.mp hw
    simp only [hw, ite_true, Exec.finalByte, h y w hW hC, memAt]
    obtain ⟨i, hi, -⟩ := lastW_exists (evs := x.evs) (y := y) w.2 ⟨w.2, hW, hC⟩
    rw [hi]; simp only [Exec.evN]; rfl
  · have hn : lastW x.evs y x.n = none := by
      cases hl : lastW x.evs y x.n with
      | none => rfl
      | some i =>
        obtain ⟨hi, ⟨hil, hiW, hiC⟩, -⟩ := lastW_some hl
        exact absurd (written_iff.mpr ⟨⟨i, hil⟩, hiW, hiC⟩) hw
    simp only [Bool.not_eq_true] at hw
    simp [hw, memAt, hn]

/-! ## Completeness -/

end

/-- The sequential candidate: every read byte from its last earlier write, coherence in list
order. -/
def seqExec (evs : List Ev) (rmw : List (Nat × Nat)) : Exec where
  evs := evs
  rf := fun r y => lastW evs y r
  co := fun y => (List.range evs.length).filter fun i =>
    (evs.getD i dummyEv).isW && (evs.getD i dummyEv).covers y
  rmw := rmw

/-- The unit facts well-formedness needs beyond `Shape`. -/
structure ShapeWf (evs : List Ev) (rmw : List (Nat × Nat)) : Prop where
  sm : ∀ i j (hi : i < evs.length) (hj : j < evs.length), evs[i].pos = evs[j].pos →
    evs[i].act = evs[j].act ∧ evs[i].locked = evs[j].locked ∧ evs[i].ann = evs[j].ann ∧
      evs[i].accAddr = evs[j].accAddr ∧ evs[i].accSize = evs[j].accSize
  unit : ∀ e ∈ evs, if e.isM then 0 < e.size ∧ e.accAddr ≤ e.addr ∧
      e.addr + e.size ≤ e.accAddr + e.accSize ∧ (e.isW = true → e.data.length = e.size)
    else e.size = 0
  rmw : ∀ p ∈ rmw, ∃ (h1 : p.1 < evs.length) (h2 : p.2 < evs.length),
    evs[p.1].isR = true ∧ evs[p.2].isW = true ∧ evs[p.1].pos < evs[p.2].pos ∧
      evs[p.1].locked = true ∧ evs[p.2].locked = true ∧ evs[p.1].accAddr = evs[p.2].accAddr ∧
      evs[p.1].accSize = evs[p.2].accSize

section
variable {evs : List Ev} {rmw : List (Nat × Nat)}

theorem seq_n : (seqExec evs rmw).n = evs.length := rfl

theorem co_sorted (y : Nat) : ((seqExec evs rmw).co y).Pairwise (· < ·) :=
  List.Pairwise.filter _ List.pairwise_lt_range

theorem mem_co {y w : Nat} : w ∈ (seqExec evs rmw).co y ↔ WC evs y w := by
  simp only [seqExec, List.mem_filter, List.mem_range, Bool.and_eq_true, WC]
  constructor
  · rintro ⟨h, h1, h2⟩; exact ⟨h, by rwa [getD_eq h] at h1, by rwa [getD_eq h] at h2⟩
  · rintro ⟨h, h1, h2⟩; exact ⟨h, by rwa [getD_eq h], by rwa [getD_eq h]⟩

/-- Every `scRel` edge of the sequential candidate goes forward in position. -/
theorem seq_scRel_pos (hS : Shape evs) {a b : Fin (seqExec evs rmw).n}
    (h : (seqExec evs rmw).scRel a b = true) :
    ((seqExec evs rmw).ev a).pos < ((seqExec evs rmw).ev b).pos := by
  let x := seqExec evs rmw
  have hS' : Shape x.evs := hS
  have po_pos : ∀ {a b : Fin x.n}, x.po a b = true → (x.ev a).pos < (x.ev b).pos := by
    intro a b h; simp only [Exec.po, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2
  rcases BRel.union_iff.mp h with h | h
  · exact po_pos h
  obtain ⟨c, hac, hcb⟩ := BRel.seq_elim h
  have hcb' : (x.ev c).pos = (x.ev b).pos := by
    simp only [Exec.sm, Bool.and_eq_true, beq_iff_eq] at hcb; exact hcb.2
  rw [← hcb']
  simp only [Exec.com, BRel.union_iff] at hac
  rcases hac with hac | hac | hac
  · -- rf: from the last earlier write
    simp only [Exec.rfR, Bool.and_eq_true] at hac
    obtain ⟨⟨haW, hcR⟩, hany⟩ := hac
    obtain ⟨y, hy, hh⟩ := any_bytes.mp hany
    simp only [Bool.and_eq_true, beq_iff_eq] at hh
    obtain ⟨hl, haC⟩ := hh
    have hlt := (lastW_some hl).1
    exact po_pos (po_of_lt hS' hlt haC hy)
  · simp only [Exec.coR, Bool.and_eq_true] at hac
    obtain ⟨⟨haW, hcW⟩, hany⟩ := hac
    obtain ⟨y, hy, hh⟩ := any_bytes.mp hany
    simp only [Bool.and_eq_true] at hh
    exact po_pos (po_of_lt hS' (before_sorted (co_sorted y) hh.2) hy hh.1)
  · simp only [Exec.frR, Bool.and_eq_true] at hac
    obtain ⟨⟨haR, hcW⟩, hany⟩ := hac
    obtain ⟨y, hy, hh⟩ := any_bytes.mp hany
    simp only [Bool.and_eq_true] at hh
    obtain ⟨hcC, hm⟩ := hh
    have hac : a.val < c.val := by
      rcases Nat.lt_trichotomy a.val c.val with t | t | t
      · exact t
      · exfalso; have : a = c := Fin.ext t
        subst this; exact W_ne_R hcW haR
      · exfalso
        have hWC : WC evs y c := ⟨c.2, hcW, hcC⟩
        change (match lastW evs y a.val with
          | none => true | some v => before (x.co y) v c.val) = true at hm
        cases hl : lastW evs y a.val with
        | none => exact lastW_none hl c t hWC
        | some v =>
          rw [hl] at hm
          have hvc := before_sorted (co_sorted y) hm
          exact (lastW_some hl).2.2 c hvc t hWC
    exact po_pos (po_of_lt hS' hac hy hcC)

theorem seqExec_sc (hS : Shape evs) : (seqExec evs rmw).Sc := by
  refine ⟨?_, ?_⟩
  · simp only [Exec.atomicB]; rw [BRel.emptyB_iff]
    intro a b
    simp only [BRel.inter, BRel.seq, Exec.fre, Exec.ext, List.any_eq_false, Bool.and_eq_false_iff]
    right; intro c _
    have : ((seqExec evs rmw).ev a).tid = ((seqExec evs rmw).ev c).tid :=
      (hS.tid _ (List.getElem_mem a.2)).trans (hS.tid _ (List.getElem_mem c.2)).symm
    simp [this]
  · intro a hcyc
    have : ∀ a b, TransGen (seqExec evs rmw).scRel.Holds a b →
        ((seqExec evs rmw).ev a).pos < ((seqExec evs rmw).ev b).pos := by
      intro a b h
      induction h with
      | single h => exact seq_scRel_pos hS h
      | tail _ h ih => exact lt_trans ih (seq_scRel_pos hS h)
    exact lt_irrefl _ (this a a hcyc)

theorem seqExec_wf (hS : Shape evs) (hW : ShapeWf evs rmw) : (seqExec evs rmw).Wf = true := by
  have hev : ∀ a : Fin (seqExec evs rmw).n, (seqExec evs rmw).ev a = evs[a.val] := fun _ => rfl
  have hevN : ∀ i (h : i < evs.length), (seqExec evs rmw).evN i = evs[i] := fun i h => getD_eq h _
  simp only [Exec.Wf, Bool.and_eq_true, List.all_eq_true]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro r _
    simp only [Bool.or_eq_true, Bool.not_eq_true', List.all_eq_true]
    right; intro y _
    change (match lastW evs y r.val with
      | none => true | some w => (seqExec evs rmw).valid w && ((seqExec evs rmw).evN w).isW && ((seqExec evs rmw).evN w).covers y) = true
    cases hl : lastW evs y r.val with
    | none => rfl
    | some w =>
      obtain ⟨-, ⟨hwl, hwW, hwC⟩, -⟩ := lastW_some hl
      simp only [Exec.valid, Bool.and_eq_true, decide_eq_true_eq, hevN w hwl]
      exact ⟨⟨hwl, hwW⟩, hwC⟩
  · intro y _
    simp only [decide_eq_true_eq]
    refine ⟨⟨List.Nodup.filter _ List.nodup_range, fun w hw => ?_⟩, fun w _ => ?_⟩
    · obtain ⟨hwl, hwW, hwC⟩ := mem_co.mp hw
      simp [Exec.valid, hevN w hwl, hwW, hwC, seq_n, hwl]
    · simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_false_iff, List.contains_iff_mem]
      by_cases h : ((seqExec evs rmw).ev w).isW = true ∧ ((seqExec evs rmw).ev w).covers y = true
      · right; exact mem_co.mpr ⟨w.2, h.1, h.2⟩
      · left
        simp only [not_and, Bool.not_eq_true] at h
        by_cases h1 : ((seqExec evs rmw).ev w).isW = true
        · right; exact h h1
        · left; simpa using h1
  · intro p hp
    obtain ⟨h1, h2, hR, hWr, hpos, hl1, hl2, ha, hs⟩ := hW.rmw p hp
    simp only [Exec.valid, hevN _ h1, hevN _ h2]
    simp [seq_n, h1, h2, hR, hWr, hpos, hl1, hl2, ha, hs, hS.tid _ (List.getElem_mem h1),
      hS.tid _ (List.getElem_mem h2)]
  · intro a _ b _
    simp only [Bool.or_eq_true, Bool.not_eq_true']
    by_cases hsm : (seqExec evs rmw).sm a b = true
    · right
      simp only [Exec.sm, Bool.and_eq_true, beq_iff_eq] at hsm
      obtain ⟨e1, e2, e3, e4, e5⟩ := hW.sm a b a.2 b.2 hsm.2
      simp only [hev, Bool.and_eq_true, beq_iff_eq]
      exact ⟨⟨⟨⟨e1, e2⟩, e3⟩, e4⟩, e5⟩
    · left; simpa using hsm
  · intro e he
    have := hW.unit e he
    split
    · rename_i hM
      simp only [hM, ite_true] at this
      obtain ⟨u1, u2, u3, u4⟩ := this
      simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
        beq_iff_eq]
      refine ⟨⟨⟨u1, u2⟩, u3⟩, ?_⟩
      cases h : e.isW
      · left; rfl
      · right; exact u4 h
    · rename_i hM
      simpa [hM] using this

end

end Silmaril.Proofs.X86.Concurrency.Cir.Seq
