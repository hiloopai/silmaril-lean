module

public import Silmaril.X86.Concurrency.Cir.C11.Defs
public import Silmaril.X86.MemoryModel.Xl.Thms

/-!
# The x86 mapping is correct for RC11: the execution-level proof

`tso_rc11`: a
well-formed x86-TSO-consistent candidate whose memory units form cells (`Cells`) and whose C11
roles respect the mapping (`MapRoles`) is RC11-consistent.

The proof is direct (not a transcription of Lahav et al.'s, which goes through a
characterisation of TSO by program transformations):

* `whole`, atomicity: TSO's uniproc and atomicity;
* no-thin-air: `Exec.thinAir_of_tso`;
* `hb ⊆ (po ∪ rfe)⁺` (internal `rf` and `rmw` go forward in `po`), and a `po ∪ rfe` path between
  memory units that is not a single `po` edge is a `ghb` path after its first write
  (`hb_claim`);
* coherence: `eco` stays in one cell (`Cells`), and is a `ghb` path up to a final internal `rf`
  edge (`eco_claim`, using `rf ; fr ⊆ co` in a cell); a `po` edge closes a uniproc cycle, a
  `ghb` path a `ghb` cycle;
* SC: every `psc` edge is a path of `G = ghb ∪ po` through an `mfence` (`psc_G`), because SC
  writes are locked and SC fences are `mfence`s or locked; `G` is acyclic because its `po`
  edges at fences compress into `mfence` edges of `ghb` (`G_acyclic`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.C11Map

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.C11
open Silmaril.X86.MemoryModel.Axiomatic
open Relation

/-! ## Lists and bytes -/

theorem before_cons_of_ne {c a b : Nat} {l : List Nat} (h : c ≠ a) :
    before (c :: l) a b = before l a b := by
  simp [before, h]

theorem before_total {l : List Nat} {a b : Nat} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    before l a b = true ∨ before l b a = true := by
  induction l with
  | nil => simp at ha
  | cons c l ih =>
    by_cases hca : c = a
    · subst hca
      left
      simp only [before, beq_self_eq_true, ite_true, List.contains_eq_mem, decide_eq_true_eq]
      rcases List.mem_cons.mp hb with h | h
      · exact absurd h.symm hab
      · exact h
    · by_cases hcb : c = b
      · subst hcb
        right
        simp only [before, beq_self_eq_true, ite_true, List.contains_eq_mem, decide_eq_true_eq]
        rcases List.mem_cons.mp ha with h | h
        · exact absurd h.symm hca
        · exact h
      · rw [before_cons_of_ne hca, before_cons_of_ne hcb]
        exact ih (by simpa [Ne.symm hca] using ha) (by simpa [Ne.symm hcb] using hb)

theorem mem_bytes {e : Ev} {y : Nat} : y ∈ e.bytes ↔ e.addr ≤ y ∧ y < e.addr + e.size := by
  simp [Ev.bytes, List.mem_range'_1]

theorem covers_iff {e : Ev} {y : Nat} : e.covers y = true ↔ e.addr ≤ y ∧ y < e.addr + e.size := by
  simp [Ev.covers]

theorem covers_of_mem {e : Ev} {y : Nat} (h : y ∈ e.bytes) : e.covers y = true :=
  covers_iff.mpr (mem_bytes.mp h)

theorem mem_of_covers {e : Ev} {y : Nat} (h : e.covers y = true) : y ∈ e.bytes :=
  mem_bytes.mpr (covers_iff.mp h)

theorem not_R_and_W {e : Ev} (hr : e.isR = true) (hw : e.isW = true) : False := by
  simp only [Ev.isR, Ev.isW, beq_iff_eq] at hr hw
  rw [hr] at hw
  cases hw

theorem isM_of_isW {e : Ev} (h : e.isW = true) : e.isM = true := by simp [Ev.isM, h]
theorem isM_of_isR {e : Ev} (h : e.isR = true) : e.isM = true := by simp [Ev.isM, h]

theorem not_isM_of_fence {e : Ev} {k} (h : e.isFence k = true) : e.isM = false := by
  simp only [Ev.isFence, beq_iff_eq] at h
  simp [Ev.isM, Ev.isR, Ev.isW, h]

/-! ## What `Wf` gives -/

/-- The facts of `Wf` the proof uses. -/
structure WfF (x : Exec) : Prop where
  coAll : ∀ y ∈ x.touched, ∀ w : Fin x.n, (x.ev w).isW = true → (x.ev w).covers y = true →
    w.val ∈ x.co y
  rmwPo : ∀ a b : Fin x.n, x.rmwR a b = true → x.po a b = true
  smAct : ∀ a b : Fin x.n, x.sm a b = true → (x.ev a).act = (x.ev b).act

theorem evN_eq (x : Exec) (i : Nat) (h : i < x.n) : x.evN i = x.ev ⟨i, h⟩ := by
  simp [Exec.evN, Exec.ev, List.getD_eq_getElem?_getD, h]

theorem wfF {x : Exec} (h : x.Wf = true) : WfF x := by
  simp only [Exec.Wf, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨-, h2⟩, h3⟩, h4⟩, -⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · intro y hy w hW hC
    have := h2 y hy
    simp only [decide_eq_true_eq] at this
    have := this.2 w (List.mem_finRange w)
    simp only [hW, hC, Bool.and_self, Bool.not_true, Bool.false_or, List.contains_eq_mem,
      decide_eq_true_eq] at this
    exact this
  · intro a b hab
    simp only [Exec.rmwR, List.contains_eq_mem, decide_eq_true_eq] at hab
    have := h3 _ hab
    simp only [Exec.valid, decide_eq_true_eq, beq_iff_eq] at this
    have ht := this.1.1.1.1.1.2
    have hp := this.1.1.1.1.2
    rw [evN_eq x a.val a.isLt, evN_eq x b.val b.isLt] at ht hp
    simp [Exec.po, ht, hp]
  · intro a b hab
    have := h4 a (List.mem_finRange a) b (List.mem_finRange b)
    simp only [hab, Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at this
    exact this.1.1.1.1

/-! ## Communication, uniproc and `ghb` -/

section Rel
variable {x : Exec}

theorem com_uni {a b : Fin x.n} (h : x.com a b = true) : x.uniproc a b = true := by
  simp only [Exec.uniproc, BRel.union_iff]
  exact .inr (BRel.seq_of_left x.sm_refl h)

theorem rf_com {a b : Fin x.n} (h : x.rfR a b = true) : x.com a b = true := by
  simp [Exec.com, BRel.union_iff, h]

theorem co_com {a b : Fin x.n} (h : x.coR a b = true) : x.com a b = true := by
  simp [Exec.com, BRel.union_iff, h]

theorem fr_com {a b : Fin x.n} (h : x.frR a b = true) : x.com a b = true := by
  simp [Exec.com, BRel.union_iff, h]

theorem rf_kinds {a b : Fin x.n} (h : x.rfR a b = true) :
    (x.ev a).isW = true ∧ (x.ev b).isR = true := by
  simp only [Exec.rfR, Bool.and_eq_true] at h
  exact h.1

theorem co_kinds {a b : Fin x.n} (h : x.coR a b = true) :
    (x.ev a).isW = true ∧ (x.ev b).isW = true := by
  simp only [Exec.coR, Bool.and_eq_true] at h
  exact h.1

theorem fr_kinds {a b : Fin x.n} (h : x.frR a b = true) :
    (x.ev a).isR = true ∧ (x.ev b).isW = true := by
  simp only [Exec.frR, Bool.and_eq_true] at h
  exact h.1

theorem com_kinds {a b : Fin x.n} (h : x.com a b = true) :
    (x.ev a).isM = true ∧ (x.ev b).isM = true := by
  simp only [Exec.com, BRel.union_iff] at h
  rcases h with h | h | h
  · exact ⟨isM_of_isW (rf_kinds h).1, isM_of_isR (rf_kinds h).2⟩
  · exact ⟨isM_of_isW (co_kinds h).1, isM_of_isW (co_kinds h).2⟩
  · exact ⟨isM_of_isR (fr_kinds h).1, isM_of_isW (fr_kinds h).2⟩

/-- Two communicating units share a byte. -/
theorem com_share {a b : Fin x.n} (h : x.com a b = true) :
    ∃ y, (x.ev a).covers y = true ∧ (x.ev b).covers y = true := by
  simp only [Exec.com, BRel.union_iff] at h
  rcases h with h | h | h
  · simp only [Exec.rfR, Bool.and_eq_true, List.any_eq_true, beq_iff_eq] at h
    obtain ⟨-, y, hy, -, hc⟩ := h
    exact ⟨y, hc, covers_of_mem hy⟩
  · simp only [Exec.coR, Bool.and_eq_true, List.any_eq_true] at h
    obtain ⟨-, y, hy, hc, -⟩ := h
    exact ⟨y, covers_of_mem hy, hc⟩
  · simp only [Exec.frR, Bool.and_eq_true, List.any_eq_true] at h
    obtain ⟨-, y, hy, hc, -⟩ := h
    exact ⟨y, covers_of_mem hy, hc⟩

theorem ppo_ghb {a b : Fin x.n} (h : x.ppo a b = true) : x.ghb a b = true := by
  simp only [Exec.ghb, BRel.union_iff]
  exact .inr (.inr (.inl h))

theorem comGhb_ghb {a b : Fin x.n} (h : (x.rfe.union (x.frR.union x.coR)) a b = true) :
    x.ghb a b = true := by
  simp only [Exec.ghb, BRel.union_iff]
  exact .inr (.inr (.inr (BRel.seq_of_left x.sm_refl h)))

theorem rfe_ghb {a b : Fin x.n} (h : x.rfe a b = true) : x.ghb a b = true :=
  comGhb_ghb (BRel.union_iff.mpr (.inl h))

theorem fr_ghb {a b : Fin x.n} (h : x.frR a b = true) : x.ghb a b = true :=
  comGhb_ghb (BRel.union_iff.mpr (.inr (BRel.union_iff.mpr (.inl h))))

theorem co_ghb {a b : Fin x.n} (h : x.coR a b = true) : x.ghb a b = true :=
  comGhb_ghb (BRel.union_iff.mpr (.inr (BRel.union_iff.mpr (.inr h))))

theorem mfence_ghb {a b : Fin x.n} (h : x.mfence a b = true) : x.ghb a b = true := by
  simp only [Exec.ghb, BRel.union_iff]
  exact .inl h

/-- A `po` edge from a read to a memory unit, or between writes, is `ghb`. -/
theorem po_ghb_R {a b : Fin x.n} (hpo : x.po a b = true) (ha : (x.ev a).isR = true)
    (hb : (x.ev b).isM = true) : x.ghb a b = true :=
  ppo_ghb (by simp [Exec.ppo, hpo, ha, hb])

theorem po_ghb_W {a b : Fin x.n} (hpo : x.po a b = true) (ha : (x.ev a).isM = true)
    (hb : (x.ev b).isW = true) : x.ghb a b = true := by
  simp only [Ev.isM, Bool.or_eq_true] at ha
  rcases ha with ha | ha
  · exact ppo_ghb (by simp [Exec.ppo, hpo, ha, hb, Ev.isM])
  · exact ppo_ghb (by simp [Exec.ppo, hpo, ha, hb])

/-- A `po` edge between memory units with a locked end is `ghb`. -/
theorem po_ghb_A {a b : Fin x.n} (hpo : x.po a b = true) (ha : (x.ev a).isM = true)
    (hb : (x.ev b).isM = true) (hl : (x.ev a).isA = true ∨ (x.ev b).isA = true) :
    x.ghb a b = true := by
  have ha' := ha
  simp only [Ev.isM, Bool.or_eq_true] at ha
  rcases ha with ha | ha
  · exact po_ghb_R hpo ha hb
  · have hb' := hb
    simp only [Ev.isM, Bool.or_eq_true] at hb
    rcases hb with hb | hb
    · simp only [Exec.ghb, BRel.union_iff]
      refine .inr (.inl ?_)
      simp only [Exec.implied, hpo, ha, hb, Bool.and_self, Bool.true_and, Bool.or_eq_true]
      exact hl
    · exact po_ghb_W hpo ha' hb

theorem mfence_elim {a b : Fin x.n} (h : x.mfence a b = true) :
    ∃ f, (x.ev f).isFence .mfence = true ∧ x.po a f = true ∧ x.po f b = true := by
  simp only [Exec.mfence, Exec.fencerel, List.any_eq_true, Bool.and_eq_true] at h
  obtain ⟨f, -, ⟨hf, h1⟩, h2⟩ := h
  exact ⟨f, hf, h1, h2⟩

theorem mfence_intro {a b f : Fin x.n} (hf : (x.ev f).isFence .mfence = true)
    (h1 : x.po a f = true) (h2 : x.po f b = true) : x.ghb a b = true := by
  apply mfence_ghb
  simp only [Exec.mfence, Exec.fencerel, List.any_eq_true, Bool.and_eq_true]
  exact ⟨f, List.mem_finRange f, ⟨hf, h1⟩, h2⟩

/-- Under uniproc, a reads-from edge is external or goes forward in program order. -/
theorem rf_po_or_rfe (hu : BRel.Acyclic x.uniproc) {a b : Fin x.n} (h : x.rfR a b = true) :
    x.po a b = true ∨ x.rfe a b = true := by
  have hcom : x.uniproc a b = true := com_uni (rf_com h)
  by_cases he : x.ext a b = true
  · exact .inr (BRel.inter_iff.mpr ⟨h, he⟩)
  · have htid : (x.ev a).tid = (x.ev b).tid := by simpa [Exec.ext] using he
    rcases Nat.lt_trichotomy (x.ev a).pos (x.ev b).pos with hlt | heq | hgt
    · exact .inl (by simp [Exec.po, htid, hlt])
    · exfalso
      apply hu a
      refine .single ?_
      simp only [BRel.Holds, Exec.uniproc, BRel.union_iff]
      refine .inr ?_
      simp only [BRel.seq, List.any_eq_true, Bool.and_eq_true]
      exact ⟨b, List.mem_finRange b, rf_com h, by simp [Exec.sm, htid, heq]⟩
    · exfalso
      have hk := rf_kinds h
      obtain ⟨y, hya, hyb⟩ := com_share (rf_com h)
      have hloc : x.loc b a = true := by
        simp only [Exec.loc, Bool.and_eq_true, List.any_eq_true]
        exact ⟨⟨isM_of_isR hk.2, isM_of_isW hk.1⟩, y, mem_of_covers hyb, hya⟩
      have hpo : x.poLoc b a = true :=
        BRel.inter_iff.mpr ⟨by simp [Exec.po, htid, hgt], hloc⟩
      apply hu b
      exact .tail (.single (BRel.union_iff.mpr (.inl hpo))) hcom

/-- `ghb` edges at non-memory units (fences) are `mfence` edges. -/
theorem ghb_fence (hw : WfF x) {a b : Fin x.n} (h : x.ghb a b = true)
    (hf : (x.ev a).isM = false ∨ (x.ev b).isM = false) : x.mfence a b = true := by
  simp only [Exec.ghb, BRel.union_iff] at h
  rcases h with h | h | h | h
  · exact h
  · exfalso
    simp only [Exec.implied, Bool.and_eq_true] at h
    rcases hf with hf | hf
    · simp [isM_of_isW h.1.1.2] at hf
    · simp [isM_of_isR h.1.2] at hf
  · exfalso
    simp only [Exec.ppo, Bool.and_eq_true, Bool.or_eq_true] at h
    rcases h.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rcases hf with hf | hf
      · simp [isM_of_isW h1] at hf
      · simp [isM_of_isW h2] at hf
    · rcases hf with hf | hf
      · simp [isM_of_isR h1] at hf
      · simp [h2] at hf
  · exfalso
    obtain ⟨c, h1, h2⟩ := BRel.seq_elim h
    have hk := com_kinds (x.comGhb_part h1)
    have hact := hw.smAct _ _ h2
    have hbM : (x.ev b).isM = true := by
      have := hk.2
      simp only [Ev.isM, Ev.isR, Ev.isW] at this ⊢
      rwa [← hact]
    rcases hf with hf | hf
    · simp [hk.1] at hf
    · simp [hbM] at hf

end Rel

/-! ## Happens-before is a `po ∪ rfe` path -/

section Hb
variable {x : Exec}

theorem tg_flat {α : Type _} {r s : α → α → Prop} (h : ∀ a b, r a b → TransGen s a b) {a b : α}
    (hab : TransGen r a b) : TransGen s a b := by
  induction hab with
  | single h1 => exact h _ _ h1
  | tail _ h2 ih => exact ih.trans (h _ _ h2)

theorem tg1 {n : Nat} {r : BRel n} {a b : Fin n} (h : r a b = true) : TransGen r.Holds a b :=
  .single h

theorem rtg_tg {α : Type _} {r : α → α → Prop} {a b c d : α} (h1 : ReflTransGen r a b)
    (h2 : r b c) (h3 : ReflTransGen r c d) : TransGen r a d :=
  (TransGen.tail' h1 h2).trans_left h3

/-- `po ∪ rf`. -/
def PRf (x : Exec) (a b : Fin x.n) : Prop := x.po a b = true ∨ x.rfR a b = true

/-- `po ∪ rfe`. -/
def PR (x : Exec) (a b : Fin x.n) : Prop := x.po a b = true ∨ x.rfe a b = true

theorem po_rtg {a b : Fin x.n} (h : a = b ∨ x.po a b = true) : ReflTransGen (PRf x) a b := by
  rcases h with rfl | h
  · exact .refl
  · exact .single (.inl h)

theorem rfRmw_PRf (hw : WfF x) {ro : Nat → Role} {c w : Fin x.n} (h : Rc11.RfRmwStar ro x c w) :
    ReflTransGen (PRf x) c w := by
  induction h with
  | refl => exact .refl
  | tail _ hst ih =>
    obtain ⟨d, hd1, hd2⟩ := BRel.seq_elim hst
    simp only [Rc11.rf, Rc11.rmw, Bool.and_eq_true] at hd1 hd2
    exact (ih.tail (.inr hd1.1)).tail (.inl (hw.rmwPo _ _ hd2.1))

theorem sw_PRf (hw : WfF x) {ro : Nat → Role} {a b : Fin x.n} (h : Rc11.Sw ro x a b) :
    TransGen (PRf x) a b := by
  obtain ⟨-, a', w, r, ha', ⟨-, c, hc, -, -, hcw⟩, hrf, -, -, hb, -⟩ := h
  have h1 : ReflTransGen (PRf x) a a' := by
    rcases ha' with rfl | ⟨-, h⟩
    · exact .refl
    · exact .single (.inl h)
  have h2 : ReflTransGen (PRf x) a' c := by
    rcases hc with rfl | ⟨h, -⟩
    · exact .refl
    · exact .single (.inl h)
  have h3 : ReflTransGen (PRf x) c w := rfRmw_PRf hw hcw
  have h4 : PRf x w r := by
    simp only [Rc11.rf, Bool.and_eq_true] at hrf
    exact .inr hrf.1
  have h5 : ReflTransGen (PRf x) r b := by
    rcases hb with rfl | ⟨h, -⟩
    · exact .refl
    · exact .single (.inl h)
  exact rtg_tg (h1.trans (h2.trans h3)) h4 h5

/-- **Happens-before is a `po ∪ rfe` path** (on TSO, internal `rf` is `po`). -/
theorem hb_PR (hw : WfF x) (hu : BRel.Acyclic x.uniproc) {ro : Nat → Role} {a b : Fin x.n}
    (h : Rc11.Hb ro x a b) : TransGen (PR x) a b := by
  have h1 : TransGen (PRf x) a b := by
    refine tg_flat (fun a b hab => ?_) h
    rcases hab with hab | hab
    · exact .single (.inl hab)
    · exact sw_PRf hw hab
  refine tg_flat (fun a b hab => .single ?_) h1
  rcases hab with hab | hab
  · exact .inl hab
  · exact rf_po_or_rfe hu hab

theorem PR_thinAir {a b : Fin x.n} (h : TransGen (PR x) a b) : TransGen x.thinAir.Holds a b := by
  refine tg_flat (fun a b hab => .single ?_) h
  simp only [BRel.Holds, Exec.thinAir, BRel.union_iff]
  rcases hab with hab | hab
  · exact .inl hab
  · exact .inr (BRel.inter_iff.mp hab).1

/-- **The shape of a `po ∪ rfe` path**: a `po` edge, or `po` to a write `w₂` (or `w₂` is the
start), a `ghb` path from `w₂` to a read `c`, and `po` from `c` (or `c` is the end). -/
theorem hb_claim {a b : Fin x.n} (h : TransGen (PR x) a b) :
    x.po a b = true ∨ ∃ w₂ c, (x.ev w₂).isW = true ∧ (w₂ = a ∨ x.po a w₂ = true) ∧
      TransGen x.ghb.Holds w₂ c ∧ (x.ev c).isR = true ∧ (c = b ∨ x.po c b = true) := by
  induction h with
  | single hab =>
    rcases hab with hab | hab
    · exact .inl hab
    · have hk := rf_kinds (BRel.inter_iff.mp hab).1
      exact .inr ⟨a, _, hk.1, .inl rfl, .single (rfe_ghb hab), hk.2, .inl rfl⟩
  | @tail d e _ hde ih =>
    rcases hde with hde | hde
    · rcases ih with ih | ⟨w₂, c, hw, ha, hg, hc, hcd⟩
      · exact .inl (x.po_trans ih hde)
      · refine .inr ⟨w₂, c, hw, ha, hg, hc, .inr ?_⟩
        rcases hcd with rfl | hcd
        · exact hde
        · exact x.po_trans hcd hde
    · have hk := rf_kinds (BRel.inter_iff.mp hde).1
      rcases ih with ih | ⟨w₂, c, hw, ha, hg, hc, hcd⟩
      · exact .inr ⟨d, e, hk.1, .inr ih, .single (rfe_ghb hde), hk.2, .inl rfl⟩
      · rcases hcd with rfl | hcd
        · exact absurd hk.1 (fun h => not_R_and_W hc h)
        · refine .inr ⟨w₂, e, hw, ha, ?_, hk.2, .inl rfl⟩
          exact (hg.tail (po_ghb_R hcd hc (isM_of_isW hk.1))).tail (rfe_ghb hde)

/-- A `po ∪ rfe` path to a memory unit: a `po` edge, or `po` to a write followed by `ghb⁺`. -/
theorem hb_mem {a b : Fin x.n} (h : TransGen (PR x) a b) (hb : (x.ev b).isM = true) :
    x.po a b = true ∨ ∃ w₂, (x.ev w₂).isW = true ∧ (w₂ = a ∨ x.po a w₂ = true) ∧
      TransGen x.ghb.Holds w₂ b := by
  rcases hb_claim h with h | ⟨w₂, c, hw, ha, hg, hc, hcb⟩
  · exact .inl h
  · refine .inr ⟨w₂, hw, ha, ?_⟩
    rcases hcb with rfl | hcb
    · exact hg
    · exact hg.tail (po_ghb_R hcb hc hb)

end Hb

/-! ## Cells and extended coherence -/

section Eco
variable {x : Exec}

theorem cell_of_com (hc : Cells x) {a b : Fin x.n} (h : x.com a b = true) :
    (x.ev a).addr = (x.ev b).addr ∧ (x.ev a).size = (x.ev b).size := by
  obtain ⟨y, ha, hb⟩ := com_share h
  exact hc a b (com_kinds h).1 (com_kinds h).2 y ha hb

theorem covers_cell {e f : Ev} (ha : e.addr = f.addr) (hs : e.size = f.size) {y : Nat}
    (h : e.covers y = true) : f.covers y = true := by
  rw [covers_iff] at h ⊢; omega

/-- Two distinct writes of a byte are `co`-ordered. -/
theorem co_total (hw : WfF x) {w f : Fin x.n} (hwW : (x.ev w).isW = true)
    (hfW : (x.ev f).isW = true) {y : Nat} (hyw : (x.ev w).covers y = true)
    (hyf : (x.ev f).covers y = true) (hne : w ≠ f) : x.coR w f = true ∨ x.coR f w = true := by
  have ht : y ∈ x.touched := by
    simp only [Exec.touched, List.mem_flatMap, List.mem_filter]
    exact ⟨x.ev w, ⟨List.getElem_mem _, isM_of_isW hwW⟩, mem_of_covers hyw⟩
  have h1 := hw.coAll y ht w hwW hyw
  have h2 := hw.coAll y ht f hfW hyf
  have hne' : w.val ≠ f.val := fun h => hne (Fin.ext h)
  rcases before_total h1 h2 hne' with h | h
  · left
    simp only [Exec.coR, hwW, hfW, Bool.true_and, List.any_eq_true, Bool.and_eq_true]
    exact ⟨y, mem_of_covers hyw, hyf, h⟩
  · right
    simp only [Exec.coR, hwW, hfW, Bool.true_and, List.any_eq_true, Bool.and_eq_true]
    exact ⟨y, mem_of_covers hyf, hyw, h⟩

/-- **`rf ; fr ⊆ co`** in a cell, under uniproc. -/
theorem rf_fr_co (hw : WfF x) (hc : Cells x) (hu : BRel.Acyclic x.uniproc) {w e f : Fin x.n}
    (h1 : x.rfR w e = true) (h2 : x.frR e f = true) : x.coR w f = true := by
  obtain ⟨y, hye, hyf⟩ := com_share (fr_com h2)
  have hwe := cell_of_com hc (rf_com h1)
  have hyw : (x.ev w).covers y = true := covers_cell hwe.1.symm hwe.2.symm hye
  have hwW := (rf_kinds h1).1
  have hfW := (fr_kinds h2).2
  by_cases hne : w = f
  · subst hne
    exact absurd (TransGen.tail (tg1 (com_uni (rf_com h1))) (com_uni (fr_com h2)))
      (hu w)
  · rcases co_total hw hwW hfW hyw hyf hne with h | h
    · exact h
    · exfalso
      exact hu f (((tg1 (com_uni (co_com h))).tail (com_uni (rf_com h1))).tail
        (com_uni (fr_com h2)))

/-- The raw edges of `eco`. -/
def EcoE (x : Exec) (a b : Fin x.n) : Prop :=
  x.rfR a b = true ∨ x.coR a b = true ∨ x.frR a b = true

theorem ecoE_com {a b : Fin x.n} (h : EcoE x a b) : x.com a b = true := by
  rcases h with h | h | h
  · exact rf_com h
  · exact co_com h
  · exact fr_com h

theorem eco_ecoE {ro : Nat → Role} {a b : Fin x.n} (h : Rc11.Eco ro x a b) :
    TransGen (EcoE x) a b := by
  refine tg_flat (fun a b hab => .single ?_) h
  simp only [BRel.Holds, BRel.union_iff, Rc11.rf, Rc11.mo, Rc11.fr, Bool.and_eq_true] at hab
  rcases hab with hab | hab | hab
  · exact .inl hab.1
  · exact .inr (.inl hab.1)
  · exact .inr (.inr hab.1)

/-- `eco` stays in one cell, and its end has a byte. -/
theorem ecoE_cell (hc : Cells x) {a b : Fin x.n} (h : TransGen (EcoE x) a b) :
    ((x.ev a).addr = (x.ev b).addr ∧ (x.ev a).size = (x.ev b).size) ∧
      (x.ev a).isM = true ∧ (x.ev b).isM = true ∧ ∃ y, (x.ev b).covers y = true := by
  induction h with
  | single hab =>
    obtain ⟨y, -, hy⟩ := com_share (ecoE_com hab)
    exact ⟨cell_of_com hc (ecoE_com hab), (com_kinds (ecoE_com hab)).1,
      (com_kinds (ecoE_com hab)).2, y, hy⟩
  | tail _ hde ih =>
    obtain ⟨⟨h1, h2⟩, ha, -, -⟩ := ih
    obtain ⟨y, -, hy⟩ := com_share (ecoE_com hde)
    have := cell_of_com hc (ecoE_com hde)
    exact ⟨⟨h1.trans this.1, h2.trans this.2⟩, ha, (com_kinds (ecoE_com hde)).2, y, hy⟩

theorem ecoE_uni {a b : Fin x.n} (h : TransGen (EcoE x) a b) : TransGen x.uniproc.Holds a b :=
  tg_flat (fun _ _ hab => .single (com_uni (ecoE_com hab))) h

/-- **`eco` is a `ghb` path up to a final `rf` edge.** -/
theorem eco_claim (hw : WfF x) (hc : Cells x) (hu : BRel.Acyclic x.uniproc) {b a : Fin x.n}
    (h : TransGen (EcoE x) b a) :
    TransGen x.ghb.Holds b a ∨ ∃ w, (w = b ∨ TransGen x.ghb.Holds b w) ∧ x.rfR w a = true := by
  induction h with
  | single hab =>
    rcases hab with hab | hab | hab
    · exact .inr ⟨b, .inl rfl, hab⟩
    · exact .inl (.single (co_ghb hab))
    · exact .inl (.single (fr_ghb hab))
  | @tail d e _ hde ih =>
    rcases hde with hde | hde | hde
    · rcases ih with ih | ⟨w, -, hw'⟩
      · exact .inr ⟨d, .inr ih, hde⟩
      · exact absurd (rf_kinds hde).1 (fun h => not_R_and_W (rf_kinds hw').2 h)
    · rcases ih with ih | ⟨w, -, hw'⟩
      · exact .inl (ih.tail (co_ghb hde))
      · exact absurd (co_kinds hde).1 (fun h => not_R_and_W (rf_kinds hw').2 h)
    · rcases ih with ih | ⟨w, hbw, hw'⟩
      · exact .inl (ih.tail (fr_ghb hde))
      · have hco := co_ghb (rf_fr_co hw hc hu hw' hde)
        rcases hbw with rfl | hbw
        · exact .inl (.single hco)
        · exact .inl (hbw.tail hco)

end Eco

/-! ## Coherence -/

section Coh
variable {x : Exec}

theorem coherence (hw : WfF x) (hc : Cells x) (ht : x.Tso) {ro : Nat → Role} {a b : Fin x.n}
    (hab : Rc11.Hb ro x a b) : a ≠ b ∧ ¬ Rc11.Eco ro x b a := by
  have hpr := hb_PR hw ht.2.1 hab
  refine ⟨fun h => ?_, fun heco => ?_⟩
  · subst h
    exact Exec.thinAir_of_tso x ht a (PR_thinAir hpr)
  have he := eco_ecoE heco
  obtain ⟨⟨hA, hS⟩, hbM, haM, y, hy⟩ := ecoE_cell hc he
  rcases hb_mem hpr hbM with hpo | ⟨w₂, hw₂, haw, hg⟩
  · -- a `po` edge in one cell: a uniproc cycle
    have hloc : x.loc a b = true := by
      simp only [Exec.loc, Bool.and_eq_true, List.any_eq_true]
      exact ⟨⟨haM, hbM⟩, y, mem_of_covers hy, covers_cell hA.symm hS.symm hy⟩
    exact ht.2.1 a ((tg1 (BRel.union_iff.mpr (.inl (BRel.inter_iff.mpr
      ⟨hpo, hloc⟩)))).trans (ecoE_uni he))
  · have hab' : TransGen x.ghb.Holds a b := by
      rcases haw with rfl | haw
      · exact hg
      · exact TransGen.head (po_ghb_W haw haM hw₂) hg
    rcases eco_claim hw hc ht.2.1 he with hba | ⟨w, hbw, hwa⟩
    · exact ht.2.2 a (hab'.trans hba)
    · have haR := (rf_kinds hwa).2
      have hpo : x.po a w₂ = true := by
        rcases haw with rfl | haw
        · exact absurd hw₂ (fun h => not_R_and_W haR h)
        · exact haw
      have hww : TransGen x.ghb.Holds w w₂ := by
        rcases rf_po_or_rfe ht.2.1 hwa with h | h
        · exact .single (po_ghb_W (x.po_trans h hpo) (isM_of_isW (rf_kinds hwa).1) hw₂)
        · exact (tg1 (rfe_ghb h)).tail (po_ghb_R hpo haR (isM_of_isW hw₂))
      have hwb := hww.trans hg
      rcases hbw with rfl | hbw
      · exact ht.2.2 w hwb
      · exact ht.2.2 b (hbw.trans hwb)

end Coh

/-! ## `ghb` with `po` edges at `mfence`s is acyclic -/

section G
variable {x : Exec}

/-- An `mfence` unit. -/
abbrev Mf (x : Exec) (a : Fin x.n) : Prop := (x.ev a).isFence .mfence = true

/-- `ghb`, and `po` edges with an `mfence` at either end. -/
def G (x : Exec) (a b : Fin x.n) : Prop :=
  x.ghb a b = true ∨ (x.po a b = true ∧ (Mf x a ∨ Mf x b))

theorem G_po (hw : WfF x) {a b : Fin x.n} (h : G x a b) (hm : Mf x a ∨ Mf x b) :
    x.po a b = true := by
  rcases h with h | h
  · refine x.fencerel_po (ghb_fence hw h ?_)
    rcases hm with hm | hm
    · exact .inl (not_isM_of_fence hm)
    · exact .inr (not_isM_of_fence hm)
  · exact h.1

/-- `po` through an `mfence` after the start, at or before the end. -/
def PF (x : Exec) (c d : Fin x.n) : Prop := ∃ f, Mf x f ∧ x.po c f = true ∧ (f = d ∨ x.po f d = true)

theorem PF_ghb {c d : Fin x.n} (h : PF x c d) (hd : ¬ Mf x d) : x.ghb c d = true := by
  obtain ⟨f, hf, h1, h2⟩ := h
  rcases h2 with rfl | h2
  · exact absurd hf hd
  · exact mfence_intro hf h1 h2

theorem PF_po {c d e : Fin x.n} (h : PF x c d) (hde : x.po d e = true) : PF x c e := by
  obtain ⟨f, hf, h1, h2⟩ := h
  refine ⟨f, hf, h1, .inr ?_⟩
  rcases h2 with rfl | h2
  · exact hde
  · exact x.po_trans h2 hde

theorem ghb_PF (hw : WfF x) {d e : Fin x.n} (h : x.ghb d e = true) (he : Mf x e) : PF x d e := by
  obtain ⟨f, hf, h1, h2⟩ := mfence_elim (ghb_fence hw h (.inr (not_isM_of_fence he)))
  exact ⟨f, hf, h1, .inr h2⟩

theorem G_claim (hw : WfF x) {a : Fin x.n} (ha : ¬ Mf x a) {d : Fin x.n} (h : TransGen (G x) a d) :
    (¬ Mf x d ∧ TransGen x.ghb.Holds a d) ∨
      ∃ c, ¬ Mf x c ∧ (c = a ∨ TransGen x.ghb.Holds a c) ∧ PF x c d := by
  -- one step from a non-`mfence` unit reached by `ghb⁺` (or the start)
  have step : ∀ c e, ¬ Mf x c → (c = a ∨ TransGen x.ghb.Holds a c) → G x c e →
      (¬ Mf x e ∧ TransGen x.ghb.Holds a e) ∨
        ∃ c', ¬ Mf x c' ∧ (c' = a ∨ TransGen x.ghb.Holds a c') ∧ PF x c' e := by
    intro c e hc hac hce
    by_cases he : Mf x e
    · refine .inr ⟨c, hc, hac, ?_⟩
      rcases hce with hce | hce
      · exact ghb_PF hw hce he
      · exact ⟨e, he, hce.1, .inl rfl⟩
    · rcases hce with hce | hce
      · refine .inl ⟨he, ?_⟩
        rcases hac with rfl | hac
        · exact .single hce
        · exact hac.tail hce
      · rcases hce.2 with h' | h'
        · exact absurd h' hc
        · exact absurd h' he
  induction h with
  | single hab => exact step a _ ha (.inl rfl) hab
  | @tail d e _ hde ih =>
    rcases ih with ⟨hd, hgd⟩ | ⟨c, hc, hac, hcd⟩
    · exact step d e hd (.inr hgd) hde
    · by_cases hd : Mf x d
      · exact .inr ⟨c, hc, hac, PF_po hcd (G_po hw hde (.inl hd))⟩
      · have hgd : TransGen x.ghb.Holds a d := by
          rcases hac with rfl | hac
          · exact .single (PF_ghb hcd hd)
          · exact hac.tail (PF_ghb hcd hd)
        exact step d e hd (.inr hgd) hde

theorem G_split (hw : WfF x) {a b : Fin x.n} (h : TransGen (G x) a b) :
    x.po a b = true ∨ ∃ m, ¬ Mf x m ∧ ReflTransGen (G x) a m ∧ ReflTransGen (G x) m b := by
  induction h with
  | @single b hab =>
    by_cases ha : Mf x a
    · by_cases hb : Mf x b
      · exact .inl (G_po hw hab (.inl ha))
      · exact .inr ⟨b, hb, .single hab, .refl⟩
    · exact .inr ⟨a, ha, .refl, .single hab⟩
  | @tail b c hab hbc ih =>
    rcases ih with ih | ⟨m, hm, h1, h2⟩
    · by_cases hb : Mf x b
      · by_cases hc : Mf x c
        · exact .inl (x.po_trans ih (G_po hw hbc (.inl hb)))
        · exact .inr ⟨c, hc, (hab.tail hbc).to_reflTransGen, .refl⟩
      · exact .inr ⟨b, hb, hab.to_reflTransGen, .single hbc⟩
    · exact .inr ⟨m, hm, h1, h2.tail hbc⟩

/-- **`G` is acyclic** when `ghb` is. -/
theorem G_acyclic (hw : WfF x) (hg : BRel.Acyclic x.ghb) (a : Fin x.n) :
    ¬ TransGen (G x) a a := by
  intro h
  rcases G_split hw h with hpo | ⟨m, hm, h1, h2⟩
  · simp [x.po_irrefl] at hpo
  · have hmm : TransGen (G x) m m := (TransGen.trans_left (TransGen.trans_right h2 h) h1)
    rcases G_claim hw hm hmm with ⟨-, hc⟩ | ⟨c, -, hc, hcm⟩
    · exact hg m hc
    · have := PF_ghb hcm hm
      rcases hc with rfl | hc
      · exact hg c (.single this)
      · exact hg m (hc.tail this)

theorem ghb_G {a b : Fin x.n} (h : TransGen x.ghb.Holds a b) : TransGen (G x) a b :=
  tg_flat (fun _ _ hab => .single (.inl hab)) h

end G

/-! ## SC -/

section Sc
variable {x : Exec}

/-- A memory unit or an `mfence`. -/
def S (x : Exec) (a : Fin x.n) : Prop := (x.ev a).isM = true ∨ Mf x a

theorem po_G_R {a b : Fin x.n} (h : x.po a b = true) (ha : (x.ev a).isR = true) (hb : S x b) :
    G x a b := by
  rcases hb with hb | hb
  · exact .inl (po_ghb_R h ha hb)
  · exact .inr ⟨h, .inr hb⟩

theorem po_G_W {a b : Fin x.n} (h : x.po a b = true) (ha : S x a) (hb : (x.ev b).isW = true) :
    G x a b := by
  rcases ha with ha | ha
  · exact .inl (po_ghb_W h ha hb)
  · exact .inr ⟨h, .inl ha⟩

theorem po_G_strong {a b : Fin x.n} (h : x.po a b = true) (ha : S x a) (hb : S x b)
    (hs : (Mf x a ∨ (x.ev a).isA = true) ∨ (Mf x b ∨ (x.ev b).isA = true)) : G x a b := by
  by_cases hma : Mf x a
  · exact .inr ⟨h, .inl hma⟩
  by_cases hmb : Mf x b
  · exact .inr ⟨h, .inr hmb⟩
  have ha' : (x.ev a).isM = true := ha.resolve_right hma
  have hb' : (x.ev b).isM = true := hb.resolve_right hmb
  refine .inl (po_ghb_A h ha' hb' ?_)
  rcases hs with (h1 | h1) | (h1 | h1)
  · exact absurd h1 hma
  · exact .inl h1
  · exact absurd h1 hmb
  · exact .inr h1

/-- A `po ∪ rfe` path between memory units or `mfence`s: a `po` edge or a `G` path. -/
theorem hb_G {a b : Fin x.n} (h : TransGen (PR x) a b) (ha : S x a) (hb : S x b) :
    x.po a b = true ∨ TransGen (G x) a b := by
  rcases hb_claim h with h | ⟨w₂, c, hw, haw, hg, hc, hcb⟩
  · exact .inl h
  · refine .inr ?_
    have h1 : TransGen (G x) w₂ b := by
      rcases hcb with rfl | hcb
      · exact ghb_G hg
      · exact (ghb_G hg).tail (po_G_R hcb hc hb)
    rcases haw with rfl | haw
    · exact h1
    · exact TransGen.head (po_G_W haw ha hw) h1

/-- `po` or a `po ∪ rfe` path. -/
def PH (x : Exec) (a b : Fin x.n) : Prop := x.po a b = true ∨ TransGen (PR x) a b

theorem PH_tg {a b : Fin x.n} (h : PH x a b) : TransGen (PR x) a b := by
  rcases h with h | h
  · exact .single (.inl h)
  · exact h

theorem PH_trans {a b c : Fin x.n} (h1 : PH x a b) (h2 : PH x b c) : PH x a c := by
  rcases h1 with h1 | h1
  · rcases h2 with h2 | h2
    · exact .inl (x.po_trans h1 h2)
    · exact .inr (TransGen.head (.inl h1) h2)
  · exact .inr (h1.trans (PH_tg h2))

theorem role_sc_of_isF {r : Role} (h : r.isF = true) : r.sc = true := by
  cases r <;> simp_all [Role.isF, Role.sc]

variable {ro : Nat → Role}

theorem sc_S (hm : MapRoles ro x) {a : Fin x.n} (h : (ro a.val).sc = true) : S x a :=
  ((hm a).1 h).1

theorem F_S (hm : MapRoles ro x) {a : Fin x.n} (h : (ro a.val).isF = true) : S x a :=
  sc_S hm (role_sc_of_isF h)

theorem F_strong (hm : MapRoles ro x) {a : Fin x.n} (h : (ro a.val).isF = true) :
    Mf x a ∨ (x.ev a).isA = true := (hm a).2 h

/-- `po` between SC events is a `G` edge (an SC write is locked). -/
theorem po_G_sc (hm : MapRoles ro x) {a b : Fin x.n} (h : x.po a b = true)
    (ha : (ro a.val).sc = true) (hb : (ro b.val).sc = true) : G x a b := by
  have hSa := sc_S hm ha
  have hSb := sc_S hm hb
  by_cases hma : Mf x a
  · exact .inr ⟨h, .inl hma⟩
  have haM : (x.ev a).isM = true := hSa.resolve_right hma
  have haM' := haM
  simp only [Ev.isM, Bool.or_eq_true] at haM'
  rcases haM' with hR | hW
  · exact po_G_R h hR hSb
  · have hl := ((hm a).1 ha).2 hW
    exact po_G_strong h hSa hSb (.inl (.inr (by simp [Ev.isA, hl, haM])))

theorem PH_G (hm : MapRoles ro x) {a b : Fin x.n} (h : PH x a b) (ha : (ro a.val).sc = true)
    (hb : (ro b.val).sc = true) : TransGen (G x) a b := by
  rcases hb_G (PH_tg h) (sc_S hm ha) (sc_S hm hb) with h | h
  · exact .single (po_G_sc hm h ha hb)
  · exact h

/-- From an SC fence along happens-before to a memory unit. -/
theorem F_hb_G (hm : MapRoles ro x) {a b : Fin x.n} (h : TransGen (PR x) a b)
    (ha : (ro a.val).isF = true) (hb : (x.ev b).isM = true) : TransGen (G x) a b := by
  rcases hb_G h (F_S hm ha) (.inl hb) with h | h
  · exact .single (po_G_strong h (F_S hm ha) (.inl hb) (.inl (F_strong hm ha)))
  · exact h

/-- From a memory unit along happens-before to an SC fence. -/
theorem hb_F_G (hm : MapRoles ro x) {a b : Fin x.n} (h : TransGen (PR x) a b)
    (ha : (x.ev a).isM = true) (hb : (ro b.val).isF = true) : TransGen (G x) a b := by
  rcases hb_G h (.inl ha) (F_S hm hb) with h | h
  · exact .single (po_G_strong h (.inl ha) (F_S hm hb) (.inr (F_strong hm hb)))
  · exact h

theorem mo_kinds {a b : Fin x.n} (h : Rc11.mo ro x a b = true) :
    x.coR a b = true := by
  simp only [Rc11.mo, Bool.and_eq_true] at h
  exact h.1

theorem fr_raw {a b : Fin x.n} (h : Rc11.fr ro x a b = true) : x.frR a b = true := by
  simp only [Rc11.fr, Bool.and_eq_true] at h
  exact h.1

theorem psc_G (hw : WfF x) (hc : Cells x) (ht : x.Tso) (hm : MapRoles ro x) {a b : Fin x.n}
    (h : Rc11.Psc ro x a b) : TransGen (G x) a b := by
  have hu := ht.2.1
  rcases h with ⟨a', b', hpre, hscb, hsuf⟩ | ⟨haF, hbF, hF⟩
  · have hasc : (ro a.val).sc = true := by
      rcases hpre with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact role_sc_of_isF h
    have hbsc : (ro b.val).sc = true := by
      rcases hsuf with ⟨h, -⟩ | ⟨h, -⟩
      · exact h
      · exact role_sc_of_isF h
    -- the prefix and suffix as `PH` or equality
    have hpre' : a' = a ∨ ((ro a.val).isF = true ∧ TransGen (PR x) a a') := by
      rcases hpre with ⟨-, rfl⟩ | ⟨hF, h | h⟩
      · exact .inl rfl
      · exact .inl h
      · exact .inr ⟨hF, hb_PR hw hu h⟩
    have hsuf' : b' = b ∨ ((ro b.val).isF = true ∧ TransGen (PR x) b' b) := by
      rcases hsuf with ⟨-, rfl⟩ | ⟨hF, h | h⟩
      · exact .inl rfl
      · exact .inl h
      · exact .inr ⟨hF, hb_PR hw hu h⟩
    have viaPH : PH x a' b' → TransGen (G x) a b := by
      intro hab'
      have h1 : PH x a b' := by
        rcases hpre' with rfl | ⟨-, h⟩
        · exact hab'
        · exact PH_trans (.inr h) hab'
      have h2 : PH x a b := by
        rcases hsuf' with rfl | ⟨-, h⟩
        · exact h1
        · exact PH_trans h1 (.inr h)
      exact PH_G hm h2 hasc hbsc
    have viaGhb : x.ghb a' b' = true → (x.ev a').isM = true → (x.ev b').isM = true →
        TransGen (G x) a b := by
      intro hg ha'M hb'M
      have h1 : TransGen (G x) a b' := by
        rcases hpre' with rfl | ⟨hF, h⟩
        · exact .single (.inl hg)
        · exact (F_hb_G hm h hF ha'M).tail (.inl hg)
      rcases hsuf' with rfl | ⟨hF, h⟩
      · exact h1
      · exact h1.trans (hb_F_G hm h hb'M hF)
    rcases hscb with h | ⟨c, d, h1, -, h2, h3, -⟩ | ⟨h, -⟩ | h | h
    · exact viaPH (.inl h)
    · exact viaPH (PH_trans (PH_trans (.inl h1) (.inr (hb_PR hw hu h2))) (.inl h3))
    · exact viaPH (.inr (hb_PR hw hu h))
    · have h' := mo_kinds h
      exact viaGhb (co_ghb h') (isM_of_isW (co_kinds h').1) (isM_of_isW (co_kinds h').2)
    · have h' := fr_raw h
      exact viaGhb (fr_ghb h') (isM_of_isR (fr_kinds h').1) (isM_of_isW (fr_kinds h').2)
  · rcases hF with h | ⟨c, d, h1, h2, h3⟩
    · exact PH_G hm (.inr (hb_PR hw hu h)) (role_sc_of_isF haF) (role_sc_of_isF hbF)
    · have he := eco_ecoE h2
      obtain ⟨-, hcM, hdM, -⟩ := ecoE_cell hc he
      have hac := F_hb_G hm (hb_PR hw hu h1) haF hcM
      have hdb' := hb_PR hw hu h3
      have hdb := hb_F_G hm hdb' hdM hbF
      rcases eco_claim hw hc hu he with hcd | ⟨w, hcw, hwd⟩
      · exact (hac.trans (ghb_G hcd)).trans hdb
      · have hwb : TransGen (G x) w b := by
          rcases rf_po_or_rfe hu hwd with hpo | hrfe
          · have hwM := isM_of_isW (rf_kinds hwd).1
            have hdR := (rf_kinds hwd).2
            rcases hb_claim hdb' with hpo' | ⟨w₂, c', hw₂, hdw, hg, hc', hcb⟩
            · exact .single (po_G_strong (x.po_trans hpo hpo') (.inl hwM) (F_S hm hbF)
                (.inr (F_strong hm hbF)))
            · have hdw' : x.po d w₂ = true := by
                rcases hdw with rfl | hdw
                · exact absurd hw₂ (fun h => not_R_and_W hdR h)
                · exact hdw
              have h1 : TransGen (G x) w₂ b := by
                rcases hcb with rfl | hcb
                · exact ghb_G hg
                · exact (ghb_G hg).tail (po_G_R hcb hc' (F_S hm hbF))
              exact TransGen.head (.inl (po_ghb_W (x.po_trans hpo hdw') hwM hw₂)) h1
          · exact TransGen.head (.inl (rfe_ghb hrfe)) hdb
        rcases hcw with rfl | hcw
        · exact hac.trans hwb
        · exact (hac.trans (ghb_G hcw)).trans hwb

end Sc

/-! ## The theorem -/

/-- **The x86 mapping is correct for RC11, execution by execution**: a well-formed
TSO-consistent candidate with cells and mapping-respecting roles is RC11-consistent. -/
theorem tso_rc11 {x : Exec} {ro : Nat → Role} (hwf : x.Wf = true) (ht : x.Tso) (hc : Cells x)
    (hm : MapRoles ro x) : Rc11.Consistent ro x := by
  have hw := wfF hwf
  refine ⟨?_, ?_, ht.1, ?_, ?_⟩
  · intro a b h1 h2
    exact ht.2.1 a (TransGen.tail (tg1 (com_uni h1)) (com_uni h2))
  · intro a b h
    exact coherence hw hc ht h
  · intro a h
    have := tg_flat (fun a b hab => psc_G hw hc ht hm hab) h
    exact G_acyclic hw ht.2.2 a this
  · intro a h
    refine Exec.thinAir_of_tso x ht a (tg_flat (fun a b hab => .single ?_) h)
    simp only [BRel.Holds, Exec.thinAir, BRel.union_iff]
    rcases hab with hab | hab
    · exact .inl hab
    · simp only [Rc11.rf, Bool.and_eq_true] at hab
      exact .inr hab.1

end Silmaril.Proofs.X86.Concurrency.Cir.C11Map
