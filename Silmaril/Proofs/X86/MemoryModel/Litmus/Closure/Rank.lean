module

public import Silmaril.X86.MemoryModel.Litmus.Models.Defs
public import Mathlib.Data.Fintype.Card

/-!
# Domain closure: the rank argument over candidate executions

Proofs for `Silmaril/X86/MemoryModel/Litmus/Closure/Thms.lean`.

The lemmas `before_*`, `WfFacts`, `wfFacts`, `NoTwo`, `cell_eq`, `coR_of`, `rfR_of`, `frR_of`,
`co_uniform` and `rf_uniform` are **copied** from
`Silmaril/Proofs/X86/MemoryModel/Litmus/Models/Ax.lean`, whose header does not export them; only
the namespace differs.

The new result is `rank_lemma`: in a well-formed candidate with no two-cycle in `com`, one cell
per overlapping pair and acyclic `po ∪ rf` (no thin air), give each read unit the number of
read units before it in `(po ∪ rf)⁺` (its **rank**). If initial bytes lie in the level-0 value
set and a write unit's bytes lie in level `k + 1` whenever every read before it in program order
lies in level `k`, then every read unit's bytes lie in level `rank + 1`, and the rank is less
than the number of read units.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.MemoryModel.Litmus.Closure

open Silmaril.X86.MemoryModel.Litmus
open Silmaril.X86.MemoryModel.Axiomatic

/-! ## `before` -/

theorem before_mem {l : List Nat} {a b : Nat} (h : before l a b = true) : a ∈ l ∧ b ∈ l := by
  induction l with
  | nil => simp [before] at h
  | cons c l ih =>
    simp only [before] at h
    split at h
    · rename_i hc
      simp only [beq_iff_eq] at hc; subst hc
      exact ⟨by simp, List.mem_cons_of_mem _ (by simpa using h)⟩
    · obtain ⟨h1, h2⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩

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

/-- Two repetition-free lists with the same members and the same order are equal. -/
theorem eq_of_before : ∀ {l₁ l₂ : List Nat}, l₁.Nodup → l₂.Nodup → (∀ a, a ∈ l₁ ↔ a ∈ l₂) →
    (∀ a b, before l₁ a b = true → before l₂ a b = true) → l₁ = l₂
  | [], l₂, _, _, hm, _ => by
    cases l₂ with
    | nil => rfl
    | cons c _ => exact absurd ((hm c).mpr (by simp)) (by simp)
  | h :: t, l₂, hn₁, hn₂, hm, hb => by
    cases l₂ with
    | nil => exact absurd ((hm h).mp (by simp)) (by simp)
    | cons h' t' =>
      have hh : h' = h := by
        by_contra hne
        have h'mem : h' ∈ t := by
          have := (hm h').mpr (by simp)
          simpa [hne] using this
        have hb1 : before (h :: t) h h' = true := by simp [before, h'mem]
        have hb2 := hb _ _ hb1
        rw [before_cons_of_ne hne] at hb2
        exact (List.nodup_cons.mp hn₂).1 (before_mem hb2).2
      subst hh
      congr 1
      apply eq_of_before (List.nodup_cons.mp hn₁).2 (List.nodup_cons.mp hn₂).2
      · intro a
        by_cases ha : a = h'
        · subst ha
          simp only [(List.nodup_cons.mp hn₁).1, (List.nodup_cons.mp hn₂).1]
        · have := hm a; simpa [ha] using this
      · intro a b hab
        have ha : a ≠ h' := fun e => (List.nodup_cons.mp hn₁).1 (e ▸ (before_mem hab).1)
        have := hb a b (by rw [before_cons_of_ne (Ne.symm ha)]; exact hab)
        rwa [before_cons_of_ne (Ne.symm ha)] at this

theorem before_irrefl {l : List Nat} (hn : l.Nodup) (a : Nat) : before l a a = false := by
  induction l with
  | nil => rfl
  | cons c l ih =>
    by_cases hca : c = a
    · subst hca
      simp only [before, beq_self_eq_true, ite_true, List.contains_eq_mem, decide_eq_false_iff_not]
      exact (List.nodup_cons.mp hn).1
    · rw [before_cons_of_ne hca]; exact ih (List.nodup_cons.mp hn).2

/-! ## Facts from `Wf`, `cellsOk` and consistency -/

theorem evN_eq (x : Exec) (i : Nat) (h : i < x.n) : x.evN i = x.ev ⟨i, h⟩ := by
  simp [Exec.evN, Exec.ev, List.getD_eq_getElem?_getD, h]

theorem mem_bytes {e : Ev} {y : Nat} : y ∈ e.bytes ↔ e.addr ≤ y ∧ y < e.addr + e.size := by
  simp [Ev.bytes, List.mem_range'_1]

theorem covers_iff {e : Ev} {y : Nat} : e.covers y = true ↔ e.addr ≤ y ∧ y < e.addr + e.size := by
  simp [Ev.covers]

theorem mem_touched {x : Exec} {y : Nat} :
    y ∈ x.touched ↔ ∃ e ∈ x.evs, e.isM = true ∧ y ∈ e.bytes := by
  simp [Exec.touched, List.mem_flatMap, List.mem_filter, and_assoc]

/-- What `Wf` says about `rf` and `co`. -/
structure WfFacts (x : Exec) : Prop where
  rf : ∀ r : Fin x.n, (x.ev r).isR = true → ∀ y ∈ (x.ev r).bytes, ∀ w, x.rf r.val y = some w →
    ∃ h : w < x.n, (x.ev ⟨w, h⟩).isW = true ∧ (x.ev ⟨w, h⟩).covers y = true
  coNodup : ∀ y ∈ x.touched, (x.co y).Nodup
  coMem : ∀ y ∈ x.touched, ∀ w ∈ x.co y,
    ∃ h : w < x.n, (x.ev ⟨w, h⟩).isW = true ∧ (x.ev ⟨w, h⟩).covers y = true
  coAll : ∀ y ∈ x.touched, ∀ w : Fin x.n, (x.ev w).isW = true → (x.ev w).covers y = true →
    w.val ∈ x.co y
  pos : ∀ e ∈ x.evs, e.isM = true → 0 < e.size

theorem wfFacts {x : Exec} (h : x.Wf = true) : WfFacts x := by
  simp only [Exec.Wf, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, -⟩, -⟩, h5⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro r hr y hy w hw
    have := h1 r (List.mem_finRange r)
    simp only [hr, Bool.not_true, Bool.false_or, List.all_eq_true] at this
    have := this y hy
    rw [hw] at this
    simp only [Exec.valid, Bool.and_eq_true, decide_eq_true_eq] at this
    obtain ⟨⟨hv, hW⟩, hC⟩ := this
    exact ⟨hv, by rwa [← evN_eq], by rwa [← evN_eq]⟩
  · intro y hy
    have := h2 y hy
    simp only [decide_eq_true_eq] at this
    exact this.1.1
  · intro y hy w hw
    have := h2 y hy
    simp only [decide_eq_true_eq] at this
    have := this.1.2 w hw
    simp only [Exec.valid, decide_eq_true_eq] at this
    obtain ⟨⟨hv, hW⟩, hC⟩ := this
    exact ⟨hv, by rwa [← evN_eq], by rwa [← evN_eq]⟩
  · intro y hy w hW hC
    have := h2 y hy
    simp only [decide_eq_true_eq] at this
    have := this.2 w (List.mem_finRange w)
    simp only [hW, hC, Bool.and_self, Bool.not_true, Bool.false_or, List.contains_eq_mem,
      decide_eq_true_eq] at this
    exact this
  · intro e he hM
    have := h5 e he
    simp only [hM, ite_true, Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1.1.1

/-- No two-cycle in `com`. -/
def NoTwo (x : Exec) : Prop := ∀ a b : Fin x.n, x.com a b = true → x.com b a = true → False

theorem noTwo_of {x : Exec} {R : BRel x.n} (hR : BRel.Acyclic R)
    (hsub : ∀ a b, x.com a b = true → R a b = true) : NoTwo x := by
  intro a b h1 h2
  exact hR a (Relation.TransGen.tail (Relation.TransGen.single (hsub a b h1)) (hsub b a h2))

theorem noTwo_of_sc {x : Exec} (h : x.Sc) : NoTwo x :=
  noTwo_of h.2 fun a b hab => by
    simp only [Exec.scRel, BRel.union, Bool.or_eq_true]
    exact Or.inr (BRel.seq_of_left (x.sm_refl) hab)

theorem noTwo_of_tso {x : Exec} (h : x.Tso) : NoTwo x :=
  noTwo_of h.2.1 fun a b hab => by
    simp only [Exec.uniproc, BRel.union, Bool.or_eq_true]
    exact Or.inr (BRel.seq_of_left (x.sm_refl) hab)

theorem noTwo_of_xl {x : Exec} (h : x.Xl) : NoTwo x :=
  noTwo_of h.2.1 fun a b hab => by
    simp only [Exec.uniprocXl, BRel.union, Bool.or_eq_true]
    exact Or.inr (BRel.seq_of_left (fun c => by simp [Exec.smT]) hab)

/-- Two memory units that share a byte are in the same cell. -/
theorem cell_eq {x : Exec} (hc : cellsOk x.evs = true) {a b : Fin x.n} (ha : (x.ev a).isM = true)
    (hb : (x.ev b).isM = true) {y : Nat} (hya : (x.ev a).covers y = true)
    (hyb : (x.ev b).covers y = true) :
    (x.ev a).addr = (x.ev b).addr ∧ (x.ev a).size = (x.ev b).size := by
  unfold cellsOk at hc
  simp only [List.all_eq_true, List.mem_filter] at hc
  have hma : x.ev a ∈ x.evs := List.getElem_mem _
  have hmb : x.ev b ∈ x.evs := List.getElem_mem _
  have := hc (x.ev a) ⟨hma, ha⟩ (x.ev b) ⟨hmb, hb⟩
  rw [covers_iff] at hya hyb
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true',
    Bool.and_eq_false_iff, decide_eq_false_iff_not] at this
  omega

theorem isM_of_isW {e : Ev} (h : e.isW = true) : e.isM = true := by simp [Ev.isM, h]
theorem isM_of_isR {e : Ev} (h : e.isR = true) : e.isM = true := by simp [Ev.isM, h]

theorem covers_of_cell {e f : Ev} (ha : e.addr = f.addr) (hs : e.size = f.size) {y : Nat}
    (h : y ∈ f.bytes) : e.covers y = true := by
  rw [covers_iff]; rw [mem_bytes] at h; omega

theorem mem_bytes_of_covers {e : Ev} {y : Nat} (h : e.covers y = true) : y ∈ e.bytes := by
  rw [mem_bytes]; rwa [covers_iff] at h

/-! ## Uniformity of consistent candidates -/

theorem coR_of {x : Exec} {a b : Fin x.n} (ha : (x.ev a).isW = true) (hb : (x.ev b).isW = true)
    {y : Nat} (hya : (x.ev a).covers y = true) (hyb : (x.ev b).covers y = true)
    (h : before (x.co y) a.val b.val = true) : x.com a b = true := by
  simp only [Exec.com, BRel.union, Bool.or_eq_true]
  refine Or.inr (Or.inl ?_)
  simp only [Exec.coR, ha, hb, Bool.true_and, List.any_eq_true, Bool.and_eq_true]
  exact ⟨y, mem_bytes_of_covers hya, hyb, h⟩

theorem rfR_of {x : Exec} {w r : Fin x.n} (hw : (x.ev w).isW = true) (hr : (x.ev r).isR = true)
    {y : Nat} (hy : y ∈ (x.ev r).bytes) (hrf : x.rf r.val y = some w.val)
    (hc : (x.ev w).covers y = true) : x.com w r = true := by
  simp only [Exec.com, BRel.union, Bool.or_eq_true]
  refine Or.inl ?_
  simp only [Exec.rfR, hw, hr, Bool.true_and, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
  exact ⟨y, hy, hrf, hc⟩

theorem frR_of {x : Exec} {r w : Fin x.n} (hr : (x.ev r).isR = true) (hw : (x.ev w).isW = true)
    {y : Nat} (hy : y ∈ (x.ev r).bytes) (hc : (x.ev w).covers y = true)
    (hrf : match x.rf r.val y with
      | none => True
      | some v => before (x.co y) v w.val = true) : x.com r w = true := by
  simp only [Exec.com, BRel.union, Bool.or_eq_true]
  refine Or.inr (Or.inr ?_)
  simp only [Exec.frR, hr, hw, Bool.true_and, List.any_eq_true, Bool.and_eq_true]
  refine ⟨y, hy, hc, ?_⟩
  revert hrf
  cases x.rf r.val y <;> simp

/-- **All bytes of a cell have one coherence order.** -/
theorem co_uniform {x : Exec} (hw : WfFacts x) (hn : NoTwo x) (hc : cellsOk x.evs = true)
    {e : Fin x.n} (he : (x.ev e).isM = true) {y₁ y₂ : Nat} (h₁ : y₁ ∈ (x.ev e).bytes)
    (h₂ : y₂ ∈ (x.ev e).bytes) : x.co y₁ = x.co y₂ := by
  have ht₁ : y₁ ∈ x.touched := mem_touched.mpr ⟨_, List.getElem_mem _, he, h₁⟩
  have ht₂ : y₂ ∈ x.touched := mem_touched.mpr ⟨_, List.getElem_mem _, he, h₂⟩
  -- a write covering a byte of `e`'s cell covers every byte of it
  have hcov : ∀ (w : Fin x.n), (x.ev w).isW = true → ∀ {y y'}, y ∈ (x.ev e).bytes →
      y' ∈ (x.ev e).bytes → (x.ev w).covers y = true → (x.ev w).covers y' = true := by
    intro w hW y y' hy hy' hcw
    obtain ⟨ha, hs⟩ := cell_eq hc (isM_of_isW hW) he hcw (covers_of_cell rfl rfl hy)
    exact covers_of_cell ha hs hy'
  have hmem : ∀ {y y'}, y ∈ x.touched → y' ∈ x.touched → y ∈ (x.ev e).bytes →
      y' ∈ (x.ev e).bytes → ∀ w, w ∈ x.co y → w ∈ x.co y' := by
    intro y y' ht ht' hy hy' w hwm
    obtain ⟨hwn, hW, hC⟩ := hw.coMem y ht w hwm
    exact hw.coAll y' ht' ⟨w, hwn⟩ hW (hcov _ hW hy hy' hC)
  apply eq_of_before (hw.coNodup y₁ ht₁) (hw.coNodup y₂ ht₂)
    (fun w => ⟨hmem ht₁ ht₂ h₁ h₂ w, hmem ht₂ ht₁ h₂ h₁ w⟩)
  intro a b hab
  obtain ⟨ha1, hb1⟩ := before_mem hab
  obtain ⟨han, haW, haC⟩ := hw.coMem y₁ ht₁ a ha1
  obtain ⟨hbn, hbW, hbC⟩ := hw.coMem y₁ ht₁ b hb1
  have hne : a ≠ b := by
    rintro rfl; rw [before_irrefl (hw.coNodup y₁ ht₁)] at hab; cases hab
  rcases before_total (hmem ht₁ ht₂ h₁ h₂ a ha1) (hmem ht₁ ht₂ h₁ h₂ b hb1) hne with h | h
  · exact h
  · exfalso
    exact hn ⟨a, han⟩ ⟨b, hbn⟩ (coR_of haW hbW haC hbC hab)
      (coR_of hbW haW (hcov _ hbW h₁ h₂ hbC) (hcov _ haW h₁ h₂ haC) h)

/-- **A read unit takes all its bytes from one source.** -/
theorem rf_uniform {x : Exec} (hw : WfFacts x) (hn : NoTwo x) (hc : cellsOk x.evs = true)
    {r : Fin x.n} (hr : (x.ev r).isR = true) {y₁ y₂ : Nat} (h₁ : y₁ ∈ (x.ev r).bytes)
    (h₂ : y₂ ∈ (x.ev r).bytes) : x.rf r.val y₁ = x.rf r.val y₂ := by
  have hcov : ∀ (w : Fin x.n), (x.ev w).isW = true → ∀ {y y'}, y ∈ (x.ev r).bytes →
      y' ∈ (x.ev r).bytes → (x.ev w).covers y = true → (x.ev w).covers y' = true := by
    intro w hW y y' hy hy' hcw
    obtain ⟨ha, hs⟩ := cell_eq hc (isM_of_isW hW) (isM_of_isR hr) hcw (covers_of_cell rfl rfl hy)
    exact covers_of_cell ha hs hy'
  have ht₁ : y₁ ∈ x.touched := mem_touched.mpr ⟨_, List.getElem_mem _, isM_of_isR hr, h₁⟩
  cases e₁ : x.rf r.val y₁ with
  | none =>
    cases e₂ : x.rf r.val y₂ with
    | none => rfl
    | some w₂ =>
      exfalso
      obtain ⟨hn₂, hW₂, hC₂⟩ := hw.rf r hr y₂ h₂ w₂ e₂
      exact hn r ⟨w₂, hn₂⟩ (frR_of hr hW₂ h₁ (hcov _ hW₂ h₂ h₁ hC₂) (by rw [e₁]; trivial))
        (rfR_of hW₂ hr h₂ e₂ hC₂)
  | some w₁ =>
    obtain ⟨hn₁, hW₁, hC₁⟩ := hw.rf r hr y₁ h₁ w₁ e₁
    cases e₂ : x.rf r.val y₂ with
    | none =>
      exfalso
      exact hn r ⟨w₁, hn₁⟩ (frR_of hr hW₁ h₂ (hcov _ hW₁ h₁ h₂ hC₁) (by rw [e₂]; trivial))
        (rfR_of hW₁ hr h₁ e₁ hC₁)
    | some w₂ =>
      obtain ⟨hn₂, hW₂, hC₂⟩ := hw.rf r hr y₂ h₂ w₂ e₂
      by_cases hne : w₁ = w₂
      · rw [hne]
      exfalso
      have hm₁ := hw.coAll y₁ ht₁ ⟨w₁, hn₁⟩ hW₁ hC₁
      have hm₂ := hw.coAll y₁ ht₁ ⟨w₂, hn₂⟩ hW₂ (hcov _ hW₂ h₂ h₁ hC₂)
      rcases before_total hm₁ hm₂ hne with h | h
      · exact hn r ⟨w₂, hn₂⟩ (frR_of hr hW₂ h₁ (hcov _ hW₂ h₂ h₁ hC₂) (by rw [e₁]; exact h))
          (rfR_of hW₂ hr h₂ e₂ hC₂)
      · have hco := co_uniform hw hn hc (isM_of_isR hr) h₁ h₂
        rw [hco] at h
        exact hn r ⟨w₁, hn₁⟩ (frR_of hr hW₁ h₂ (hcov _ hW₁ h₁ h₂ hC₁) (by rw [e₂]; exact h))
          (rfR_of hW₁ hr h₁ e₁ hC₁)

/-! ## The rank argument (new in this module) -/

theorem V_le {V : Nat → List Byte → Prop} (hmono : ∀ k bs, V k bs → V (k + 1) bs) {a b : Nat}
    {bs : List Byte} (h : V a bs) (hab : a ≤ b) : V b bs := by
  induction hab with
  | refl => exact h
  | step _ ih => exact hmono _ _ ih

open Classical in
/-- The read units before `r` in `(po ∪ rf)⁺`. -/
noncomputable def anc (x : Exec) (r : Fin x.n) : Finset (Fin x.n) :=
  Finset.univ.filter fun r' => (x.ev r').isR = true ∧ Relation.TransGen x.thinAir.Holds r' r

/-- The read units. -/
def readUnits (x : Exec) : Finset (Fin x.n) :=
  ((List.finRange x.n).filter fun r => (x.ev r).isR).toFinset

theorem anc_card_lt {x : Exec} (hta : BRel.Acyclic x.thinAir) {r : Fin x.n}
    (hr : (x.ev r).isR = true) : (anc x r).card < (readUnits x).card := by
  classical
  apply Finset.card_lt_card
  refine ⟨?_, ?_⟩
  · intro r' h
    simp only [anc, Finset.mem_filter, Finset.mem_univ, true_and] at h
    simp [readUnits, h.1]
  · intro hsub
    have := hsub (show r ∈ readUnits x by simp [readUnits, hr])
    simp only [anc, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact hta r this.2

theorem anc_lt {x : Exec} (hta : BRel.Acyclic x.thinAir) {r' r : Fin x.n}
    (hr' : (x.ev r').isR = true) (h : Relation.TransGen x.thinAir.Holds r' r) :
    (anc x r').card < (anc x r).card := by
  classical
  apply Finset.card_lt_card
  refine ⟨?_, ?_⟩
  · intro z hz
    simp only [anc, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact ⟨hz.1, hz.2.trans h⟩
  · intro hsub
    have := hsub (show r' ∈ anc x r by simp [anc, hr', h])
    simp only [anc, Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact hta r' this.2

/-- **The rank lemma.** -/
theorem rank_lemma {x : Exec} (hwf : WfFacts x) (hn : NoTwo x) (hc : cellsOk x.evs = true)
    (hta : BRel.Acyclic x.thinAir) (init : Nat → Byte) (exps : Nat → List Byte)
    (hreads : ∀ r : Fin x.n, (x.ev r).isR = true → x.readBytes init r.val = exps r.val)
    (V : Nat → List Byte → Prop) (hmono : ∀ k bs, V k bs → V (k + 1) bs)
    (hinit : ∀ r : Fin x.n, (x.ev r).isR = true → V 0 ((x.ev r).bytes.map init))
    (hwrite : ∀ (k : Nat) (w : Fin x.n), k < (readUnits x).card → (x.ev w).isW = true →
      (∀ r : Fin x.n, (x.ev r).isR = true → x.po r w = true → V k (exps r.val)) →
      V (k + 1) ((x.ev w).bytes.map (x.ev w).byte)) :
    ∀ r : Fin x.n, (x.ev r).isR = true → V ((anc x r).card + 1) (exps r.val) := by
  suffices H : ∀ k, ∀ r : Fin x.n, (anc x r).card = k → (x.ev r).isR = true →
      V (k + 1) (exps r.val) from fun r hr => H _ r rfl hr
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro r hk hr
  have hpos := hwf.pos (x.ev r) (List.getElem_mem _) (isM_of_isR hr)
  have hy0 : (x.ev r).addr ∈ (x.ev r).bytes := mem_bytes.mpr ⟨le_refl _, by omega⟩
  have hu : ∀ y ∈ (x.ev r).bytes, x.rf r.val y = x.rf r.val (x.ev r).addr :=
    fun y hy => rf_uniform hwf hn hc hr hy hy0
  have hrb := hreads r hr
  unfold Exec.readBytes at hrb
  rw [evN_eq x r.val r.isLt] at hrb
  cases hs : x.rf r.val (x.ev r).addr with
  | none =>
    have e1 : (x.ev r).bytes.map (x.readByte init r.val) = (x.ev r).bytes.map init :=
      List.map_congr_left fun y hy => by simp [Exec.readByte, hu y hy, hs]
    rw [← hrb, e1]
    exact V_le hmono (hinit r hr) (by omega)
  | some w =>
    obtain ⟨hwn, hW, hC⟩ := hwf.rf r hr _ hy0 w hs
    obtain ⟨ha, hsz⟩ := cell_eq hc (isM_of_isW hW) (isM_of_isR hr) hC (covers_of_cell rfl rfl hy0)
    have hbytes : (x.ev r).bytes = (x.ev ⟨w, hwn⟩).bytes := by simp [Ev.bytes, ha, hsz]
    have e1 : (x.ev r).bytes.map (x.readByte init r.val) =
        (x.ev r).bytes.map (x.ev ⟨w, hwn⟩).byte :=
      List.map_congr_left fun y hy => by simp [Exec.readByte, hu y hy, hs, evN_eq x w hwn]
    have e2 : exps r.val = (x.ev ⟨w, hwn⟩).bytes.map (x.ev ⟨w, hwn⟩).byte := by
      rw [← hrb]
      show (x.ev r).bytes.map _ = _
      rw [e1, hbytes]
    rw [e2]
    refine hwrite k ⟨w, hwn⟩ (hk ▸ anc_card_lt hta hr) hW fun r' hr' hpo => ?_
    have hrf : x.rfR ⟨w, hwn⟩ r = true := by
      simp only [Exec.rfR, hW, hr, Bool.true_and, List.any_eq_true, Bool.and_eq_true, beq_iff_eq]
      exact ⟨_, hy0, hs, hC⟩
    have htg : Relation.TransGen x.thinAir.Holds r' r :=
      .tail (b := ⟨w, hwn⟩) (.single (by simp [BRel.Holds, Exec.thinAir, BRel.union, hpo]))
        (by simp [BRel.Holds, Exec.thinAir, BRel.union, hrf])
    have hlt := anc_lt hta hr' htg
    rw [hk] at hlt
    exact V_le hmono (ih _ hlt r' rfl hr') (by omega)

theorem readUnits_card_le (x : Exec) : (readUnits x).card ≤ (x.evs.filter Ev.isR).length := by
  refine (List.toFinset_card_le _).trans (le_of_eq ?_)
  have : (List.finRange x.n).map x.ev = x.evs := List.map_getElem_finRange x.evs
  rw [← this, List.filter_map, List.length_map]
  rfl

/-- **Every read unit lies in the level of the number of read units.** -/
theorem reads_in_level {x : Exec} (hwf : WfFacts x) (hn : NoTwo x) (hc : cellsOk x.evs = true)
    (hta : BRel.Acyclic x.thinAir) (init : Nat → Byte) (exps : Nat → List Byte)
    (hreads : ∀ r : Fin x.n, (x.ev r).isR = true → x.readBytes init r.val = exps r.val)
    (V : Nat → List Byte → Prop) (hmono : ∀ k bs, V k bs → V (k + 1) bs)
    (hinit : ∀ r : Fin x.n, (x.ev r).isR = true → V 0 ((x.ev r).bytes.map init))
    {K : Nat} (hK : (x.evs.filter Ev.isR).length ≤ K)
    (hwrite : ∀ (k : Nat) (w : Fin x.n), k < K → (x.ev w).isW = true →
      (∀ r : Fin x.n, (x.ev r).isR = true → x.po r w = true → V k (exps r.val)) →
      V (k + 1) ((x.ev w).bytes.map (x.ev w).byte)) :
    ∀ r : Fin x.n, (x.ev r).isR = true → V K (exps r.val) := fun r hr =>
  V_le hmono (rank_lemma hwf hn hc hta init exps hreads V hmono hinit
    (fun k w hk => hwrite k w (lt_of_lt_of_le hk ((readUnits_card_le x).trans hK))) r hr)
    (by have := anc_card_lt hta hr; have := readUnits_card_le x; omega)

end Silmaril.Proofs.X86.MemoryModel.Litmus.Closure
