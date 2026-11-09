module

public import Silmaril.Proofs.X86.MemoryModel.Litmus.Models.Op

/-!
# Litmus models: the axiomatic candidate enumerator is exact

`axJudge_spec`: when `Test.axJudge` succeeds, the outcomes of its judged candidates consistent
under SC, TSO or XL are exactly the outcomes of `AxReach` under that model. Soundness is by
construction. Completeness: every well-formed candidate `x` over the units of a choice of traces
whose reads return the traces' bytes and which is consistent under any of the three models has
no two-cycle in `com` (each model's acyclic relation contains `com`), and then

* `co_uniform`: all bytes of a cell have the same coherence order (two writes ordered
  differently on two bytes are `co`-related both ways);
* `rf_uniform`: a read unit takes all its bytes from one source (otherwise `rf` and `fr` relate
  it with a write both ways);

so `x` agrees, on every argument the models, `Wf`, `ReadsOk` and the final state look at, with
the enumerated candidate that has its `rf` per read unit and its `co` per cell (`agree_*`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.MemoryModel.Litmus

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

/-! ## Agreement -/

theorem all_congr' {γ : Type} {l : List γ} {f g : γ → Bool} (h : ∀ a ∈ l, f a = g a) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.all_cons]
    rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]

theorem any_congr' {γ : Type} {l : List γ} {f g : γ → Bool} (h : ∀ a ∈ l, f a = g a) :
    l.any f = l.any g := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.any_cons]
    rw [h a (by simp), ih (fun b hb => h b (by simp [hb]))]

/-- Two executions over the same units and pairs that agree on every `rf` and `co` argument the
models look at. -/
structure Agree (x x' : Exec) : Prop where
  evs : x.evs = x'.evs
  rmw : x.rmw = x'.rmw
  rf : ∀ r y, (x.evN r).isR = true → y ∈ (x.evN r).bytes → x.rf r y = x'.rf r y
  co : ∀ y ∈ x.touched, x.co y = x'.co y

section Congr

variable {evs : List Ev} {rmw : List (Nat × Nat)} {rf rf' : Nat → Nat → Option Nat}
  {co co' : Nat → List Nat}

theorem agree_rels (h : Agree ⟨evs, rf, co, rmw⟩ ⟨evs, rf', co', rmw⟩) :
    Exec.rfR ⟨evs, rf, co, rmw⟩ = Exec.rfR ⟨evs, rf', co', rmw⟩ ∧
      Exec.coR ⟨evs, rf, co, rmw⟩ = Exec.coR ⟨evs, rf', co', rmw⟩ ∧
      Exec.frR ⟨evs, rf, co, rmw⟩ = Exec.frR ⟨evs, rf', co', rmw⟩ := by
  have hrf : ∀ (r : Fin evs.length) y, (evs[r]).isR = true → y ∈ (evs[r]).bytes →
      rf r.val y = rf' r.val y := by
    intro r y hr hy
    have := h.rf r.val y
    rw [evN_eq ⟨evs, rf, co, rmw⟩ r.val r.isLt] at this
    exact this hr hy
  have hco : ∀ (a : Fin evs.length) y, (evs[a]).isM = true → y ∈ (evs[a]).bytes →
      co y = co' y := by
    intro a y ha hy
    exact h.co y (mem_touched.mpr ⟨_, List.getElem_mem _, ha, hy⟩)
  refine ⟨?_, ?_, ?_⟩
  · funext w r
    simp only [Exec.rfR, Exec.ev]
    cases hr : (evs[r]).isR
    · simp
    · congr 1
      exact any_congr' fun y hy => by rw [hrf r y hr hy]
  · funext a b
    simp only [Exec.coR, Exec.ev]
    cases ha : (evs[a]).isW
    · simp
    · congr 1
      exact any_congr' fun y hy => by rw [hco a y (isM_of_isW ha) hy]
  · funext r w
    simp only [Exec.frR, Exec.ev]
    cases hr : (evs[r]).isR
    · simp
    · congr 1
      exact any_congr' fun y hy => by rw [hrf r y hr hy, hco r y (isM_of_isR hr) hy]

theorem agree_sc (h : Agree ⟨evs, rf, co, rmw⟩ ⟨evs, rf', co', rmw⟩) :
    Exec.Sc ⟨evs, rf, co, rmw⟩ ↔ Exec.Sc ⟨evs, rf', co', rmw⟩ := by
  obtain ⟨h1, h2, h3⟩ := agree_rels h
  simp only [Exec.Sc, Exec.atomicB, Exec.scRel, Exec.com, Exec.fre, Exec.coe, h1, h2, h3]
  exact Iff.rfl

theorem agree_tso (h : Agree ⟨evs, rf, co, rmw⟩ ⟨evs, rf', co', rmw⟩) :
    Exec.Tso ⟨evs, rf, co, rmw⟩ ↔ Exec.Tso ⟨evs, rf', co', rmw⟩ := by
  obtain ⟨h1, h2, h3⟩ := agree_rels h
  simp only [Exec.Tso, Exec.atomicB, Exec.uniproc, Exec.ghb, Exec.comGhb, Exec.com, Exec.fre,
    Exec.coe, Exec.rfe, h1, h2, h3]
  exact Iff.rfl

theorem agree_xl (h : Agree ⟨evs, rf, co, rmw⟩ ⟨evs, rf', co', rmw⟩) :
    Exec.Xl ⟨evs, rf, co, rmw⟩ ↔ Exec.Xl ⟨evs, rf', co', rmw⟩ := by
  obtain ⟨h1, h2, h3⟩ := agree_rels h
  simp only [Exec.Xl, Exec.atomicB, Exec.uniprocXl, Exec.thinAir, Exec.ghbXl, Exec.comGhbXl,
    Exec.com, Exec.fre, Exec.coe, Exec.rfe, h1, h2, h3]
  exact Iff.rfl

theorem agree_wf (h : Agree ⟨evs, rf, co, rmw⟩ ⟨evs, rf', co', rmw⟩) :
    Exec.Wf ⟨evs, rf, co, rmw⟩ = Exec.Wf ⟨evs, rf', co', rmw⟩ := by
  unfold Exec.Wf
  congr 1
  congr 1
  congr 1
  congr 1
  · apply all_congr'
    intro r _
    cases hr : (Exec.ev ⟨evs, rf, co, rmw⟩ r).isR
    · have hr' : (Exec.ev ⟨evs, rf', co', rmw⟩ r).isR = false := hr
      rw [hr']; rfl
    · have hr' : (Exec.ev ⟨evs, rf', co', rmw⟩ r).isR = true := hr
      rw [hr']
      simp only [Bool.not_true, Bool.false_or]
      apply all_congr'
      intro y hy
      have := h.rf r.val y
      rw [evN_eq ⟨evs, rf, co, rmw⟩ r.val r.isLt] at this
      have e : rf r.val y = rf' r.val y := this hr hy
      rw [e]
      rfl
  · apply all_congr'
    intro y hy
    have e : Exec.co ⟨evs, rf, co, rmw⟩ y = Exec.co ⟨evs, rf', co', rmw⟩ y := h.co y hy
    rw [e]
    rfl

theorem agree_readsOk (t : Test) (exps : List (List Byte))
    (h : Agree ⟨evs, rf, co, rmw⟩ ⟨evs, rf', co', rmw⟩) :
    ReadsOk t ⟨evs, rf, co, rmw⟩ exps ↔ ReadsOk t ⟨evs, rf', co', rmw⟩ exps := by
  have : ∀ r, (Exec.evN ⟨evs, rf, co, rmw⟩ r).isR = true →
      Exec.readBytes ⟨evs, rf, co, rmw⟩ t.initB r = Exec.readBytes ⟨evs, rf', co', rmw⟩ t.initB r := by
    intro r hr
    simp only [Exec.readBytes]
    apply List.map_congr_left
    intro y hy
    have e : rf r y = rf' r y := h.rf r y hr hy
    simp only [Exec.readByte]
    rw [e]
    rfl
  simp only [ReadsOk]
  constructor
  · intro H r hr hR; rw [← this r hR]; exact H r hr hR
  · intro H r hr hR; rw [this r hR]; exact H r hr hR

theorem agree_final (t : Test) (trs : List XTrace)
    (h : Agree ⟨evs, rf, co, rmw⟩ ⟨evs, rf', co', rmw⟩) :
    finalAx t trs ⟨evs, rf, co, rmw⟩ = finalAx t trs ⟨evs, rf', co', rmw⟩ := by
  simp only [finalAx]
  congr 1
  funext y
  by_cases hw : writtenByte ⟨evs, rf, co, rmw⟩ y = true
  · have hw' := hw
    simp only [writtenByte, List.any_eq_true, Bool.and_eq_true] at hw'
    obtain ⟨e, he, hW, hC⟩ := hw'
    have ht : y ∈ Exec.touched ⟨evs, rf, co, rmw⟩ :=
      mem_touched.mpr ⟨e, he, isM_of_isW hW, mem_bytes_of_covers hC⟩
    have hw2 : writtenByte ⟨evs, rf', co', rmw⟩ y = true := hw
    simp only [hw, hw2, ↓reduceIte]
    simp only [Exec.finalByte]
    have e : co y = co' y := h.co y ht
    rw [e]
    rfl
  · have hf : writtenByte ⟨evs, rf, co, rmw⟩ y = false := by simpa using hw
    have hf2 : writtenByte ⟨evs, rf', co', rmw⟩ y = false := hf
    simp only [hf, hf2, Bool.false_eq_true, ↓reduceIte]

end Congr

theorem agree_all {x x' : Exec} (h : Agree x x') :
    (x.Sc ↔ x'.Sc) ∧ (x.Tso ↔ x'.Tso) ∧ (x.Xl ↔ x'.Xl) ∧ x.Wf = x'.Wf ∧
      (∀ t exps, ReadsOk t x exps ↔ ReadsOk t x' exps) ∧
      ∀ t trs, finalAx t trs x = finalAx t trs x' := by
  obtain ⟨evs, rf, co, rmw⟩ := x
  obtain ⟨evs', rf', co', rmw'⟩ := x'
  have he : evs = evs' := h.evs
  have hr : rmw = rmw' := h.rmw
  subst he hr
  exact ⟨agree_sc h, agree_tso h, agree_xl h, agree_wf h, fun t exps => agree_readsOk t exps h,
    fun t trs => agree_final t trs h⟩

/-! ## The enumerated candidates -/

theorem getD_dummy (evs : List Ev) (i : Nat) (h : i < evs.length) : evs.getD i dummyEv = evs[i] := by
  simp [List.getD_eq_getElem?_getD, h]

theorem mem_idxs {evs : List Ev} {p : Ev → Bool} {i : Nat} :
    i ∈ idxs evs p ↔ ∃ h : i < evs.length, p evs[i] = true := by
  simp only [idxs, List.mem_filter, List.mem_range]
  constructor
  · rintro ⟨h, hp⟩; exact ⟨h, by rwa [getD_dummy _ _ h] at hp⟩
  · rintro ⟨h, hp⟩; exact ⟨h, by rwa [getD_dummy _ _ h]⟩

theorem idxs_nodup (evs : List Ev) (p : Ev → Bool) : (idxs evs p).Nodup :=
  List.nodup_range.filter _

theorem lookup_zip_map {γ : Type} (rs : List Nat) (f : Nat → γ) (r : Nat) (h : r ∈ rs) :
    (rs.zip (rs.map f)).lookup r = some (f r) := by
  induction rs with
  | nil => simp at h
  | cons a rs ih =>
    simp only [List.map_cons, List.zip_cons_cons, lookup_cons']
    by_cases hr : r = a
    · subst hr; simp
    · simp only [hr, ite_false]; exact ih (by simpa [hr] using h)

theorem mem_zip_map {γ δ : Type} {l : List γ} {g : γ → δ} {p : γ × δ} (h : p ∈ l.zip (l.map g)) :
    p.2 = g p.1 ∧ p.1 ∈ l := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · obtain ⟨h1, h2⟩ := ih h; exact ⟨h1, List.mem_cons_of_mem _ h2⟩

theorem mem_zip_map_of {γ δ : Type} {l : List γ} (g : γ → δ) {c : γ} (h : c ∈ l) :
    (c, g c) ∈ l.zip (l.map g) := by
  induction l with
  | nil => simp at h
  | cons a l ih =>
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at h ⊢
    rcases h with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (ih h)

theorem mem_candidates {t : Test} {evs : List Ev} {exps : List (List Byte)}
    {rmw : List (Nat × Nat)} {x : Exec} :
    x ∈ candidates t evs exps rmw ↔
      ∃ rfc ∈ seqL ((readsOf evs).map (rfChoices t evs exps)),
        ∃ coc ∈ seqL ((cellsOf evs).map fun c => arrangements (writesIn evs c)),
          x = mkExec evs rmw ((readsOf evs).zip rfc) ((cellsOf evs).zip coc) := by
  simp only [candidates, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨rfc, hr, coc, hc, rfl⟩; exact ⟨rfc, hr, coc, hc, rfl⟩
  · rintro ⟨rfc, hr, coc, hc, rfl⟩; exact ⟨rfc, hr, coc, hc, rfl⟩

theorem forall₂_map_same {γ δ : Type} {l : List γ} {f : γ → δ} {g : γ → List δ}
    (h : ∀ a ∈ l, f a ∈ g a) : List.Forall₂ (· ∈ ·) (l.map f) (l.map g) := by
  rw [List.forall₂_map_left_iff, List.forall₂_map_right_iff, List.forall₂_same]
  exact h

theorem mem_cellsOf {evs : List Ev} {c : Nat × Nat} :
    c ∈ cellsOf evs ↔ ∃ e ∈ evs, e.isM = true ∧ (e.addr, e.size) = c := by
  simp [cellsOf, mem_uniq, List.mem_map, List.mem_filter, and_assoc]

/-- **Every consistent candidate agrees with an enumerated one.** -/
theorem cand_complete (t : Test) {evs : List Ev} {exps : List (List Byte)}
    {rmw : List (Nat × Nat)} (hc : cellsOk evs = true) {x : Exec} (hx : x.evs = evs)
    (hrmw : x.rmw = rmw) (hwf : x.Wf = true) (hro : ReadsOk t x exps) (hn : NoTwo x) :
    ∃ x' ∈ candidates t evs exps rmw, Agree x x' := by
  subst hx hrmw
  have hw := wfFacts hwf
  have hpos : ∀ (i : Nat) (hi : i < x.n), (x.evs[i]).isM = true → x.evs[i].addr ∈ x.evs[i].bytes :=
    fun i hi hM => mem_bytes.mpr ⟨le_refl _, by have := hw.pos _ (List.getElem_mem hi) hM; omega⟩
  let f : Nat → Option Nat := fun r => x.rf r (x.evN r).addr
  let g : Nat × Nat → List Nat := fun c => x.co c.1
  refine ⟨mkExec x.evs x.rmw ((readsOf x.evs).zip ((readsOf x.evs).map f))
    ((cellsOf x.evs).zip ((cellsOf x.evs).map g)), ?_, ?_⟩
  · refine mem_candidates.mpr ⟨_, ?_, _, ?_, rfl⟩
    · rw [mem_seqL]
      apply forall₂_map_same
      intro r hr
      obtain ⟨hrn, hR⟩ := mem_idxs.mp hr
      have hRF : (x.ev ⟨r, hrn⟩).isR = true := hR
      have hNr : x.evN r = x.evs[r] := evN_eq x r hrn
      have ha0 := hpos r hrn (isM_of_isR hR)
      unfold rfChoices
      rw [List.mem_filter, getD_dummy _ _ hrn]
      constructor
      · simp only [f, hNr]
        cases hf : x.rf r x.evs[r].addr with
        | none => exact List.mem_cons_self
        | some w =>
          obtain ⟨hwn, hW, hC⟩ := hw.rf ⟨r, hrn⟩ hRF _ ha0 w hf
          obtain ⟨ha, hs⟩ := cell_eq hc (isM_of_isW hW) (isM_of_isR hRF) hC
            (covers_of_cell rfl rfl ha0)
          refine List.mem_cons_of_mem _ (List.mem_map.mpr ⟨w, mem_idxs.mpr ⟨hwn, ?_⟩, rfl⟩)
          simp only [Bool.and_eq_true, beq_iff_eq]
          exact ⟨⟨hW, ha⟩, hs⟩
      · rw [beq_iff_eq, ← hro r hrn (by rw [hNr]; exact hR)]
        simp only [srcBytes, Exec.readBytes, getD_dummy _ _ hrn, hNr]
        apply List.map_congr_left
        intro y hy
        simp only [f, hNr, Exec.readByte]
        have he : x.rf r x.evs[r].addr = x.rf r y := rf_uniform hw hn hc hRF ha0 hy
        rw [he]
        cases x.rf r y <;> rfl
    · rw [mem_seqL]
      apply forall₂_map_same
      intro c hc'
      obtain ⟨e, he, hM, rfl⟩ := mem_cellsOf.mp hc'
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
      have hMF : (x.ev ⟨i, hi⟩).isM = true := hM
      have ha0 := hpos i hi hM
      have ht : x.evs[i].addr ∈ x.touched := mem_touched.mpr ⟨_, he, hM, ha0⟩
      have hmemco : ∀ w, w ∈ x.co x.evs[i].addr ↔ w ∈ writesIn x.evs (x.evs[i].addr, x.evs[i].size) := by
        intro w
        constructor
        · intro hwm
          obtain ⟨hwn, hW, hC⟩ := hw.coMem _ ht w hwm
          obtain ⟨ha, hs⟩ := cell_eq hc (isM_of_isW hW) hMF hC (covers_of_cell rfl rfl ha0)
          refine mem_idxs.mpr ⟨hwn, ?_⟩
          simp only [Bool.and_eq_true, beq_iff_eq]
          exact ⟨⟨hW, ha⟩, hs⟩
        · intro hwm
          obtain ⟨hwn, hp⟩ := mem_idxs.mp hwm
          simp only [Bool.and_eq_true, beq_iff_eq] at hp
          obtain ⟨⟨hW, ha⟩, hs⟩ := hp
          exact hw.coAll _ ht ⟨w, hwn⟩ hW (covers_of_cell ha hs ha0)
      simp only [g]
      rw [mem_arrangements]
      refine ⟨hw.coNodup _ ht, ?_, fun w hwm => (hmemco w).mp hwm⟩
      exact ((List.perm_ext_iff_of_nodup (hw.coNodup _ ht) (idxs_nodup _ _)).mpr hmemco).length_eq
  · refine ⟨rfl, rfl, ?_, ?_⟩
    · intro r y hR hy
      have hrn : r < x.n := by
        by_contra hrn
        have hle : x.evs.length ≤ r := Nat.le_of_not_lt hrn
        simp only [Exec.evN, List.getD_eq_getElem?_getD, List.getElem?_eq_none hle] at hR
        simp [Ev.isR] at hR
      have hNr : x.evN r = x.evs[r] := evN_eq x r hrn
      rw [hNr] at hR hy
      have hRF : (x.ev ⟨r, hrn⟩).isR = true := hR
      have hrs : r ∈ readsOf x.evs := mem_idxs.mpr ⟨hrn, hR⟩
      simp only [mkExec, lookup_zip_map _ _ _ hrs, Option.getD_some, f, hNr]
      exact rf_uniform hw hn hc hRF hy (hpos r hrn (isM_of_isR hR))
    · intro y hy
      obtain ⟨e, he, hM, hye⟩ := mem_touched.mp hy
      have hce : (e.addr, e.size) ∈ cellsOf x.evs := mem_cellsOf.mpr ⟨e, he, hM, rfl⟩
      simp only [mkExec]
      cases hfind : ((cellsOf x.evs).zip ((cellsOf x.evs).map g)).find?
          (fun p => decide (p.1.1 ≤ y) && decide (y < p.1.1 + p.1.2)) with
      | none =>
        exfalso
        have := List.find?_eq_none.mp hfind _ (mem_zip_map_of g hce)
        rw [mem_bytes] at hye
        simp [hye.1, hye.2] at this
      | some p =>
        have hp := List.find?_some hfind
        have hpm := List.mem_of_find?_eq_some hfind
        obtain ⟨hp2, hp1⟩ := mem_zip_map hpm
        obtain ⟨e', he', hM', hc'⟩ := mem_cellsOf.mp hp1
        obtain ⟨i', hi', rfl⟩ := List.getElem_of_mem he'
        simp only [Option.map_some, Option.getD_some, hp2, g]
        rw [← hc'] at hp ⊢
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
        exact co_uniform hw hn hc (e := ⟨i', hi'⟩) hM' (mem_bytes.mpr hp)
          (hpos i' hi' hM')

/-! ## Judging -/

theorem readsOkB_iff {t : Test} {x : Exec} {exps : List (List Byte)} :
    readsOkB t x exps = true ↔ ReadsOk t x exps := by
  simp only [readsOkB, ReadsOk, List.all_eq_true, List.mem_range, Bool.or_eq_true,
    Bool.not_eq_true', beq_iff_eq]
  constructor
  · intro h r hr hR
    rcases h r hr with h | h
    · rw [hR] at h; cases h
    · exact h
  · intro h r hr
    cases hR : (x.evN r).isR
    · exact Or.inl rfl
    · exact Or.inr (h r hr hR)

theorem xl_flag {x : Exec} : (decide x.Tso || (!decide x.Tame && decide x.Xl)) = true ↔ x.Xl := by
  constructor
  · intro h
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not] at h
    rcases h with h | h
    · exact x.xl_of_tso h
    · exact h.2
  · intro h
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not]
    by_cases ht : x.Tso
    · exact Or.inl ht
    · refine Or.inr ⟨fun hT => ht ((x.xl_iff_tso_of_tame hT).mp h), h⟩

theorem judge_sound {t : Test} {trs : List XTrace} {exps : List (List Byte)} {x : Exec}
    {j : Judged} (h : judge t trs exps x = some j) :
    x.Wf = true ∧ ReadsOk t x exps ∧ j.out = t.outcome (finalAx t trs x) ∧
      ∀ M : Model, M.sel j = true ↔ M.Holds x := by
  unfold judge at h
  simp only at h
  split at h
  · rename_i hc
    cases h
    simp only [Bool.and_eq_true] at hc
    obtain ⟨⟨hxl, hwf⟩, hro⟩ := hc
    refine ⟨hwf, readsOkB_iff.mp hro, rfl, ?_⟩
    intro M
    cases M with
    | sc =>
      simp only [Model.sel, Model.Holds, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨fun h => h.2, fun h => ⟨x.tso_of_sc h, h⟩⟩
    | tso => simp [Model.sel, Model.Holds]
    | xl => exact xl_flag
  · cases h

theorem judge_complete {t : Test} {trs : List XTrace} {exps : List (List Byte)} {x : Exec}
    {M : Model} (hwf : x.Wf = true) (hro : ReadsOk t x exps) (hM : M.Holds x) :
    ∃ j, judge t trs exps x = some j ∧ M.sel j = true ∧ j.out = t.outcome (finalAx t trs x) := by
  have hxl : x.Xl := by
    cases M with
    | sc => exact x.xl_of_sc hM
    | tso => exact x.xl_of_tso hM
    | xl => exact hM
  have hj : judge t trs exps x = some ⟨decide x.Tso && decide x.Sc, decide x.Tso,
      decide x.Tso || (!decide x.Tame && decide x.Xl), t.outcome (finalAx t trs x)⟩ := by
    have hc : ((decide x.Tso || (!decide x.Tame && decide x.Xl)) && x.Wf &&
        readsOkB t x exps) = true := by
      simp only [Bool.and_eq_true]
      exact ⟨⟨xl_flag.mpr hxl, hwf⟩, readsOkB_iff.mpr hro⟩
    unfold judge
    simp only [hc, ↓reduceIte]
  refine ⟨_, hj, ?_, rfl⟩
  obtain ⟨-, -, -, hsel⟩ := judge_sound hj
  exact (hsel M).mpr hM

theorem noTwo_of_model {x : Exec} {M : Model} (h : M.Holds x) : NoTwo x := by
  cases M with
  | sc => exact noTwo_of_sc h
  | tso => exact noTwo_of_tso h
  | xl => exact noTwo_of_xl h

/-! ## The enumerator -/

theorem mapM_flatten_mem {γ δ : Type} {f : γ → Option (List δ)} :
    ∀ {l : List γ} {rss : List (List δ)}, l.mapM f = some rss → ∀ y : δ,
      y ∈ rss.flatten ↔ ∃ a ∈ l, ∃ ys, f a = some ys ∧ y ∈ ys
  | [], rss, h, y => by simp at h; subst h; simp
  | a :: l, rss, h, y => by
    rw [List.mapM_cons] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨ys, ha, rs, hl, rfl⟩ := h
    simp only [List.flatten_cons, List.mem_append, List.mem_cons, exists_eq_or_imp,
      mapM_flatten_mem hl y, ha, Option.some.injEq, exists_eq_left']

theorem mapM_some_of_mem {γ δ : Type} {f : γ → Option δ} :
    ∀ {l : List γ} {rs : List δ}, l.mapM f = some rs → ∀ a ∈ l, ∃ r, f a = some r
  | [], _, _, a, ha => by simp at ha
  | b :: l, rs, h, a, ha => by
    rw [List.mapM_cons] at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨r, hb, rs', hl, rfl⟩ := h
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨r, hb⟩
    · exact mapM_some_of_mem hl a ha

theorem mem_outsBy {js : List Judged} {p : Judged → Bool} {o : Outcome} :
    o ∈ outsBy js p ↔ ∃ j ∈ js, p j = true ∧ j.out = o := by
  simp [outsBy, mem_uniq, List.mem_map, List.mem_filter, and_assoc]

/-- **The axiomatic enumerator is exact**: when `Test.axJudge` succeeds, the outcomes of its
judged candidates consistent under a model are exactly the outcomes of `AxReach` under it. -/
theorem axJudge_spec {t : Test} {T : List (List XTrace)} {js : List Judged}
    (h : t.axJudge T = some js) (M : Model) (o : Outcome) :
    o ∈ outsBy js M.sel ↔ ∃ f, AxReach t T M.Holds f ∧ t.outcome f = o := by
  unfold Test.axJudge at h
  obtain ⟨rss, hm, rfl⟩ := Option.map_eq_some_iff.mp h
  rw [mem_outsBy]
  constructor
  · rintro ⟨j, hj, hsel, rfl⟩
    obtain ⟨trs, htrs, jl, hjc, hjl⟩ := (mapM_flatten_mem hm j).mp hj
    unfold judgeCombo at hjc
    simp only at hjc
    split at hjc
    · cases hjc
      obtain ⟨x, hx, hjx⟩ := List.mem_filterMap.mp hjl
      obtain ⟨hwf, hro, hout, hs⟩ := judge_sound hjx
      obtain ⟨rfc, -, coc, -, rfl⟩ := mem_candidates.mp hx
      exact ⟨_, ⟨trs, (mem_seqL _ _).mp htrs, _, rfl, rfl, hwf, hro, (hs M).mp hsel, rfl⟩,
        hout.symm⟩
    · cases hjc
  · rintro ⟨f, ⟨trs, htrs, x, hevs, hrmw, hwf, hro, hM, rfl⟩, rfl⟩
    have htrs' : trs ∈ seqL T := (mem_seqL _ _).mpr htrs
    obtain ⟨jl, hjc⟩ := mapM_some_of_mem hm trs htrs'
    have hjc' := hjc
    unfold judgeCombo at hjc'
    simp only at hjc'
    split at hjc'
    · rename_i hcells
      cases hjc'
      obtain ⟨x', hx', hag⟩ := cand_complete t hcells hevs hrmw hwf hro (noTwo_of_model hM)
      obtain ⟨hsc, htso, hxl, hwf', hro', hfin⟩ := agree_all hag
      have hM' : M.Holds x' := by
        cases M with
        | sc => exact hsc.mp hM
        | tso => exact htso.mp hM
        | xl => exact hxl.mp hM
      obtain ⟨j, hj, hsel, hout⟩ := judge_complete (trs := trs) (hwf'.symm.trans hwf)
        ((hro' t _).mp hro) hM'
      refine ⟨j, (mapM_flatten_mem hm j).mpr ⟨trs, htrs', _, hjc,
        List.mem_filterMap.mpr ⟨x', hx', hj⟩⟩, hsel, ?_⟩
      rw [hout, ← hfin]
    · cases hjc'

end Silmaril.Proofs.X86.MemoryModel.Litmus
