module

public import Silmaril.Proofs.X86.Concurrency.Cir.Fj.Shape

/-!
# Fork-join CIR: candidate-execution facts

The few facts about XL's candidate executions the fork-join theorem
uses, for any execution:

* `ghb_of_fr`, `ghb_of_rfe`, `ghb_of_lock`: from-reads, external reads-from and the
  locked-instruction order are edges of XL's global order `ghbXl`;
* `wf_rf`, `wf_co`, `wf_coLast`: what `Exec.Wf` says about the source of a read byte and the
  coherence order of a byte;
* `units_idx`, `idx_units`, `readByte_eq`: units of `AxReach` and their expected bytes.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Fj

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.MemoryModel.Litmus (Byte XAct XTrace units ReadsOk)
open Silmaril.X86.MemoryModel.Axiomatic (Ev Exec BRel)

variable {x : Exec}

theorem any_finRange {n : Nat} {p : Fin n → Bool} (c : Fin n) (h : p c = true) :
    (List.finRange n).any p = true :=
  List.any_eq_true.mpr ⟨c, List.mem_finRange c, h⟩

theorem ghb_of_com {a b : Fin x.n} (h : (x.rfe.union (x.frR.union x.coR)) a b = true) :
    x.ghbXl a b = true := by
  have : x.comGhbXl a b = true := any_finRange b (by simp [h, Exec.smT])
  simp [Exec.ghbXl, BRel.union, this]

theorem ghb_of_fr {a b : Fin x.n} (h : x.frR a b = true) : x.ghbXl a b = true :=
  ghb_of_com (by simp [BRel.union, h])

theorem ghb_of_rfe {a b : Fin x.n} (h : x.rfe a b = true) : x.ghbXl a b = true :=
  ghb_of_com (by simp [BRel.union, h])

theorem ghb_of_lock {a b : Fin x.n} (h : x.lockXl a b = true) : x.ghbXl a b = true := by
  simp [Exec.ghbXl, BRel.union, h]

theorem mem_bytes {e : Ev} {y : Nat} : y ∈ e.bytes ↔ e.covers y = true := by
  simp [Ev.bytes, Ev.covers, List.mem_range'_1]

theorem evN_eq (a : Fin x.n) : x.evN a = x.ev a := by
  simp [Exec.evN, Exec.ev]

/-! ## Well-formedness -/

theorem wf_rf (h : x.Wf = true) {r : Fin x.n} (hr : (x.ev r).isR = true) {y : Nat}
    (hy : (x.ev r).covers y = true) {w : Nat} (hw : x.rf r.val y = some w) :
    w < x.n ∧ (x.evN w).isW = true ∧ (x.evN w).covers y = true := by
  simp only [Exec.Wf, Bool.and_eq_true, List.all_eq_true] at h
  have := h.1.1.1.1 r (List.mem_finRange r)
  simp only [hr, Bool.not_true, Bool.false_or, List.all_eq_true] at this
  have := this y (mem_bytes.mpr hy)
  rw [hw] at this
  simp only [Exec.valid, Bool.and_eq_true, decide_eq_true_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

theorem wf_co (h : x.Wf = true) {y : Nat} (w : Fin x.n) (hw : (x.ev w).isW = true)
    (hy : (x.ev w).covers y = true) :
    w.val ∈ x.co y ∧ ∀ v ∈ x.co y, v < x.n ∧ (x.evN v).isW = true ∧ (x.evN v).covers y = true := by
  simp only [Exec.Wf, Bool.and_eq_true, List.all_eq_true] at h
  have ht : y ∈ x.touched := by
    simp only [Exec.touched, List.mem_flatMap, List.mem_filter]
    exact ⟨x.ev w, ⟨List.getElem_mem _, by simp [Ev.isM, hw]⟩, mem_bytes.mpr hy⟩
  have := h.1.1.1.2 y ht
  refine ⟨?_, fun v hv => ?_⟩
  · have := this.2 w (List.mem_finRange w)
    simpa [hw, hy] using this
  · have := this.1.2 v hv
    simp only [Exec.valid, decide_eq_true_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩

theorem wf_coLast (h : x.Wf = true) {y : Nat} (w : Fin x.n) (hw : (x.ev w).isW = true)
    (hy : (x.ev w).covers y = true) :
    ∃ v, (x.co y).getLast? = some v ∧ v < x.n ∧ (x.evN v).isW = true ∧
      (x.evN v).covers y = true := by
  obtain ⟨hw', hall⟩ := wf_co h w hw hy
  have hne : x.co y ≠ [] := List.ne_nil_of_mem hw'
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp (List.getLast?_isSome.mpr hne)
  exact ⟨v, hv, hall v (List.mem_of_getLast? hv)⟩

/-! ## Units and indices -/

variable {trs : List XTrace}

theorem units_idx (hevs : x.evs = (units trs).map Prod.fst) (a : Fin x.n) :
    ∃ q ∈ units trs, q.1 = x.ev a ∧ ((units trs).map Prod.snd).getD a [] = q.2 := by
  have ha : a.val < (units trs).length := by
    have := a.isLt; simp only [Exec.n, hevs, List.length_map] at this; exact this
  refine ⟨(units trs)[a.val], List.getElem_mem _, ?_, ?_⟩
  · simp [Exec.ev, hevs]
  · simp [List.getD_eq_getElem?_getD, ha]

theorem idx_units (hevs : x.evs = (units trs).map Prod.fst) {q : Ev × List Byte}
    (hq : q ∈ units trs) :
    ∃ a : Fin x.n, x.ev a = q.1 ∧ ((units trs).map Prod.snd).getD a [] = q.2 := by
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hq
  have hk' : k < x.n := by simp [Exec.n, hevs, hk]
  refine ⟨⟨k, hk'⟩, by simp [Exec.ev, hevs], by simp [List.getD_eq_getElem?_getD, hk]⟩

theorem map_range'_getD {f : Nat → Byte} {a n y : Nat} (h1 : a ≤ y) (h2 : y < a + n) :
    ((List.range' a n).map f).getD (y - a) 0 = f y := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range' (by omega)]
  simp; congr 1; omega

/-- **What a read unit returns at a byte it covers.** -/
theorem readByte_eq {t : Silmaril.X86.MemoryModel.Litmus.Test} {exps : List (List Byte)}
    (hR : ReadsOk t x exps) (r : Fin x.n) (hr : (x.ev r).isR = true) {y : Nat}
    (hy : (x.ev r).covers y = true) :
    x.readByte t.initB r y = (exps.getD r []).getD (y - (x.ev r).addr) 0 := by
  have := hR r r.isLt (by rw [evN_eq]; exact hr)
  rw [← this]
  simp only [Exec.readBytes, evN_eq, Ev.bytes]
  simp only [Ev.covers, Bool.and_eq_true, decide_eq_true_eq] at hy
  rw [map_range'_getD hy.1 hy.2]

end Silmaril.Proofs.X86.Concurrency.Cir.Fj
