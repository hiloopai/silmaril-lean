module

public import Silmaril.X86.MemoryModel.Litmus.Models.Defs
public import Silmaril.X86.MemoryModel.Axiomatic.Thms

/-!
# Localisation: basic facts about candidate executions

Well-formedness unpacked, `before` under an injective renaming, and
`rmwPairs` membership. `mem_bytes`, `any_bytes`, `evN_eq`, `wf_rf`, `wf_co`, `touched_of`,
`before_mem`, `before_sorted`, `written_iff` are **copied** (some generalised) from
`Silmaril/Proofs/X86/Concurrency/Cir/Seq/{Mem,Exec}.lean`, whose header does not
export them.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Localize

open Silmaril.X86.MemoryModel.Axiomatic
open Silmaril.X86.MemoryModel.Litmus (Byte dummyEv rmwPairs writtenByte)

theorem mem_bytes {e : Ev} {y : Nat} : y ∈ e.bytes ↔ e.covers y = true := by
  simp only [Ev.bytes, List.mem_range'_1, Ev.covers, Bool.and_eq_true, decide_eq_true_eq]

theorem any_bytes {e : Ev} {p : Nat → Bool} :
    e.bytes.any p = true ↔ ∃ y, e.covers y = true ∧ p y = true := by
  simp only [List.any_eq_true, mem_bytes]

theorem getD_eq {evs : List Ev} {i : Nat} (h : i < evs.length) (d : Ev) :
    evs.getD i d = evs[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem evN_eq {x : Exec} {i : Nat} (h : i < x.n) : x.evN i = x.evs[i] := getD_eq h _

theorem ev_eq {x : Exec} (a : Fin x.n) : x.ev a = x.evs[a.val] := rfl

theorem W_ne_R {e : Ev} (hW : e.isW = true) (hR : e.isR = true) : False := by
  simp only [Ev.isW, Ev.isR, beq_iff_eq] at hW hR; rw [hW] at hR; cases hR

theorem isM_of_W {e : Ev} (hW : e.isW = true) : e.isM = true := by simp [Ev.isM, hW]
theorem isM_of_R {e : Ev} (hR : e.isR = true) : e.isM = true := by simp [Ev.isM, hR]

/-! ## Well-formedness, unpacked -/

section Wf
variable {x : Exec}

theorem wf_rf (hwf : x.Wf = true) {r : Nat} (hr : r < x.n) (hR : (x.evs[r]).isR = true) {y : Nat}
    (hy : (x.evs[r]).covers y = true) {w : Nat} (h : x.rf r y = some w) :
    ∃ hw : w < x.n, (x.evs[w]).isW = true ∧ (x.evs[w]).covers y = true := by
  simp only [Exec.Wf, Bool.and_eq_true, List.all_eq_true] at hwf
  have := hwf.1.1.1.1 ⟨r, hr⟩ (List.mem_finRange _)
  simp only [Exec.ev, Fin.getElem_fin, hR, Bool.not_true, Bool.false_or, List.all_eq_true] at this
  have := this y (mem_bytes.mpr hy)
  rw [h] at this
  simp only [Exec.valid, Bool.and_eq_true, decide_eq_true_eq] at this
  obtain ⟨⟨hv, hW⟩, hC⟩ := this
  exact ⟨hv, by rwa [evN_eq hv] at hW, by rwa [evN_eq hv] at hC⟩

theorem touched_of {y : Nat} {w : Nat} (hw : w < x.n) (hM : (x.evs[w]).isM = true)
    (hC : (x.evs[w]).covers y = true) : y ∈ x.touched := by
  simp only [Exec.touched, List.mem_flatMap, List.mem_filter]
  exact ⟨x.evs[w], ⟨List.getElem_mem _, hM⟩, mem_bytes.mpr hC⟩

theorem mem_touched {y : Nat} (h : y ∈ x.touched) :
    ∃ w, ∃ hw : w < x.n, (x.evs[w]).isM = true ∧ (x.evs[w]).covers y = true := by
  simp only [Exec.touched, List.mem_flatMap, List.mem_filter] at h
  obtain ⟨e, ⟨he, hM⟩, hy⟩ := h
  obtain ⟨w, hw, rfl⟩ := List.getElem_of_mem he
  exact ⟨w, hw, hM, mem_bytes.mp hy⟩

theorem wf_co (hwf : x.Wf = true) {y : Nat} (hy : y ∈ x.touched) :
    (x.co y).Nodup ∧
      (∀ w ∈ x.co y, ∃ hw : w < x.n, (x.evs[w]).isW = true ∧ (x.evs[w]).covers y = true) ∧
      ∀ w (hw : w < x.n), (x.evs[w]).isW = true → (x.evs[w]).covers y = true → w ∈ x.co y := by
  simp only [Exec.Wf, Bool.and_eq_true, List.all_eq_true] at hwf
  have := hwf.1.1.1.2 y hy
  simp only [decide_eq_true_eq] at this
  obtain ⟨⟨hnd, hall⟩, hcov⟩ := this
  refine ⟨hnd, fun w hw => ?_, fun w hw hW hC => ?_⟩
  · have := hall w hw
    simp only [Exec.valid, decide_eq_true_eq] at this
    obtain ⟨⟨hv, hW⟩, hC⟩ := this
    exact ⟨hv, by rwa [evN_eq hv] at hW, by rwa [evN_eq hv] at hC⟩
  · have := hcov ⟨w, hw⟩ (List.mem_finRange _)
    simp only [Exec.ev, Fin.getElem_fin, Bool.not_and, Bool.or_eq_true, Bool.not_eq_true', List.contains_iff_mem]
      at this
    rcases this with (h | h) | h
    · simp [hW] at h
    · simp [hC] at h
    · exact h

theorem wf_rmw (hwf : x.Wf = true) {a b : Nat} (h : (a, b) ∈ x.rmw) :
    (x.evN a).accAddr = (x.evN b).accAddr ∧ (x.evN a).accSize = (x.evN b).accSize := by
  simp only [Exec.Wf, Bool.and_eq_true, List.all_eq_true] at hwf
  have := hwf.1.1.2 _ h
  simp only [beq_iff_eq] at this
  exact ⟨this.1.2, this.2⟩

theorem wf_sm (hwf : x.Wf = true) {a b : Fin x.n} (h : x.sm a b = true) :
    (x.ev a).act = (x.ev b).act ∧ (x.ev a).locked = (x.ev b).locked ∧ (x.ev a).ann = (x.ev b).ann ∧
      (x.ev a).accAddr = (x.ev b).accAddr ∧ (x.ev a).accSize = (x.ev b).accSize := by
  simp only [Exec.Wf, Bool.and_eq_true, List.all_eq_true] at hwf
  have := hwf.1.2 a (List.mem_finRange _) b (List.mem_finRange _)
  simp only [h, Bool.not_true, Bool.false_or, Bool.and_eq_true, beq_iff_eq] at this
  exact ⟨this.1.1.1.1, this.1.1.1.2, this.1.1.2, this.1.2, this.2⟩

theorem wf_ev (hwf : x.Wf = true) {e : Ev} (he : e ∈ x.evs) :
    (if e.isM then
      decide (0 < e.size) && decide (e.accAddr ≤ e.addr) &&
        decide (e.addr + e.size ≤ e.accAddr + e.accSize) && (!e.isW || e.data.length == e.size)
    else e.size == 0) = true := by
  simp only [Exec.Wf, Bool.and_eq_true, List.all_eq_true] at hwf
  exact hwf.2 e he

end Wf

/-! ## `before` -/

theorem before_mem {l : List Nat} {a b : Nat} (h : before l a b = true) : a ∈ l ∧ b ∈ l := by
  induction l with
  | nil => simp [before] at h
  | cons c l ih =>
    simp only [before] at h
    split at h
    · rename_i hc
      simp only [beq_iff_eq] at hc
      subst hc
      exact ⟨List.mem_cons_self, List.mem_cons_of_mem _ (List.contains_iff_mem.mp h)⟩
    · obtain ⟨h1, h2⟩ := ih h
      exact ⟨List.mem_cons_of_mem _ h1, List.mem_cons_of_mem _ h2⟩

theorem before_sorted {l : List Nat} (hs : l.Pairwise (· < ·)) {a b : Nat}
    (h : before l a b = true) : a < b := by
  induction l with
  | nil => simp [before] at h
  | cons c l ih =>
    simp only [before] at h
    split at h
    · rename_i hc
      simp only [beq_iff_eq] at hc
      subst hc
      exact List.rel_of_pairwise_cons hs (List.contains_iff_mem.mp h)
    · exact ih hs.of_cons h

/-- `before` under a renaming that hits `a` and `b` exactly at `a0` and `b0`. -/
theorem before_map {f : Nat → Nat} {a b a0 b0 : Nat} (ha : ∀ c, f c = a ↔ c = a0)
    (hb : ∀ c, f c = b ↔ c = b0) : ∀ l : List Nat, before (l.map f) a b = before l a0 b0
  | [] => rfl
  | c :: l => by
    simp only [List.map_cons, before]
    by_cases hca : c = a0
    · subst hca
      have h1 : (f c == a) = true := by simp [(ha c).mpr rfl]
      simp only [h1, beq_self_eq_true, ite_true]
      apply Bool.eq_iff_iff.mpr
      rw [List.contains_iff_mem, List.contains_iff_mem, List.mem_map]
      constructor
      · rintro ⟨u, hu, he⟩; rwa [← (hb u).mp he]
      · intro h; exact ⟨b0, h, (hb b0).mpr rfl⟩
    · have h1 : (f c == a) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; exact fun h => hca ((ha c).mp h)
      simp only [h1, beq_eq_false_iff_ne.mpr hca, Bool.false_eq_true, ite_false]
      exact before_map ha hb l

/-- `before` under a renaming that, on the list, hits `a` and `b` exactly at `a0` and `b0`. -/
theorem before_map_on {f : Nat → Nat} {a b a0 b0 : Nat} :
    ∀ l : List Nat, (∀ c ∈ l, f c = a ↔ c = a0) → (∀ c ∈ l, f c = b ↔ c = b0) →
      before (l.map f) a b = before l a0 b0
  | [], _, _ => rfl
  | c :: l, ha, hb => by
    simp only [List.map_cons, before]
    have ha' : ∀ c' ∈ l, f c' = a ↔ c' = a0 := fun c' h => ha c' (List.mem_cons_of_mem _ h)
    have hb' : ∀ c' ∈ l, f c' = b ↔ c' = b0 := fun c' h => hb c' (List.mem_cons_of_mem _ h)
    by_cases hca : c = a0
    · subst hca
      have h1 : (f c == a) = true := by simp [(ha c List.mem_cons_self).mpr rfl]
      simp only [h1, beq_self_eq_true, ite_true]
      apply Bool.eq_iff_iff.mpr
      rw [List.contains_iff_mem, List.contains_iff_mem, List.mem_map]
      constructor
      · rintro ⟨u, hu, he⟩; rwa [← (hb' u hu).mp he]
      · intro h; exact ⟨b0, h, (hb' b0 h).mpr rfl⟩
    · have h1 : (f c == a) = false := by
        simp only [beq_eq_false_iff_ne, ne_eq]; exact fun h => hca ((ha c List.mem_cons_self).mp h)
      simp only [h1, beq_eq_false_iff_ne.mpr hca, Bool.false_eq_true, ite_false]
      exact before_map_on l ha' hb'

theorem accOverlap_comm (e f : Ev) : e.accOverlap f = f.accOverlap e := by
  simp only [Ev.accOverlap, Bool.and_comm]

/-- An element of the image of `l` is the image of an element of `l`. -/
theorem before_map_mem {f : Nat → Nat} {l : List Nat} {a b : Nat}
    (h : before (l.map f) a b = true) : (∃ u ∈ l, f u = a) ∧ ∃ v ∈ l, f v = b := by
  obtain ⟨h1, h2⟩ := before_mem h
  simp only [List.mem_map] at h1 h2
  exact ⟨h1, h2⟩

/-! ## Locked pairs -/

theorem mem_rmwPairs_iff {evs : List Ev} {a b : Nat} :
    (a, b) ∈ rmwPairs evs ↔ ∃ (ha : a < evs.length) (hb : b < evs.length),
      evs[a].isR = true ∧ evs[a].locked = true ∧ evs[b].isW = true ∧ evs[b].locked = true ∧
      evs[a].tid = evs[b].tid ∧ evs[b].pos = evs[a].pos + 1 ∧ evs[a].addr = evs[b].addr ∧
      evs[a].size = evs[b].size := by
  simp only [rmwPairs, List.mem_flatMap]
  constructor
  · rintro ⟨qa, hqa, hq⟩
    by_cases hA : (qa.1.isR && qa.1.locked) = true
    · rw [ite_eq_left hA, List.mem_filterMap] at hq
      obtain ⟨qb, hqb, hq⟩ := hq
      simp only [Option.ite_none_right_eq_some, Option.some.injEq, Prod.mk.injEq] at hq
      obtain ⟨hB, rfl, rfl⟩ := hq
      obtain ⟨ha1, ha2⟩ := List.mem_zipIdx' (x := qa.1) (i := qa.2) hqa
      obtain ⟨hb1, hb2⟩ := List.mem_zipIdx' (x := qb.1) (i := qb.2) hqb
      refine ⟨ha1, hb1, ?_⟩
      rw [← ha2, ← hb2]
      simp only [Bool.and_eq_true, beq_iff_eq] at hA hB
      exact ⟨hA.1, hA.2, hB.1.1.1.1.1, hB.1.1.1.1.2, hB.1.1.1.2, hB.1.1.2, hB.1.2, hB.2⟩
    · rw [ite_eq_right hA] at hq; simp at hq
  · rintro ⟨ha, hb, h1, h2, h3, h4, h5, h6, h7, h8⟩
    refine ⟨(evs[a], a), List.mem_zipIdx_iff_getElem?.mpr (by simp [ha]), ?_⟩
    simp only [h1, h2, Bool.and_self, ite_true, List.mem_filterMap]
    refine ⟨(evs[b], b), List.mem_zipIdx_iff_getElem?.mpr (by simp [hb]), ?_⟩
    simp [h3, h4, h5, h6, h7, h8]

/-! ## Written bytes -/

theorem written_iff {x : Exec} {y : Nat} :
    writtenByte x y = true ↔ ∃ w, ∃ hw : w < x.n, (x.evs[w]).isW = true ∧ (x.evs[w]).covers y = true := by
  simp only [writtenByte, List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨e, he, h1, h2⟩
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    exact ⟨i, hi, h1, h2⟩
  · rintro ⟨w, hw, h1, h2⟩
    exact ⟨_, List.getElem_mem _, h1, h2⟩

end Silmaril.Proofs.X86.Concurrency.Cir.Localize
