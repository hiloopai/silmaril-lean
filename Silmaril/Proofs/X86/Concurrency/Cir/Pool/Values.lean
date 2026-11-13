module

public import Silmaril.Proofs.X86.Concurrency.Cir.Pool.Job

/-!
# Proofs: the values in a job's done cells

For a well-formed item (`Item.wfB`: distinct input and output addresses, the counter apart
from them, inputs apart from outputs, `arg` and `fn arg` of the right lengths):

* `doneH_cnt_one`: the run counter holds `1`;
* `doneH_outs`: the output cells hold `fn arg`, in order.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Pool

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Pool

/-- The value of a list of cells at the address of its `i`-th cell, addresses distinct. -/
theorem cellsH_at : ∀ {cs : List (Nat × Nat)} {vs : List Nat} (hl : vs.length = cs.length),
    (cs.map (·.1)).Nodup → ∀ i (hi : i < cs.length),
      cellsH (cellVals cs vs) (cs[i].1) = some (vs[i]'(by omega))
  | [], _, _, _, i, hi => by simp at hi
  | _ :: _, [], hl, _, _, _ => by simp at hl
  | c :: cs, v :: vs, hl, hnd, i, hi => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    cases i with
    | zero => simp [cellsH, cellVals]
    | succ i =>
      have hne : c.1 ≠ (cs[i]'(by simp at hi; omega)).1 := fun e =>
        hnd.1 ⟨cs[i]'(by simp at hi; omega), List.getElem_mem _, e.symm⟩
      have := cellsH_at (cs := cs) (vs := vs) (by simpa using hl) hnd.2 i (by simp at hi; omega)
      have hb : (c.1 == (cs[i]'(by simp at hi; omega)).1) = false := by simpa using hne
      simp only [cellsH, cellVals, List.find?_cons, List.getElem_cons_succ, hb] at this ⊢
      exact this

/-- The last write to the address of the `i`-th cell, addresses distinct. -/
theorem cellLast_at : ∀ {cs : List (Nat × Nat)} {vs : List Nat} (hl : vs.length = cs.length),
    (cs.map (·.1)).Nodup → ∀ i (hi : i < cs.length),
      cellLast (cellVals cs vs) (cs[i].1) = some (vs[i]'(by omega))
  | [], _, _, _, i, hi => by simp at hi
  | _ :: _, [], hl, _, _, _ => by simp at hl
  | c :: cs, v :: vs, hl, hnd, i, hi => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    cases i with
    | zero =>
      have : cellLast (cellVals cs vs) c.1 = none := by
        cases e : cellLast (cellVals cs vs) c.1 with
        | none => rfl
        | some w =>
          obtain ⟨d, hd, ed⟩ := cellLast_some (l := cellVals cs vs) (a := c.1) (by rw [e]; rfl)
          obtain ⟨d', hd', ed'⟩ := cellVals_fst hd
          exact absurd ⟨d', hd', ed'.trans ed⟩ hnd.1
      simp [cellVals, cellLast, this]
    | succ i =>
      have := cellLast_at (cs := cs) (vs := vs) (by simpa using hl) hnd.2 i (by simp at hi; omega)
      simp only [cellVals, cellLast, List.getElem_cons_succ]
      rw [this]; rfl

/-- No cell of the list is at `a`. -/
theorem cellLast_none {cs : List (Nat × Nat)} {vs : List Nat} {a : Nat}
    (h : a ∉ cs.map (·.1)) : cellLast (cellVals cs vs) a = none := by
  cases e : cellLast (cellVals cs vs) a with
  | none => rfl
  | some w =>
    obtain ⟨d, hd, ed⟩ := cellLast_some (l := cellVals cs vs) (a := a) (by rw [e]; rfl)
    obtain ⟨d', hd', ed'⟩ := cellVals_fst hd
    exact absurd (List.mem_map.mpr ⟨d', hd', ed'.trans ed⟩) h

theorem cellsH_none {cs : List (Nat × Nat)} {vs : List Nat} {a : Nat}
    (h : a ∉ cs.map (·.1)) : cellsH (cellVals cs vs) a = none := by
  cases e : cellsH (cellVals cs vs) a with
  | none => rfl
  | some w =>
    obtain ⟨d, hd, ed⟩ := cellsH_some e
    obtain ⟨d', hd', ed'⟩ := cellVals_fst hd
    exact absurd (List.mem_map.mpr ⟨d', hd', ed'.trans ed⟩) h

namespace Item

theorem ivals_eq {it : Item} (h : it.wfB = true) : it.ivals = it.arg := by
  simp only [Item.wfB, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_iff_eq,
    List.all_eq_true, List.contains_eq_mem, decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨⟨⟨⟨hin, -⟩, hci⟩, -⟩, -⟩, hlen⟩, -⟩ := h
  apply List.ext_getElem (by simp [Item.ivals, hlen])
  intro i h1 h2
  simp only [Item.ivals, List.getElem_map]
  have hi : i < it.job.ins.length := by simpa [Item.ivals] using h1
  have hne : (it.job.ins[i]'hi).1 ≠ it.cnt := fun e =>
    hci (List.mem_map.mpr ⟨_, List.getElem_mem _, e⟩)
  unfold Item.freshH
  rw [union_none (by simp [single_apply, hne]),
    union_some (cellsH_at hlen hin i hi)]
  rfl

theorem blkH_eq {it : Item} {a : Nat} (ha : a ∉ it.job.outs.map (·.1)) :
    it.blkH a = it.freshH a := by
  show (cellLast (cellVals it.job.outs (it.job.fn it.ivals)) a).or (it.freshH a) = _
  rw [cellLast_none ha]; rfl

/-- **The run counter of a well-formed item ends at `1`.** -/
theorem doneH_cnt_one {it : Item} (h : it.wfB = true) : it.doneH it.cnt = some 1 := by
  have hc : it.cnt ∉ it.job.outs.map (·.1) := by
    simp only [Item.wfB, Bool.and_eq_true, Bool.not_eq_true', List.contains_eq_mem,
      decide_eq_false_iff_not] at h
    exact h.1.1.1.2
  simp [Item.doneH, blkH_eq hc, freshH_cnt]

/-- **The output cells of a well-formed item hold `fn arg`.** -/
theorem doneH_outs {it : Item} (h : it.wfB = true) :
    it.job.outs.map (fun c => it.doneH c.1) = (it.job.fn it.arg).map some := by
  have h' := h
  simp only [Item.wfB, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', beq_iff_eq,
    List.contains_eq_mem, decide_eq_false_iff_not] at h'
  obtain ⟨⟨⟨⟨⟨⟨-, hout⟩, -⟩, hco⟩, -⟩, -⟩, hlen⟩ := h'
  apply List.ext_getElem (by simp [hlen])
  intro i h1 h2
  simp only [List.getElem_map]
  have hi : i < it.job.outs.length := by simpa using h1
  have hne : (it.job.outs[i]'hi).1 ≠ it.cnt := fun e =>
    hco (List.mem_map.mpr ⟨_, List.getElem_mem _, e⟩)
  simp only [Item.doneH, hne, ite_false]
  show (cellLast (cellVals it.job.outs (it.job.fn it.ivals)) _).or _ = _
  rw [ivals_eq h, cellLast_at (by rw [hlen]) hout i hi]
  rfl

end Item

end Silmaril.Proofs.X86.Concurrency.Cir.Pool
