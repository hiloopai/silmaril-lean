module

public import Silmaril.Proofs.X86.Concurrency.Cir.Localize.Parts

/-!
# Localisation: final bytes on the cells

The block's writes carry the replay's final bytes (`blk_W`), every out
cell is written by the block (`blk_W_of`), and a byte inside a location is mapped initially
(`initByte_some`).
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Localize

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Seq
open Silmaril.X86.MemoryModel.Axiomatic
open Silmaril.X86.MemoryModel.Litmus (Byte XAct threadUnits actUnits initByte Loc)

theorem initByte_some {locs : List Loc} {y : Nat} {l : Loc} (hl : l ∈ locs)
    (h : l.addr ≤ y ∧ y < l.addr + l.size) : ∃ b, initByte locs y = some b := by
  unfold initByte
  cases hf : locs.find? (fun l => l.addr ≤ y && y < l.addr + l.size) with
  | some l' => exact ⟨_, rfl⟩
  | none =>
    have := List.find?_eq_none.mp hf l hl
    simp [h.1, h.2] at this

/-- A block write: its byte is the final memory's, and it is in an out cell. -/
theorem blk_W (m0 m1 : Mem) (ins outs : List (Nat × Nat)) (i p : Nat) {u : Ev × List Byte}
    (hu : u ∈ threadUnits i p (blkActs m0 m1 ins outs)) (hW : u.1.isW = true) {y : Nat}
    (hy : u.1.covers y = true) :
    u.1.byte y = (m1 y).getD 0 ∧ ∃ c ∈ outs, c.1 ≤ y ∧ y < c.1 + c.2 := by
  refine threadUnits_all (P := fun u => u.1.isW = true → u.1.covers y = true →
      u.1.byte y = (m1 y).getD 0 ∧ ∃ c ∈ outs, c.1 ≤ y ∧ y < c.1 + c.2) p _
    (fun a ha q u hu hW hy => ?_) u hu hW hy
  simp only [blkActs, List.mem_append, List.mem_map] at ha
  rcases ha with ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩
  · simp only [actUnits, ldAct, List.mem_singleton] at hu
    subst hu; simp [Ev.isW] at hW
  · simp only [actUnits, stAct, List.mem_singleton] at hu
    subst hu
    simp only [Ev.covers, Bool.and_eq_true, decide_eq_true_eq] at hy
    refine ⟨?_, c, hc, hy.1, hy.2⟩
    simp only [Ev.byte]
    rw [natBytes_val]
    simp only [Seq.bytesAt, List.getElem?_map, List.getElem?_range' (show y - c.1 < c.2 by omega)]
    simp only [Option.map_some, Option.getD_some]
    congr 2; omega

/-- Every byte of an out cell is covered by a block write. -/
theorem blk_W_of (m0 m1 : Mem) (ins outs : List (Nat × Nat)) (i p : Nat) {c : Nat × Nat}
    (hc : c ∈ outs) {y : Nat} (hy : c.1 ≤ y ∧ y < c.1 + c.2) :
    ∃ u ∈ threadUnits i p (blkActs m0 m1 ins outs), u.1.isW = true ∧ u.1.covers y = true := by
  have hsplit := threadUnits_append i p (ins.map fun c => ldAct .wb c.1 c.2 ((m0.val c.1 c.2).getD 0))
    (outs.map fun c => stAct .wb c.1 c.2 ((m1.val c.1 c.2).getD 0))
  simp only [blkActs]
  rw [hsplit]
  generalize p + _ = q
  suffices h : ∀ (l : List (Nat × Nat)) q, c ∈ l → ∃ u ∈ threadUnits i q
      (l.map fun c => stAct .wb c.1 c.2 ((m1.val c.1 c.2).getD 0)), u.1.isW = true ∧
      u.1.covers y = true by
    obtain ⟨u, hu, h⟩ := h outs q hc
    exact ⟨u, List.mem_append_right _ hu, h⟩
  intro l
  induction l with
  | nil => intro q h; simp at h
  | cons d l ih =>
    intro q h
    simp only [List.map_cons, Silmaril.X86.MemoryModel.Litmus.threadUnits]
    rcases List.mem_cons.mp h with rfl | h
    · refine ⟨_, List.mem_append_left _ (List.mem_singleton_self _), rfl, ?_⟩
      simp only [Ev.covers, stAct, Bool.and_eq_true]
      exact ⟨decide_eq_true hy.1, decide_eq_true hy.2⟩
    · obtain ⟨u, hu, h'⟩ := ih _ h
      exact ⟨u, List.mem_append_right _ hu, h'⟩

end Silmaril.Proofs.X86.Concurrency.Cir.Localize
