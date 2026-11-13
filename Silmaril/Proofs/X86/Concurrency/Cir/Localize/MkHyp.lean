module

public import Silmaril.Proofs.X86.Concurrency.Cir.Localize.Glue
public import Silmaril.Proofs.X86.Concurrency.Cir.Localize.Restrict

/-!
# Localisation: the hypotheses of the surgery from unit facts

`mkHyp`: `Surg.Hyp` for kept units that avoid the cells (`UK`), fragment
units on the cells (`UC`) and block units (`UG`), with the cell bytes `cellB cs`.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Localize

open Silmaril.X86.MemoryModel.Axiomatic
open Silmaril.X86.MemoryModel.Litmus (Byte)

/-- The bytes of the cells. -/
def cellB (cs : List (Nat × Nat)) (y : Nat) : Bool := cs.any fun c => decide (c.1 ≤ y ∧ y < c.1 + c.2)

theorem covers_iff {e : Ev} {y : Nat} : e.covers y = true ↔ e.addr ≤ y ∧ y < e.addr + e.size := by
  simp [Ev.covers]

theorem cellB_false {cs : List (Nat × Nat)} {u : Ev × List Byte} (hu : UK cs u) (hM : u.1.isM = true)
    {y : Nat} (hy : u.1.covers y = true) : cellB cs y = false := by
  obtain ⟨h1, h2, h3⟩ := hu hM
  rw [covers_iff] at hy
  simp only [cellB, List.any_eq_false, decide_eq_true_eq, not_and, not_lt]
  intro c hc h
  rcases h3 c hc with h | h <;> omega

theorem cellB_true {cs : List (Nat × Nat)} {u : Ev × List Byte} (hu : UC cs u) (hM : u.1.isM = true)
    {y : Nat} (hy : u.1.covers y = true) : cellB cs y = true := by
  obtain ⟨h1, h2, h3⟩ := hu hM
  rw [covers_iff] at hy
  simp only [cellB, List.any_eq_true, decide_eq_true_eq]
  exact ⟨_, h3, hy⟩

theorem ov_KC {cs : List (Nat × Nat)} {u v : Ev × List Byte} (hu : UK cs u) (hM : u.1.isM = true)
    (hv : UC cs v) (hvM : v.1.isM = true) : u.1.accOverlap v.1 = false := by
  obtain ⟨-, -, h3⟩ := hu hM
  obtain ⟨g1, g2, g3⟩ := hv hvM
  have := h3 _ g3
  simp only [Ev.accOverlap, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  simp only at this; omega

theorem UC_of_UG {cs : List (Nat × Nat)} {ib : Nat → Byte} {u : Ev × List Byte} (h : UG cs ib u) :
    UC cs u := fun _ => ⟨h.2.2.2.2.1.symm, h.2.2.2.2.2.1.symm, h.2.2.2.2.2.2.2.1⟩

theorem UG_isM {cs : List (Nat × Nat)} {ib : Nat → Byte} {u : Ev × List Byte} (h : UG cs ib u) :
    u.1.isM = true := by
  rcases h.1 with h | h <;> simp [Ev.isM, h]

/-- **The surgery's hypotheses.** -/
theorem mkHyp (cs : List (Nat × Nat)) (ib : Nat → Byte) (A F G C : List (Ev × List Byte))
    (i p1 : Nat)
    (hA : ∀ u ∈ A, UK cs u ∧ (u.1.tid = i → u.1.pos < p1))
    (hC : ∀ u ∈ C, UK cs u ∧ (u.1.tid = i → p1 + F.length ≤ u.1.pos) ∧
      (u.1.tid = i → u.1.isW = true → u.1.locked = true → p1 + F.length < u.1.pos))
    (hF : ∀ u ∈ F, UC cs u) (hG : ∀ u ∈ G, UG cs ib u)
    (posG : ∀ k (h : k < G.length), (G[k]).1.tid = i ∧ (G[k]).1.pos = p1 + k)
    (rwG : ∀ k k' (hk : k < G.length) (hk' : k' < G.length), k ≤ k' →
      (G[k]).1.isW = true → (G[k']).1.isW = true) :
    Surg.Hyp ⟨A, F, G, C, i, p1, cellB cs⟩ ib where
  posA u hu := (hA u hu).2
  posC u hu := (hC u hu).2.1
  lockC u hu := (hC u hu).2.2
  posG := posG
  offAC u hu hM y hy := by
    rcases List.mem_append.mp hu with hu | hu
    · exact cellB_false (hA u hu).1 hM hy
    · exact cellB_false (hC u hu).1 hM hy
  onF u hu hM y hy := cellB_true (hF u hu) hM hy
  onG u hu y hy := cellB_true (UC_of_UG (hG u hu)) (UG_isM (hG u hu)) hy
  ovG u hu v hv hM := by
    have hK : UK cs u := by
      rcases List.mem_append.mp hu with hu | hu
      · exact (hA u hu).1
      · exact (hC u hu).1
    exact ov_KC hK hM (UC_of_UG (hG v hv)) (UG_isM (hG v hv))
  ovF u hu v hv hM hvM := by
    have hK : UK cs u := by
      rcases List.mem_append.mp hu with hu | hu
      · exact (hA u hu).1
      · exact (hC u hu).1
    exact ov_KC hK hM (hF v hv) hvM
  memG u hu := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, -, -⟩ := hG u hu
    exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  rwG := rwG
  readG u hu := (hG u hu).2.2.2.2.2.2.2.2

end Silmaril.Proofs.X86.Concurrency.Cir.Localize
