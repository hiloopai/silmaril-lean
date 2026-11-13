module

public import Silmaril.Proofs.X86.Concurrency.Cir.Rc.Arc

/-!
# Proofs: the first clone shares a uniquely owned object

`rc_inc_uniq`: `{uniq l P ∗ blank l j ∗ blank l k} rc_inc {tok l j ∗ tok l k}`. A thread that
owns the object outright (count `1`, payload `P`: just created, `Arc::new`) and two blanks
clones it: at the locked add the count, the payload and the two slots move into the invariant,
which was in its empty-ledger state, and the thread keeps two tokens.
-/

@[expose] public section

namespace Silmaril.Proofs.X86.Concurrency.Cir.Rc

open Silmaril.X86.Concurrency.Cir
open Silmaril.X86.Concurrency.Cir.Csl
open Silmaril.X86.Concurrency.Cir.Rc
open Silmaril.X86.Concurrency.Cir.Mutex (safe_inv_frame)

theorem disj_of' {h₁ h₂ : Heap} (H : ∀ x, (h₁ x).isSome → h₂ x = none) : Heap.Disjoint h₁ h₂ := by
  intro x
  cases e : h₁ x with
  | none => exact Or.inl rfl
  | some v => exact Or.inr (H x (by simp [e]))

/-- The ledger with two more slots in use, off those slots. -/
theorem ledger_off2 {l j k x : Nat} (hA : x ≠ gA l j) (hB : x ≠ gB l j) (hA' : x ≠ gA l k)
    (hB' : x ≠ gB l k) : ledger l [j, k] x = ledger l [] x := by
  rw [ledger_off (k := j) (S' := [k]) (fun i hi => by simp [hi]) hA hB,
    ledger_off (k := k) (S' := []) (fun i hi => by simp [hi]) hA' hB']

set_option maxHeartbeats 800000 in
/-- **The first clone of a uniquely owned object.** -/
theorem rc_inc_uniq {P : HProp} {l j k : Nat} {d : Reg} {a : Expr} {rs : Regs} {h : Heap}
    (ha : (a.eval rs).toNat = l) (hjk : j ≠ k) (hh : (uniq l P ∗ blank l j ∗ blank l k) h) :
    Csl.Safe (rcInv l P) (fun _ => tok l j ∗ tok l k) (rcInc d a) rs h := by
  have hl : l < gbase := ha ▸ eval_lt a rs
  obtain ⟨hu, hb, dub, rfl, Hu, Hb⟩ := sep_iff.mp hh
  obtain ⟨hc, hP, dcP, rfl, rfl, hp⟩ := sep_iff.mp Hu
  obtain ⟨hbj, hbk, dbb, rfl, ⟨hj, rfl⟩, ⟨hk, rfl⟩⟩ := sep_iff.mp Hb
  have nAB : ∀ i i', gA l i ≠ gB l i' := fun i i' => gA_ne_gB l i i' hl
  have nAl : ∀ i, gA l i ≠ l := fun i => gA_ne_lt hl
  have nBl : ∀ i, gB l i ≠ l := fun i => gB_ne_lt hl
  have nAA : gA l j ≠ gA l k := fun e => hjk (gA_inj hl e)
  have nBB : gB l j ≠ gB l k := fun e => hjk (gB_inj hl e)
  -- the payload avoids the count cell and the two blanks
  have hPbj : hP (gB l j) = none :=
    (union_eq_none.mp (none_of_disjoint (disjoint_symm dub)
      (by simp [union_or, single_self]))).2
  have hPbk : hP (gB l k) = none :=
    (union_eq_none.mp (none_of_disjoint (disjoint_symm dub)
      (by simp [union_or, single_self, single_ne (Ne.symm nBB)]))).2
  refine safe_rmw_at ha (fun hI hi hd => ?_)
  -- the invariant is in its empty-ledger state: the thread owns the count cell
  have hhl : (Heap.union (Heap.union (Heap.single l 1) hP)
      (Heap.union (Heap.single (gB l j) 0) (Heap.single (gB l k) 0)) l) = some 1 := by
    simp [union_or, single_self]
  obtain ⟨S, hn, hbS, hst⟩ := hi
  have hS : S = [] ∧ hI = ledger l [] := by
    rcases hst with h0 | ⟨-, H⟩
    · exact h0
    · exfalso
      obtain ⟨g, r, -, rfl, rfl, H2⟩ := sep_iff.mp H
      obtain ⟨c, q, -, rfl, rfl, -⟩ := sep_iff.mp H2
      exact disjoint_some hd (a := l) (by rw [hhl]; rfl) (by simp [union_or, single_self])
  obtain ⟨rfl, rfl⟩ := hS
  -- the payload avoids the ledger
  have hPL : ∀ x, (ledger l [] x).isSome → hP x = none := fun x hx =>
    (union_eq_none.mp (union_eq_none.mp (none_of_disjoint (disjoint_symm hd) hx)).1).2
  have hPA : ∀ i, i < M → hP (gA l i) = none := fun i hi =>
    hPL _ (by rw [ledger_gA _ hl hi]; simp)
  refine ⟨by rw [union_some hhl]; rfl, fun old hold => ?_⟩
  rw [union_some hhl] at hold
  cases hold
  rw [add_one_result (by decide)]
  have hj2 : j ∈ [j, k] := by simp
  have hk2 : k ∈ [j, k] := by simp
  refine ⟨Heap.union (Heap.single (gA l j) 0) (Heap.single (gA l k) 0),
    Heap.union (ledger l [j, k]) (Heap.union (Heap.single l 2) hP), ?_, ?_, ?_, ?_⟩
  · -- the new heaps are disjoint
    refine disj_of' fun x hx => ?_
    rcases union_isSome.mp hx with h1 | h1
    · have : x = gA l j := by by_contra hne; simp [single_apply, hne] at h1
      subst this
      simp [union_or, ledger_gA _ hl hj, hj2, single_ne (nAl j), hPA j hj]
    · have : x = gA l k := by by_contra hne; simp [single_apply, hne] at h1
      subst this
      simp [union_or, ledger_gA _ hl hk, hk2, single_ne (nAl k), hPA k hk]
  · -- the union is the old union with the count written
    funext x
    simp only [union_or, setH]
    by_cases hx : x = l
    · subst hx
      simp [single_ne (nAl j).symm, single_ne (nAl k).symm, ledger_lt _ hl, single_self]
    · simp only [hx, ite_false, single_ne hx, Option.none_or]
      by_cases e1 : x = gA l j
      · subst e1
        simp [single_self, ledger_gA _ hl hj, hPA j hj, single_ne (nAB j j), single_ne (nAB j k)]
      · by_cases e2 : x = gA l k
        · subst e2
          simp [single_self, single_ne nAA.symm, ledger_gA _ hl hk, hPA k hk,
            single_ne (nAB k j), single_ne (nAB k k)]
        · by_cases e3 : x = gB l j
          · subst e3
            simp [single_ne (nAB j j).symm, single_ne (nAB k j).symm, ledger_gB _ hl hj, hj2,
              hPbj, single_self]
          · by_cases e4 : x = gB l k
            · subst e4
              simp [single_ne (nAB j k).symm, single_ne (nAB k k).symm, ledger_gB _ hl hk, hk2,
                hPbk, single_self, single_ne nBB.symm]
            · rw [single_ne e1, single_ne e2, single_ne e3, single_ne e4,
                ledger_off2 e1 e3 e2 e4]
              cases e : hP x with
              | none => simp
              | some v =>
                have : ledger l [] x = none := by
                  cases e' : ledger l [] x with
                  | none => rfl
                  | some w => have := hPL x (by simp [e']); simp [e] at this
                simp [this]
  · -- the invariant: slots `j` and `k` in use, count `2`, the payload
    refine ⟨[j, k], by simp [hjk],
      fun i hi => by simp at hi; rcases hi with rfl | rfl <;> assumption,
      Or.inr ⟨by simp, sep_iff.mpr ⟨_, _, ?_, rfl, rfl,
        sep_iff.mpr ⟨_, hP, disjoint_single_val dcP, rfl, rfl, hp⟩⟩⟩⟩
    refine disj_of' fun x hx => ?_
    have hxg : gbase ≤ x := by
      by_contra hlt; rw [ledger_lt _ (by omega)] at hx; simp at hx
    have hxl : x ≠ l := by omega
    simp only [union_or, single_ne hxl, Option.none_or]
    by_cases e1 : x = gB l j
    · subst e1; exact hPbj
    · by_cases e2 : x = gB l k
      · subst e2; exact hPbk
      · by_cases e3 : x = gA l j
        · subst e3; rw [ledger_gA _ hl hj] at hx; simp [hj2] at hx
        · by_cases e4 : x = gA l k
          · subst e4; rw [ledger_gA _ hl hk] at hx; simp [hk2] at hx
          · rw [ledger_off2 e3 e1 e4 e2] at hx
            exact hPL x hx
  · exact sep_iff.mpr ⟨_, _, disjoint_single nAA, rfl, ⟨hj, rfl⟩, ⟨hk, rfl⟩⟩

/-- **The first clone**, under any frame invariant. -/
theorem rc_inc_uniq_spec {P J : HProp} {l j k : Nat} {d : Reg} {a : Expr} {rs : Regs} {h : Heap}
    (ha : (a.eval rs).toNat = l) (hjk : j ≠ k) (hh : (uniq l P ∗ blank l j ∗ blank l k) h) :
    Csl.Safe (rcInv l P ∗ J) (fun _ => tok l j ∗ tok l k) (rcInc d a) rs h :=
  safe_inv_frame (rc_inc_uniq ha hjk hh)

end Silmaril.Proofs.X86.Concurrency.Cir.Rc
