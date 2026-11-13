module

public import Silmaril.Logic.LinArith.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
# Farkas certificates: soundness

`Ineq.eval_eq_sum` writes a left-hand side as a sum over any finite set of variables containing
its support; `WRows.weighted_eval` sums weighted rows variable by variable, and
`WRows.IsCert.not_feasible` concludes. `WRows.check_sound`, `checkCert_sound`: the executable
checks are sound. `Cmd` lemmas: how one streaming command changes the weighted sums.
-/

namespace Silmaril.Logic.LinArith

open Finset

variable {K : Type*} [Field K]

namespace Ineq

theorem eval_cons (e : ℕ × ℤ) (cs : List (ℕ × ℤ)) (b : ℤ) (x : ℕ → K) :
    (⟨e :: cs, b⟩ : Ineq).eval x = (e.2 : K) * x e.1 + (⟨cs, b⟩ : Ineq).eval x := by
  simp only [eval, List.map_cons, List.sum_cons]

theorem coeff_cons (e : ℕ × ℤ) (cs : List (ℕ × ℤ)) (b : ℤ) (j : ℕ) :
    (⟨e :: cs, b⟩ : Ineq).coeff j = (if e.1 = j then e.2 else 0) + (⟨cs, b⟩ : Ineq).coeff j := by
  simp only [coeff, List.map_cons, List.sum_cons]

/-- One coefficient as a sum over a set of variables containing its index. -/
theorem single_sum {J : Finset ℕ} {j : ℕ} (hj : j ∈ J) (a : ℤ) (x : ℕ → K) :
    ∑ k ∈ J, ((if j = k then a else 0 : ℤ) : K) * x k = (a : K) * x j := by
  have h : ∀ k ∈ J, ((if j = k then a else 0 : ℤ) : K) * x k = if j = k then (a : K) * x j else 0 := by
    intro k _
    by_cases hk : j = k
    · simp only [hk, ↓reduceIte]
    · simp only [hk, ↓reduceIte, Int.cast_zero, zero_mul]
  rw [sum_congr rfl h, sum_ite_eq]
  simp only [hj, ↓reduceIte]

/-- **A left-hand side, variable by variable**, over any set `J` containing its support. -/
theorem eval_eq_sum (r : Ineq) {J : Finset ℕ} (hJ : ∀ e ∈ r.coeffs, e.1 ∈ J) (x : ℕ → K) :
    r.eval x = ∑ j ∈ J, (r.coeff j : K) * x j := by
  obtain ⟨cs, b⟩ := r
  induction cs with
  | nil => simp only [eval, coeff, List.map_nil, List.sum_nil, Int.cast_zero, zero_mul, sum_const_zero]
  | cons e cs ih =>
    have hcs : ∀ e' ∈ cs, e'.1 ∈ J := fun e' he' => hJ e' (List.mem_cons_of_mem e he')
    have hsplit : ∀ j ∈ J, (((⟨e :: cs, b⟩ : Ineq).coeff j : ℤ) : K) * x j =
        ((if e.1 = j then e.2 else 0 : ℤ) : K) * x j + (((⟨cs, b⟩ : Ineq).coeff j : ℤ) : K) * x j := by
      intro j _
      rw [coeff_cons, Int.cast_add, add_mul]
    rw [eval_cons, ih hcs, sum_congr rfl hsplit, sum_add_distrib,
      single_sum (hJ e List.mem_cons_self)]

/-- A variable outside the coefficient list has coefficient `0`. -/
theorem coeff_eq_zero {r : Ineq} {j : ℕ} (hj : ∀ e ∈ r.coeffs, e.1 ≠ j) : r.coeff j = 0 := by
  obtain ⟨cs, b⟩ := r
  induction cs with
  | nil => rfl
  | cons e cs ih =>
    have he : e.1 ≠ j := hj e List.mem_cons_self
    rw [coeff_cons, ih fun e' he' => hj e' (List.mem_cons_of_mem e he')]
    simp only [he, ↓reduceIte, add_zero]

end Ineq

namespace WRows

/-- **Weighted rows, variable by variable.** -/
theorem weighted_eval (rs : WRows) {J : Finset ℕ} (hJ : ∀ p ∈ rs, ∀ e ∈ p.2.coeffs, e.1 ∈ J)
    (x : ℕ → K) :
    (rs.map fun p => (p.1 : K) * p.2.eval x).sum = ∑ j ∈ J, (comb rs j : K) * x j := by
  induction rs with
  | nil => simp only [comb, List.map_nil, List.sum_nil, Int.cast_zero, zero_mul, sum_const_zero]
  | cons p rs ih =>
    have hsplit : ∀ j ∈ J, ((comb (p :: rs) j : ℤ) : K) * x j =
        (p.1 : K) * ((p.2.coeff j : K) * x j) + (comb rs j : K) * x j := by
      intro j _
      simp only [comb, List.map_cons, List.sum_cons, Int.cast_add, Int.cast_mul]
      ring
    rw [List.map_cons, List.sum_cons, ih fun q hq => hJ q (List.mem_cons_of_mem p hq),
      sum_congr rfl hsplit, sum_add_distrib, ← mul_sum,
      p.2.eval_eq_sum (hJ p List.mem_cons_self) x]

/-- The weighted left-hand sides of a solution are below the weighted bounds. -/
theorem weighted_le [LinearOrder K] [IsStrictOrderedRing K] (rs : WRows) (hy : ∀ p ∈ rs, 0 ≤ p.1) (x : ℕ → K)
    (hx : ∀ r ∈ system rs, r.Sat x) :
    (rs.map fun p => (p.1 : K) * p.2.eval x).sum ≤ (combB rs : K) := by
  have hle : ∀ p ∈ rs, (p.1 : K) * p.2.eval x ≤ (p.1 : K) * (p.2.bound : K) := fun p hp =>
    mul_le_mul_of_nonneg_left (hx p.2 (List.mem_map_of_mem hp)) (Int.cast_nonneg (hy p hp))
  have hcast : (combB rs : K) = (rs.map fun p => (p.1 : K) * (p.2.bound : K)).sum := by
    simp only [combB, Int.cast_list_sum, List.map_map, Function.comp_def, Int.cast_mul]
  rw [hcast]
  exact List.sum_le_sum hle

/-- **Soundness of Farkas certificates**: a system with a valid certificate has no solution
over any ordered field. -/
theorem IsCert.not_feasible [LinearOrder K] [IsStrictOrderedRing K] {rs : WRows} (h : IsCert rs) : ¬ Feasible K (system rs) := by
  rintro ⟨x, hx⟩
  let J : Finset ℕ := (support rs).toFinset
  have hJ : ∀ p ∈ rs, ∀ e ∈ p.2.coeffs, e.1 ∈ J := fun p hp e he =>
    List.mem_toFinset.2 (List.mem_flatMap.2 ⟨p, hp, List.mem_map_of_mem he⟩)
  have hzero : (rs.map fun p => (p.1 : K) * p.2.eval x).sum = 0 := by
    rw [weighted_eval rs hJ x]
    exact sum_eq_zero fun j _ => by rw [h.comb_zero j, Int.cast_zero, zero_mul]
  have hle := weighted_le rs h.nonneg x hx
  have hneg : (combB rs : K) < 0 := Int.cast_lt_zero.2 h.combB_neg
  rw [hzero] at hle
  exact absurd (hle.trans_lt hneg) (lt_irrefl 0)

/-- Variables outside the support have weighted coefficient `0`. -/
theorem comb_eq_zero_of_not_mem {rs : WRows} {j : ℕ} (hj : j ∉ support rs) : comb rs j = 0 := by
  have hc : ∀ p ∈ rs, p.1 * p.2.coeff j = 0 := by
    intro p hp
    have hne : ∀ e ∈ p.2.coeffs, e.1 ≠ j := fun e he hej =>
      hj (List.mem_flatMap.2 ⟨p, hp, List.mem_map.2 ⟨e, he, hej⟩⟩)
    rw [Ineq.coeff_eq_zero hne, mul_zero]
  exact List.sum_eq_zero fun z hz => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hz
    exact hc p hp

/-- **The executable check is sound.** -/
theorem check_sound {rs : WRows} (h : check rs = true) : IsCert rs := by
  simp only [check, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨hy, hs⟩, hb⟩ := h
  refine ⟨hy, fun j => ?_, hb⟩
  by_cases hj : j ∈ support rs
  · exact hs j hj
  · exact comb_eq_zero_of_not_mem hj

end WRows

theorem system_weigh {S : System} {y : List ℤ} (h : y.length = S.length) : (weigh S y).system = S := by
  simp only [WRows.system, weigh]
  exact List.map_snd_zip (h ▸ le_refl _)

/-- **Checked certificates refute the system** over every ordered field. -/
theorem checkCert_sound [LinearOrder K] [IsStrictOrderedRing K] {S : System} {y : List ℤ} (h : checkCert S y = true) : ¬ Feasible K S := by
  simp only [checkCert, Bool.and_eq_true, beq_iff_eq] at h
  have hc := (WRows.check_sound h.2).not_feasible (K := K)
  rwa [system_weigh h.1] at hc

/-! ## Streaming commands -/

namespace Cmd

theorem comb_row (rs : WRows) (y b : ℤ) (j : ℕ) : ((row y b).apply rs).comb j = rs.comb j := by
  simp only [apply, WRows.comb, List.map_cons, List.sum_cons, Ineq.coeff, List.map_nil,
    List.sum_nil, mul_zero, zero_add]

theorem combB_row (rs : WRows) (y b : ℤ) : ((row y b).apply rs).combB = y * b + rs.combB := by
  simp only [apply, WRows.combB, List.map_cons, List.sum_cons]

theorem comb_entry (y : ℤ) (r : Ineq) (rs : WRows) (j : ℕ) (a : ℤ) (k : ℕ) :
    ((entry j a).apply ((y, r) :: rs)).comb k =
      (if j = k then y * a else 0) + WRows.comb ((y, r) :: rs) k := by
  have hc : (⟨(j, a) :: r.coeffs, r.bound⟩ : Ineq).coeff k = (if j = k then a else 0) + r.coeff k :=
    Ineq.coeff_cons (j, a) r.coeffs r.bound k
  simp only [apply, WRows.comb, List.map_cons, List.sum_cons, hc]
  split <;> ring

theorem combB_entry (y : ℤ) (r : Ineq) (rs : WRows) (j : ℕ) (a : ℤ) :
    ((entry j a).apply ((y, r) :: rs)).combB = WRows.combB ((y, r) :: rs) := by
  simp only [apply, WRows.combB, List.map_cons, List.sum_cons]

theorem mults_row (rs : WRows) (y b : ℤ) : ∀ p ∈ (row y b).apply rs, p = (y, ⟨[], b⟩) ∨ p ∈ rs := by
  intro p hp
  simpa only [apply, List.mem_cons] using hp

theorem mults_entry (y : ℤ) (r : Ineq) (rs : WRows) (j : ℕ) (a : ℤ) :
    ∀ p ∈ (entry j a).apply ((y, r) :: rs), p.1 = y ∨ p ∈ rs := by
  intro p hp
  rcases List.mem_cons.1 hp with rfl | h
  · exact .inl rfl
  · exact .inr h

theorem apply_entry_nil (j : ℕ) (a : ℤ) : (entry j a).apply [] = [] := rfl

end Cmd

theorem load_append (cs : List Cmd) (c : Cmd) : load (cs ++ [c]) = c.apply (load cs) := by
  simp only [load, List.foldl_append, List.foldl_cons, List.foldl_nil]

end Silmaril.Logic.LinArith
