module

public import Silmaril.Wasm.Auto.ESeg.Defs
public import Silmaril.Wasm.Auto.EGraph.Thms

/-! # The second family of computed rewrites: shifts and comparisons

Every rewrite here keeps `Term.eval` for every operand, trapping or not, typed or not:
`shiftShift?_eval`, `cmpZero?_eval`, `signTest?_eval`. Divisibility, signed division and the
whole family (`comp2?_eval`) are in `Silmaril.Raw.Wasm.Auto.ESeg.Comp2`. The bitvector facts are
proved through `toNat` and `omega` (no `bv_decide`).
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.ESeg

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.ESeg
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
open Silmaril.Wasm.Auto.EGraph

/-! ## Operators on optional operands with constant right operands -/

/-- A comparison with a constant, as a map. -/
theorem relV_const (t : IntType) (op : IntRelOp) (a : Option Val) (y : BitVec t.width) :
    relV t op a (some (intVal t y)) =
      (a.bind (asInt t)).map fun x => Val.i32 (intRelOp t op x y) := by
  cases a with
  | none => rfl
  | some v => cases hv : asInt t v <;> simp [relV, hv]

/-- A non-trapping binary operator with a constant, as a map. -/
theorem binV_const_ok {t : IntType} {op : IntBinOp} {y : BitVec t.width}
    {g : BitVec t.width → BitVec t.width} (hg : ∀ x, intBinOp t op x y = .ok (g x))
    (a : Option Val) :
    binV t op a (some (intVal t y)) = (a.bind (asInt t)).map fun x => intVal t (g x) := by
  cases a with
  | none => rfl
  | some v => cases hv : asInt t v <;> simp [binV, hg, hv]

/-- Two maps over the integer read of the same operand agree pointwise. -/
theorem map_congr' {t : IntType} {g g' : BitVec t.width → Val} (a : Option Val)
    (h : ∀ x, g x = g' x) : (a.bind (asInt t)).map g = (a.bind (asInt t)).map g' := by
  cases a.bind (asInt t) <;> simp [h]

theorem toNat_ofNat_small {t : IntType} {n : Nat} (hn : n < t.width) :
    (BitVec.ofNat t.width n).toNat = n :=
  toNat_ofNat_lt hn

/-! ## Shifts of shifts -/

theorem shl_shl {t : IntType} {m n : Nat} (hm : m < t.width) (hn : n < t.width)
    (hmn : m + n < t.width) (x : BitVec t.width) :
    (x <<< ((BitVec.ofNat t.width m).toNat % t.width)) <<< ((BitVec.ofNat t.width n).toNat % t.width) =
      x <<< ((BitVec.ofNat t.width (m + n)).toNat % t.width) := by
  rw [toNat_ofNat_small hm, toNat_ofNat_small hn, toNat_ofNat_small hmn, Nat.mod_eq_of_lt hm,
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hmn, BitVec.shiftLeft_add]

theorem shr_shr {t : IntType} {m n : Nat} (hm : m < t.width) (hn : n < t.width)
    (hmn : m + n < t.width) (x : BitVec t.width) :
    (x >>> ((BitVec.ofNat t.width m).toNat % t.width)) >>> ((BitVec.ofNat t.width n).toNat % t.width) =
      x >>> ((BitVec.ofNat t.width (m + n)).toNat % t.width) := by
  rw [toNat_ofNat_small hm, toNat_ofNat_small hn, toNat_ofNat_small hmn, Nat.mod_eq_of_lt hm,
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hmn, BitVec.shiftRight_add]

theorem sar_sar {t : IntType} {m n : Nat} (hm : m < t.width) (hn : n < t.width)
    (hmn : m + n < t.width) (x : BitVec t.width) :
    (x.sshiftRight ((BitVec.ofNat t.width m).toNat % t.width)).sshiftRight
        ((BitVec.ofNat t.width n).toNat % t.width) =
      x.sshiftRight ((BitVec.ofNat t.width (m + n)).toNat % t.width) := by
  rw [toNat_ofNat_small hm, toNat_ofNat_small hn, toNat_ofNat_small hmn, Nat.mod_eq_of_lt hm,
    Nat.mod_eq_of_lt hn, Nat.mod_eq_of_lt hmn, BitVec.sshiftRight_add]

/-- The value of a shift of a shift by constants. -/
theorem eval_shift2 {f : Frame} {t : IntType} {op : IntBinOp} {a : Term} {m n : Nat}
    {g : Nat → BitVec t.width → BitVec t.width}
    (hg : ∀ c x, intBinOp t op x (BitVec.ofNat _ c) = .ok (g ((BitVec.ofNat t.width c).toNat % t.width) x))
    (hc : ∀ x, g n (g m x) = g (m + n) x) (hm : m < t.width) (hn : n < t.width)
    (hmn : m + n < t.width) :
    (Term.bin t op (.bin t op a (.const t m)) (.const t n)).eval f =
      (Term.bin t op a (.const t (m + n))).eval f := by
  have hm' : (BitVec.ofNat t.width m).toNat % t.width = m := by
    rw [toNat_ofNat_small hm, Nat.mod_eq_of_lt hm]
  have hn' : (BitVec.ofNat t.width n).toNat % t.width = n := by
    rw [toNat_ofNat_small hn, Nat.mod_eq_of_lt hn]
  have hmn' : (BitVec.ofNat t.width (m + n)).toNat % t.width = m + n := by
    rw [toNat_ofNat_small hmn, Nat.mod_eq_of_lt hmn]
  have h₁ : ∀ x, intBinOp t op x (BitVec.ofNat _ m) = .ok (g m x) := fun x => by
    rw [hg m x, hm']
  have h₂ : ∀ x, intBinOp t op x (BitVec.ofNat _ n) = .ok (g n x) := fun x => by
    rw [hg n x, hn']
  have h₃ : ∀ x, intBinOp t op x (BitVec.ofNat _ (m + n)) = .ok (g (m + n) x) := fun x => by
    rw [hg (m + n) x, hmn']
  simp only [Term.eval, binV_const_ok h₁, binV_const_ok h₂, binV_const_ok h₃]
  cases a.eval f with
  | none => rfl
  | some v => cases hv : asInt t v <;> simp [hv, hc]

theorem shiftShift?_eval {f : Frame} {a b : Term} (h : shiftShift? a = some b) :
    a.eval f = b.eval f := by
  unfold shiftShift? at h
  split at h
  · rename_i t op t' op' x t₁ m t₂ n
    split at h
    · rename_i hc
      obtain ⟨rfl, rfl, rfl, rfl, hm, hn, hmn, hop⟩ := hc
      cases h
      rcases hop with rfl | rfl | rfl
      · exact eval_shift2 (g := fun c x => x <<< c) (fun _ _ => rfl)
          (fun x => (BitVec.shiftLeft_add x m n).symm) hm hn hmn
      · exact eval_shift2 (g := fun c x => x >>> c) (fun _ _ => rfl)
          (fun x => (BitVec.shiftRight_add x m n).symm) hm hn hmn
      · exact eval_shift2 (g := fun c x => x.sshiftRight c) (fun _ _ => rfl)
          (fun x => BitVec.sshiftRight_add.symm) hm hn hmn
    · cases h
  · cases h

/-! ## Comparisons with `0` and `1` -/

theorem toNat_one (t : IntType) : (BitVec.ofNat t.width 1).toNat = 1 := by
  cases t <;> rfl

theorem toNat_zero' (t : IntType) : (BitVec.ofNat t.width 0).toNat = 0 := by
  cases t <;> rfl

theorem eq_zero_iff_toNat {w : Nat} (x : BitVec w) : x = 0 ↔ x.toNat = 0 := by
  constructor
  · intro h; simp [h]
  · intro h; exact BitVec.eq_of_toNat_eq (by simp [h])

theorem ltu_one (t : IntType) (x : BitVec t.width) :
    intRelOp t (.lt .unsigned) x (BitVec.ofNat _ 1) = intTestOp t .eqz x := by
  have hx : (x == 0) = decide (x.toNat < 1) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, eq_zero_iff_toNat]; omega
  simp only [intRelOp, intTestOp, toNat_one, hx]

theorem leu_zero (t : IntType) (x : BitVec t.width) :
    intRelOp t (.le .unsigned) x (BitVec.ofNat _ 0) = intTestOp t .eqz x := by
  have hx : (x == 0) = decide (x.toNat ≤ 0) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, decide_eq_true_iff, eq_zero_iff_toNat]; omega
  simp only [intRelOp, intTestOp, toNat_zero', hx]

theorem gtu_zero (t : IntType) (x : BitVec t.width) :
    intRelOp t (.gt .unsigned) x (BitVec.ofNat _ 0) = intRelOp t .ne x (BitVec.ofNat _ 0) := by
  have hx : (x != BitVec.ofNat _ 0) = decide (x.toNat > 0) := by
    have h0 : BitVec.ofNat t.width 0 = 0 := by simp
    rw [h0, Bool.eq_iff_iff, bne_iff_ne, decide_eq_true_iff, ne_eq, eq_zero_iff_toNat]; omega
  simp only [intRelOp, toNat_zero', hx]

theorem geu_one (t : IntType) (x : BitVec t.width) :
    intRelOp t (.ge .unsigned) x (BitVec.ofNat _ 1) = intRelOp t .ne x (BitVec.ofNat _ 0) := by
  have hx : (x != BitVec.ofNat _ 0) = decide (x.toNat ≥ 1) := by
    have h0 : BitVec.ofNat t.width 0 = 0 := by simp
    rw [h0, Bool.eq_iff_iff, bne_iff_ne, decide_eq_true_iff, ne_eq, eq_zero_iff_toNat]; omega
  simp only [intRelOp, toNat_one, hx]

theorem testV_eq_map (t : IntType) (a : Option Val) :
    testV t a = (a.bind (asInt t)).map fun x => Val.i32 (intTestOp t .eqz x) := rfl

theorem cmpZero?_eval {f : Frame} {a b : Term} (h : cmpZero? a = some b) :
    a.eval f = b.eval f := by
  unfold cmpZero? at h
  split at h <;> (try split at h) <;> cases h
  all_goals
    first
    | (rename_i ht; subst ht
       simp only [Term.eval, relV_const, testV_eq_map]
       exact map_congr' _ fun x => by
         first
         | rw [ltu_one] | rw [leu_zero] | rw [gtu_zero] | rw [geu_one])

/-! ## The sign test -/

theorem lts_zero_shr (x : BitVec 32) :
    intRelOp .i32 (.lt .signed) x (BitVec.ofNat 32 0) =
      x >>> ((BitVec.ofNat 32 31).toNat % 32) := by
  have hs : (BitVec.ofNat 32 31).toNat % 32 = 31 := rfl
  rw [hs]
  apply BitVec.eq_of_toNat_eq
  have hneg : x.toInt < 0 ↔ 2 ^ 31 ≤ x.toNat := by
    rw [BitVec.toInt_neg_iff]; omega
  have hlt : x.toNat < 2 ^ 32 := x.isLt
  rw [BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  simp only [intRelOp, bool32]
  split
  · rename_i hc
    have hc' : x.toInt < 0 := of_decide_eq_true hc
    have hd : x.toNat / 2 ^ 31 = 1 := by have := hneg.mp hc'; omega
    rw [hd]; rfl
  · rename_i hc
    have hc' : ¬ x.toInt < 0 := fun h => hc (decide_eq_true h)
    have hd : x.toNat / 2 ^ 31 = 0 := by
      have : ¬ 2 ^ 31 ≤ x.toNat := fun h => hc' (hneg.mpr h)
      omega
    rw [hd]; rfl

theorem signTest?_eval {f : Frame} {a b : Term} (h : signTest? a = some b) :
    a.eval f = b.eval f := by
  unfold signTest? at h
  split at h
  · rename_i x
    cases h
    have hok : ∀ z : BitVec IntType.i32.width, intBinOp .i32 (.shr .unsigned) z (BitVec.ofNat _ 31) =
        .ok (z >>> ((BitVec.ofNat 32 31).toNat % 32)) := fun _ => rfl
    simp only [Term.eval, relV_const, binV_const_ok hok]
    exact map_congr' _ fun z => by rw [i32_eq_intVal]; exact congrArg _ (lts_zero_shr z)
  · cases h

end Silmaril.Proofs.Wasm.Auto.ESeg