module

public import Silmaril.Proofs.Wasm.Auto.EGraph.Sound

/-! # Computed rewrites keep the value

`comp?_eval`: `Term.comp?` (powers of two as shifts and masks, shift counts modulo the width)
keeps `Term.eval` for every operand, trapping or not, typed or not.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Auto.EGraph

open Silmaril.Wasm Silmaril.Wasm.Auto Silmaril.Wasm.Auto.EGraph
open Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics

/-- Two binary operators with constant right operands that agree on every left operand. -/
theorem binV_congr {t : IntType} {op op' : IntBinOp} {y y' : BitVec t.width} (a : Option Val)
    (h : ∀ x, intBinOp t op x y = intBinOp t op' x y') :
    binV t op a (some (intVal t y)) = binV t op' a (some (intVal t y')) := by
  cases a with
  | none => rfl
  | some v =>
    cases hx : asInt t v with
    | none => simp [binV, hx]
    | some x => simp [binV, hx, h x]

theorem pow2Exp?_spec {w n k : Nat} (h : pow2Exp? w n = some k) : k < w ∧ 2 ^ k = n := by
  have h' := List.find?_some h
  have hm : k ∈ List.range w := List.mem_of_find?_eq_some h
  exact ⟨List.mem_range.mp hm, by simpa using h'⟩

theorem toNat_ofNat_lt {w k : Nat} (hk : k < w) : (BitVec.ofNat w k).toNat = k := by
  have : k < 2 ^ w := Nat.lt_of_lt_of_le hk (Nat.le_of_lt (Nat.lt_two_pow_self))
  simp [Nat.mod_eq_of_lt this]

theorem toNat_ofNat_pow {w k : Nat} (hk : k < w) : (BitVec.ofNat w (2 ^ k)).toNat = 2 ^ k := by
  have hlt : 2 ^ k < 2 ^ w := Nat.pow_lt_pow_right (by decide : 1 < 2) hk
  simp [Nat.mod_eq_of_lt hlt]

theorem mul_pow2 {w k : Nat} (hk : k < w) (x : BitVec w) :
    x * BitVec.ofNat w (2 ^ k) = x <<< ((BitVec.ofNat w k).toNat % w) := by
  rw [toNat_ofNat_lt hk, Nat.mod_eq_of_lt hk]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_mul, toNat_ofNat_pow hk, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]

theorem udiv_pow2 {w k : Nat} (hk : k < w) (x : BitVec w) :
    x / BitVec.ofNat w (2 ^ k) = x >>> ((BitVec.ofNat w k).toNat % w) := by
  rw [toNat_ofNat_lt hk, Nat.mod_eq_of_lt hk]
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_udiv, toNat_ofNat_pow hk, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]

theorem umod_pow2 {w k : Nat} (hk : k < w) (x : BitVec w) :
    x % BitVec.ofNat w (2 ^ k) = x &&& BitVec.ofNat w (2 ^ k - 1) := by
  apply BitVec.eq_of_toNat_eq
  have hlt : 2 ^ k - 1 < 2 ^ w :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) (Nat.pow_lt_pow_right (by decide : 1 < 2) hk)
  simp [BitVec.toNat_umod, toNat_ofNat_pow hk, BitVec.toNat_and, Nat.mod_eq_of_lt hlt,
    Nat.and_two_pow_sub_one_eq_mod]

theorem pow2_ne_zero {w k : Nat} (hk : k < w) : BitVec.ofNat w (2 ^ k) ≠ 0 := by
  intro h
  have := congrArg BitVec.toNat h
  simp [toNat_ofNat_pow hk] at this

/-- Shift counts modulo the width (`w` divides `2 ^ w` for both integer types). -/
theorem count_mod (t : IntType) (n : Nat) :
    (BitVec.ofNat t.width n).toNat % t.width =
      (BitVec.ofNat t.width (n % t.width)).toNat % t.width := by
  have hd : t.width ∣ 2 ^ t.width := by cases t <;> decide
  have hl : n % t.width < 2 ^ t.width :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (by cases t <;> decide)) (by cases t <;> decide)
  simp [Nat.mod_mod_of_dvd _ hd, Nat.mod_eq_of_lt hl]

theorem intBinOp_mul_pow2 {t : IntType} {k : Nat} (hk : k < t.width) (x : BitVec t.width) :
    intBinOp t .mul x (BitVec.ofNat _ (2 ^ k)) = intBinOp t .shl x (BitVec.ofNat _ k) := by
  simp only [intBinOp, mul_pow2 hk]

theorem intBinOp_divu_pow2 {t : IntType} {k : Nat} (hk : k < t.width) (x : BitVec t.width) :
    intBinOp t (.div .unsigned) x (BitVec.ofNat _ (2 ^ k)) =
      intBinOp t (.shr .unsigned) x (BitVec.ofNat _ k) := by
  simp only [intBinOp, pow2_ne_zero hk, ↓reduceIte, udiv_pow2 hk]

theorem intBinOp_remu_pow2 {t : IntType} {k : Nat} (hk : k < t.width) (x : BitVec t.width) :
    intBinOp t (.rem .unsigned) x (BitVec.ofNat _ (2 ^ k)) =
      intBinOp t .and x (BitVec.ofNat _ (2 ^ k - 1)) := by
  simp only [intBinOp, pow2_ne_zero hk, ↓reduceIte, umod_pow2 hk]

theorem intBinOp_count_mod {t : IntType} {op : IntBinOp}
    (hop : op = .shl ∨ (∃ s, op = .shr s) ∨ op = .rotl ∨ op = .rotr) (n : Nat)
    (x : BitVec t.width) :
    intBinOp t op x (BitVec.ofNat _ n) = intBinOp t op x (BitVec.ofNat _ (n % t.width)) := by
  rcases hop with rfl | ⟨s, rfl⟩ | rfl | rfl
  · simp only [intBinOp, count_mod t n]
  · cases s <;> simp only [intBinOp, count_mod t n]
  · simp only [intBinOp]
    rw [← BitVec.rotateLeft_mod_eq_rotateLeft (r := (BitVec.ofNat _ n).toNat), count_mod t n,
      BitVec.rotateLeft_mod_eq_rotateLeft]
  · simp only [intBinOp]
    rw [← BitVec.rotateRight_mod_eq_rotateRight (r := (BitVec.ofNat _ n).toNat), count_mod t n,
      BitVec.rotateRight_mod_eq_rotateRight]

theorem comp_mul_eval {f : Frame} {t : IntType} {x b : Term} {n : Nat}
    (h : (pow2Exp? t.width n).map (fun k => Term.bin t .shl x (.const t k)) = some b) :
    (Term.bin t .mul x (.const t n)).eval f = b.eval f := by
  obtain ⟨k, hk, hb⟩ : ∃ k, pow2Exp? t.width n = some k ∧
      Term.bin t .shl x (.const t k) = b := Option.map_eq_some_iff.mp h
  obtain ⟨hlt, hn⟩ : k < t.width ∧ 2 ^ k = n := pow2Exp?_spec hk
  rw [← hb, ← hn]
  exact binV_congr _ (intBinOp_mul_pow2 hlt)

theorem comp_divu_eval {f : Frame} {t : IntType} {x b : Term} {n : Nat}
    (h : (pow2Exp? t.width n).map (fun k => Term.bin t (.shr .unsigned) x (.const t k)) =
      some b) :
    (Term.bin t (.div .unsigned) x (.const t n)).eval f = b.eval f := by
  obtain ⟨k, hk, hb⟩ : ∃ k, pow2Exp? t.width n = some k ∧
      Term.bin t (.shr .unsigned) x (.const t k) = b := Option.map_eq_some_iff.mp h
  obtain ⟨hlt, hn⟩ : k < t.width ∧ 2 ^ k = n := pow2Exp?_spec hk
  rw [← hb, ← hn]
  exact binV_congr _ (intBinOp_divu_pow2 hlt)

theorem comp_remu_eval {f : Frame} {t : IntType} {x b : Term} {n : Nat}
    (h : (pow2Exp? t.width n).map (fun _ => Term.bin t .and x (.const t (n - 1))) = some b) :
    (Term.bin t (.rem .unsigned) x (.const t n)).eval f = b.eval f := by
  obtain ⟨k, hk, hb⟩ : ∃ k, pow2Exp? t.width n = some k ∧
      Term.bin t .and x (.const t (n - 1)) = b := Option.map_eq_some_iff.mp h
  obtain ⟨hlt, hn⟩ : k < t.width ∧ 2 ^ k = n := pow2Exp?_spec hk
  rw [← hb, ← hn]
  exact binV_congr _ (intBinOp_remu_pow2 hlt)

theorem comp_count_eval {f : Frame} {t : IntType} {op : IntBinOp} {x b : Term} {n : Nat}
    (hop : op = .shl ∨ (∃ s, op = .shr s) ∨ op = .rotl ∨ op = .rotr)
    (h : (if t.width ≤ n then some (Term.bin t op x (.const t (n % t.width))) else none) =
      some b) :
    (Term.bin t op x (.const t n)).eval f = b.eval f := by
  split at h
  · cases h
    exact binV_congr _ (intBinOp_count_mod hop n)
  · cases h

/-- **Computed rewrites keep the value.** -/
theorem comp?_eval {f : Frame} {a b : Term} (h : a.comp? = some b) : a.eval f = b.eval f := by
  unfold Term.comp? at h
  split at h
  · split at h
    · rename_i ht
      subst ht
      split at h
      · exact comp_mul_eval h
      · exact comp_divu_eval h
      · exact comp_remu_eval h
      all_goals first | cases h | exact comp_count_eval (by simp) h
    · cases h
  · cases h

end Silmaril.Proofs.Wasm.Auto.EGraph