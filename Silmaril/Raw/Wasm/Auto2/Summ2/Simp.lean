module

public import Silmaril.Wasm.Auto2.Summ2.Defs
public import Silmaril.Wasm.Auto2.Summ.Thms

/-!
# The third simplifier preserves values (unrefined)

`evX_mkBin3`, `evX_simp3`, `evX_canon3`, `map_denX_slots3`: `simp3` and `canon3`
(`Silmaril.Wasm.Auto2.Summ2.Defs`) preserve the value of every value term at every type, in every
environment and initial memory.

New proofs (unrefined).
-/

@[expose] public section

namespace Silmaril.Wasm.Auto2.Summ2

open Silmaril.Wasm Silmaril.Wasm.Numerics
open Silmaril.Wasm.Auto.Equiv
open Silmaril.Wasm.Auto.Equiv (Env binV)
open Silmaril.Wasm.Auto2.Summ (pow2? evX_canon2)

variable {ρ : Env} {B0 : ByteArray}

theorem pow2?_spec {t : IntType} {c k : Nat} (h : pow2? t (.const c) = some k) :
    k < t.width ∧ c % 2 ^ t.width = 2 ^ k := by
  simp only [pow2?] at h
  split_ifs at h with hc
  cases h
  exact ⟨hc.2.1, hc.2.2.symm⟩

/-- `x rem_u 2^k = x and (2^k - 1)`. -/
theorem umod_pow2 {w k : Nat} (hk : k < w) (x : BitVec w) :
    x % BitVec.ofNat w (2 ^ k) = x &&& BitVec.ofNat w (2 ^ k - 1) := by
  have hp : 2 ^ k < 2 ^ w := Nat.pow_lt_pow_right (by decide) hk
  have hp0 : 0 < 2 ^ k := Nat.two_pow_pos k
  have hp1 : 2 ^ k - 1 < 2 ^ w := by omega
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_umod, BitVec.toNat_and, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hp,
    Nat.mod_eq_of_lt hp1, Nat.and_two_pow_sub_one_eq_mod]

theorem ofNat_mod_pow (w c : Nat) : BitVec.ofNat w (c % 2 ^ w) = BitVec.ofNat w c := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofNat]

/-- A count reduced modulo the width. -/
theorem count_mod {t : IntType} {op : IntBinOp} (hop : countOp op = true) (x : BitVec t.width)
    (c : Nat) :
    binV t op x (BitVec.ofNat t.width (c % 2 ^ t.width % t.width)) =
      binV t op x (BitVec.ofNat t.width c) := by
  have hw : 0 < t.width := by cases t <;> decide
  have hlt : c % 2 ^ t.width % t.width < 2 ^ t.width :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ hw) (Nat.le_of_lt (Nat.lt_two_pow_self))
  have hn : (BitVec.ofNat t.width (c % 2 ^ t.width % t.width)).toNat =
      (BitVec.ofNat t.width c).toNat % t.width := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, BitVec.toNat_ofNat]
  cases op <;> simp only [countOp, Bool.false_eq_true] at hop
  · simp only [binV, intBinOp, hn, Nat.mod_mod]
  · rename_i s
    cases s <;> simp only [binV, intBinOp, hn, Nat.mod_mod]
  · simp only [binV, intBinOp, hn, BitVec.rotateLeft_mod_eq_rotateLeft]
  · simp only [binV, intBinOp, hn, BitVec.rotateRight_mod_eq_rotateRight]

theorem evX_mkBin3 (t : IntType) (op : IntBinOp) (a b : XT) :
    evX ρ B0 t (mkBin3 t op a b) = evX ρ B0 t (.bin op a b) := by
  unfold mkBin3
  split
  · rename_i c
    split
    · rename_i hop
      subst hop
      split
      · rename_i k hk
        obtain ⟨hk, hc⟩ := pow2?_spec hk
        simp only [evX, binV, intBinOp]
        have hne : BitVec.ofNat t.width c ≠ 0 := by
          intro h0
          have := congrArg BitVec.toNat h0
          rw [BitVec.toNat_ofNat, hc] at this
          simp at this
        simp only [hne, ↓reduceIte]
        rw [← ofNat_mod_pow t.width c, hc, umod_pow2 hk]
      · rfl
    · split
      · rename_i _ hop
        simp only [evX]
        exact count_mod hop _ c
      · rfl
  · rfl

/-- **The third simplifier preserves values.** -/
theorem evX_simp3 : ∀ (e : XT) (t : IntType), evX ρ B0 t (simp3 t e) = evX ρ B0 t e := by
  intro e
  induction e with
  | un op a ih => intro t; simp only [simp3, evX, ih]
  | bin op a b iha ihb => intro t; rw [simp3, evX_mkBin3]; simp only [evX, iha, ihb]
  | rel t' op a b iha ihb => intro t; simp only [simp3, evX, iha, ihb]
  | wrap a ih => intro t; simp only [simp3, evX, ih]
  | ext sx a ih => intro t; simp only [simp3, evX, ih]
  | sel c a b ihc iha ihb => intro t; simp only [simp3, evX, ihc, iha, ihb]
  | var n => intro t; rfl
  | const c => intro t; rfl
  | load m t' p a arg _ _ => intro t; rfl
  | minit => intro t; rfl
  | mstore m t' p a arg v _ _ _ => intro t; rfl

/-- **The simplifier  preserves values.** -/
theorem evX_canon3 (t : IntType) (e : XT) : evX ρ B0 t (canon3 t e) = evX ρ B0 t e := by
  rw [canon3, evX_canon, evX_simp3, evX_canon2]

theorem map_denX_slots3 (ρ : Env) (B0 : ByteArray) (l : List (IntType × XT)) :
    (slots3 l).map (denX ρ B0) = l.map (denX ρ B0) := by
  simp [slots3, denX, evX_canon3]

end Silmaril.Wasm.Auto2.Summ2
