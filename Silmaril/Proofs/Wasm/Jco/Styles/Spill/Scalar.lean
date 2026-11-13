module

public import Silmaril.Wasm.Jco.Styles.Spill.Defs
public import Silmaril.Proofs.Wasm.Jco.Styles.Wide.Scalar

/-!
# Spilled parameters: the scalar roundtrip

**`loadVal_store`**: loading a scalar field with the shim's load (sign-extended for `s8`/`s16`)
from the stored bytes of its flat lowering gives back the flat lowering. New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Jco

open Silmaril.Wasm.Jco
open Silmaril.Wasm.Component (Flat ValTy Val)

theorem setWidth_signExtend {w : Nat} (hw : w ≤ 32) (x : BitVec w) :
    (x.signExtend 32).setWidth w = x := by
  ext i hi
  rw [BitVec.getElem_setWidth, BitVec.getLsbD_signExtend]
  simp [hi, (by omega : i < 32)]

theorem mk_i32 {a : BitVec 32} (b : BitVec 32) (h : a = b) : (⟨.int .i32, a⟩ : Flat) = Flat.i32 b := by
  rw [h]

theorem mk_i64 {a : BitVec 64} (b : BitVec 64) (h : a = b) : (⟨.int .i64, a⟩ : Flat) = Flat.i64 b := by
  rw [h]

theorem mk_f32 {a : BitVec 32} (b : BitVec 32) (h : a = b) :
    (⟨.float .f32, a⟩ : Flat) = ⟨.float .f32, b⟩ := by rw [h]

theorem mk_f64 {a : BitVec 64} (b : BitVec 64) (h : a = b) :
    (⟨.float .f64, a⟩ : Flat) = ⟨.float .f64, b⟩ := by rw [h]

theorem ofNat_mod_self {w : Nat} (x : BitVec w) : BitVec.ofNat w (x.toNat % 2 ^ w) = x := by
  rw [Nat.mod_eq_of_lt x.isLt, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem zext_roundtrip {w : Nat} (hw : w ≤ 32) (x : BitVec w) :
    BitVec.ofNat 32 ((x.setWidth 32).toNat % 2 ^ w) = x.setWidth 32 := by
  apply BitVec.eq_of_toNat_eq
  have hx := x.isLt
  have hp : 2 ^ w ≤ 2 ^ 32 := Nat.pow_le_pow_right (by decide) hw
  simp only [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  rw [Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 32), Nat.mod_eq_of_lt hx,
    Nat.mod_eq_of_lt (by omega : x.toNat < 2 ^ 32)]

theorem sext_roundtrip {w : Nat} (hw : w ≤ 32) (x : BitVec w) :
    (BitVec.ofNat w ((x.signExtend 32).toNat % 2 ^ w)).signExtend 32 = x.signExtend 32 := by
  rw [ofNat_mod_toNat _ _ (Nat.dvd_refl _), setWidth_signExtend hw]

theorem lower_scalar {t : ValTy} {n : Nat} (ht : scalarSize t = some n) {v : Val}
    (hv : t.check v = true) : ∃ r, t.lower v = [r] ∧ t.flat = [r.type] := by
  cases t <;> simp [scalarSize] at ht <;> cases v <;> simp [ValTy.check] at hv <;>
    exact ⟨_, rfl, rfl⟩

/-- **Loading a stored scalar parameter gives back its flat lowering.** -/
theorem loadVal_store {t : ValTy} {n : Nat} (ht : scalarSize t = some n) {v : Val}
    (hv : t.check v = true) {r : Flat} (hr : t.lower v = [r]) :
    loadVal (t.flat.headD (.int .i32)) n (signedTy t)
      (leBytes n (normField t r).bits.toNat) = r := by
  cases t <;> simp [scalarSize] at ht <;> subst ht <;> cases v <;> simp [ValTy.check] at hv <;>
    simp [ValTy.lower] at hr <;> subst hr <;>
    simp [loadVal, normField, asI32?, signedTy, leNat_leBytes, ValTy.flat]
  case bool.bool b =>
    exact mk_i32 _ (by cases b <;> rfl)
  case s8.s8 x => exact mk_i32 _ (sext_roundtrip (w := 8) (by decide) x)
  case s16.s16 x => exact mk_i32 _ (sext_roundtrip (w := 16) (by decide) x)
  case u8.u8 x => exact mk_i32 _ (zext_roundtrip (w := 8) (by decide) x)
  case u16.u16 x => exact mk_i32 _ (zext_roundtrip (w := 16) (by decide) x)
  case s32.s32 x => exact mk_i32 _ (ofNat_mod_self (w := 32) x)
  case u32.u32 x => exact mk_i32 _ (ofNat_mod_self (w := 32) x)
  case s64.s64 x => exact mk_i64 _ (ofNat_mod_self (w := 64) x)
  case u64.u64 x => exact mk_i64 _ (ofNat_mod_self (w := 64) x)
  case f32.f32 x => exact mk_f32 _ (ofNat_mod_self (w := 32) x)
  case f64.f64 x => exact mk_f64 _ (ofNat_mod_self (w := 64) x)
  case char.char c => exact mk_i32 _ (ofNat_mod_self (w := 32) c.val.toBitVec)

end Silmaril.Proofs.Wasm.Jco
