module

public import Silmaril.Proofs.Wasm.Component.Reference.FloatABI

/-!
# Floats in variant payloads: the slot coercions

The first step toward floats in variant payloads (`Silmaril.Proofs.Wasm.Component.Reference`,
`docs/projects/wasm-components.md`, **Not done**). A float payload slot of a variant is lowered by
`lowerFlatAt` (`lowerFloat`, C7) and then re-encoded by `coerceLower` into its joined slot. When
the joined slot is an integer, `coerceLower` calls `encodeFloat`, which issues a **second** C7
choice on the already-chosen NaN; the IR re-types the float's bits (`Flat.retype`). Lifting
decodes the slot with `coerceLiftFlat` (`decodeFloat`, which canonicalises), where the IR
re-types the bits back.

* `coerceLower_float`: the coercion of a float slot `x` into an integer slot is a choice program
  whose results are the IR re-typing of some admissible lowering `y` of `x` (`NanLower prof`);
* `coerceLiftFlat_float`: decoding the re-typed bits of `y` is the canonicalisation of `y`;
* `nanLower₂_deterministic`: under the deterministic profile two lowerings in a row are one
  canonicalisation (`canonicalizeNaN_idem`).

Hence a float in a variant payload is lowered by one or two `NanLower` steps (two when its
joined slot is an integer; at most two at any nesting depth, since an encoded float is an
integer afterwards) and lifted canonicalised.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Component.Reference

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Component Silmaril.Wasm.Component.Canon Silmaril.Wasm.Component.ABI
open Silmaril.Wasm.Component.Value (NanLower)
open Silmaril.Wasm (FloatType IntType NumType)

variable {E : Silmaril.Wasm.Component.Engine.CoreEngine} {σ : Type}

/-- The float-to-integer entries of the `(have, want)` table of `lower_flat_variant`. -/
def FloatSlot : FloatType → IntType → Prop
  | .f32, .i32 | .f32, .i64 | .f64, .i64 => True
  | _, _ => False

/-- Canonicalisation is idempotent. -/
theorem canonicalizeNaN_idem (t : FloatType) (x : BitVec t.width) :
    canonicalizeNaN t (canonicalizeNaN t x) = canonicalizeNaN t x := by
  unfold canonicalizeNaN
  cases h : isNaN t x
  · simp only [h, Bool.false_eq_true, ↓reduceIte]
  · have hc : isNaN t (canonicalNaN t) = true := by cases t <;> rfl
    simp only [hc, ↓reduceIte]

/-- **Two lowerings in a row under the deterministic profile** are one canonicalisation. -/
theorem nanLower₂_deterministic {t : FloatType} {x y z : BitVec t.width}
    (h₁ : NanLower .deterministic t x y) (h₂ : NanLower .deterministic t y z) :
    z = canonicalizeNaN t x := by
  rw [nanLower_deterministic h₂, nanLower_deterministic h₁, canonicalizeNaN_idem]

theorem wrapI64ToI32_f32 (x : BitVec FloatType.f32.width) :
    wrapI64ToI32 (.float .f32 x) = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [wrapI64ToI32, Silmaril.Wasm.Execution.Runtime.Value.float, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt x.isLt

theorem flatBits64_f64 (x : BitVec FloatType.f64.width) : flatBits64 (.float .f64 x) = x := by
  apply BitVec.eq_of_toNat_eq
  simp only [flatBits64, Silmaril.Wasm.Execution.Runtime.Value.float, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt x.isLt

theorem retype_f32_i32 (y : BitVec FloatType.f32.width) :
    Flat.retype (.int .i32) (.float .f32 y) = .int .i32 (reinterpretFloatAsInt .f32 y) := by
  show (⟨.int .i32, BitVec.setWidth 32 y⟩ : Flat) = ⟨.int .i32, _⟩
  congr 1

theorem retype_f32_i64 (y : BitVec FloatType.f32.width) :
    Flat.retype (.int .i64) (.float .f32 y) =
      .int .i64 ((reinterpretFloatAsInt .f32 y).setWidth 64) := by
  show (⟨.int .i64, BitVec.setWidth 64 y⟩ : Flat) = ⟨.int .i64, _⟩
  congr 1

theorem retype_f64_i64 (y : BitVec FloatType.f64.width) :
    Flat.retype (.int .i64) (.float .f64 y) = .int .i64 (reinterpretFloatAsInt .f64 y) := by
  show (⟨.int .i64, BitVec.setWidth 64 y⟩ : Flat) = ⟨.int .i64, _⟩
  congr 1

/-- **The coercion of a float slot into an integer slot** chooses an admissible lowering and
re-types its bits, as the IR does. -/
theorem coerceLower_float (prof : ProfileKind) {t : FloatType} {w : IntType} (hs : FloatSlot t w)
    (x : BitVec t.width) :
    ChoiceProg prof (fun out => ∃ y, NanLower prof t x y ∧
        out = Flat.retype (.int w) (.float t y))
      (coerceLower (.float t) (.int w) (.float t x) : P E σ Flat) := by
  match t, w, hs with
  | .f32, .i32, _ =>
    have e : (coerceLower (.float .f32) (.int .i32) (.float .f32 x) : P E σ Flat) =
        lowerFloat .f32 x >>= fun y => pure (Flat.retype (.int .i32) (.float .f32 y)) := by
      simp only [coerceLower, encodeFloat, wrapI64ToI32_f32, bind_assoc, pure_bind,
        retype_f32_i32]
    rw [e]
    exact (lowerFloat_choice prof .f32 x).bind fun y hy => .pure ⟨y, hy, rfl⟩
  | .f32, .i64, _ =>
    have e : (coerceLower (.float .f32) (.int .i64) (.float .f32 x) : P E σ Flat) =
        lowerFloat .f32 x >>= fun y => pure (Flat.retype (.int .i64) (.float .f32 y)) := by
      simp only [coerceLower, encodeFloat, wrapI64ToI32_f32, bind_assoc, pure_bind,
        retype_f32_i64]
    rw [e]
    exact (lowerFloat_choice prof .f32 x).bind fun y hy => .pure ⟨y, hy, rfl⟩
  | .f64, .i64, _ =>
    have e : (coerceLower (.float .f64) (.int .i64) (.float .f64 x) : P E σ Flat) =
        lowerFloat .f64 x >>= fun y => pure (Flat.retype (.int .i64) (.float .f64 y)) := by
      simp only [coerceLower, encodeFloat, flatBits64_f64, bind_assoc, pure_bind,
        retype_f64_i64]
    rw [e]
    exact (lowerFloat_choice prof .f64 x).bind fun y hy => .pure ⟨y, hy, rfl⟩

theorem roundtrip_f32_i32 (y : BitVec FloatType.f32.width) :
    reinterpretIntAsFloat .f32 (BitVec.ofNat 32 (reinterpretFloatAsInt .f32 y).toNat) = y := by
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat 32 y.toNat).toNat = y.toNat
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt y.isLt

theorem roundtrip_f32_i64 (y : BitVec FloatType.f32.width) :
    reinterpretIntAsFloat .f32
      (BitVec.ofNat 32 ((reinterpretFloatAsInt .f32 y).setWidth 64).toNat) = y := by
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat 32 ((reinterpretFloatAsInt .f32 y).setWidth 64).toNat).toNat = y.toNat
  have h : y.toNat < 2 ^ 32 := y.isLt
  rw [BitVec.toNat_ofNat, BitVec.toNat_setWidth]
  show y.toNat % 2 ^ 64 % 2 ^ 32 = y.toNat
  rw [Nat.mod_eq_of_lt (by omega : y.toNat < 2 ^ 64), Nat.mod_eq_of_lt h]

theorem roundtrip_f64_i64 (y : BitVec FloatType.f64.width) :
    reinterpretIntAsFloat .f64 (BitVec.ofNat 64 (reinterpretFloatAsInt .f64 y).toNat) = y := by
  apply BitVec.eq_of_toNat_eq
  show (BitVec.ofNat 64 y.toNat).toNat = y.toNat
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt y.isLt

/-- **Decoding a re-typed float slot** canonicalises the float. -/
theorem coerceLiftFlat_float {t : FloatType} {w : IntType} (hs : FloatSlot t w)
    (y : BitVec t.width) :
    coerceLiftFlat (.int w) (.float t) (Flat.retype (.int w) (.float t y)) =
      .float t (canonicalizeNaN t y) := by
  match t, w, hs with
  | .f32, .i32, _ =>
    rw [retype_f32_i32]
    show Silmaril.Wasm.Execution.Runtime.Value.float .f32 (canonicalizeNaN .f32
      (reinterpretIntAsFloat .f32 (BitVec.ofNat 32 (reinterpretFloatAsInt .f32 y).toNat))) = _
    rw [roundtrip_f32_i32]
  | .f32, .i64, _ =>
    rw [retype_f32_i64]
    show Silmaril.Wasm.Execution.Runtime.Value.float .f32 (canonicalizeNaN .f32
      (reinterpretIntAsFloat .f32
        (BitVec.ofNat 32 ((reinterpretFloatAsInt .f32 y).setWidth 64).toNat))) = _
    rw [roundtrip_f32_i64]
  | .f64, .i64, _ =>
    rw [retype_f64_i64]
    show Silmaril.Wasm.Execution.Runtime.Value.float .f64 (canonicalizeNaN .f64
      (reinterpretIntAsFloat .f64 (BitVec.ofNat 64 (reinterpretFloatAsInt .f64 y).toNat))) = _
    rw [roundtrip_f64_i64]

end Silmaril.Proofs.Wasm.Component.Reference
