module

public import Silmaril.Proofs.Wasm.Wasmi.Observed.Nan
public import Silmaril.Numeric.Float.Wasm

/-!
# Which NaN inputs the rounding quirk disagrees on (proofs)

**The rounding functions on a NaN.** silmaril-lean's `roundIntegral` decodes its input with Lean's
core float model, which reads every NaN encoding as `notANumber` (`unpack_nan32`, from
silmaril-lean's `isNaN32` and `value_eq_notANumber_iff`), and packs `notANumber` as the positive
canonical NaN. So every rounding operator maps every NaN to `posNaN` (`round_nan`).

**The scalar disagreements.** Comparing wasmi 0.40.0's scalar result `wUnOp t op x` with the
results the profile allows for `t.op x`:

* `allowed_spec`: at the spec's NaN policy, the result is allowed unless `op` is a rounding
  operator and `x` is a signalling NaN (a NaN that is not arithmetic). On a quiet NaN the spec
  allows any arithmetic NaN (canonical for a canonical input, of either sign), so returning the
  input is allowed;
* `allowed_canonical`: at the canonical NaN policy (one deterministic result), the result is
  allowed unless `op` is a rounding operator and `x` is a NaN other than `posNaN`: the quirk
  also disagrees on quiet NaNs, for example `-nan`.

**The testsuite's inputs** (`nanIns_facts`, kernel evaluations): of the eight NaN inputs of the
rounding operators, the signalling ones are exactly `sNaNs`, and `posNaN` is among them.

New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Wasmi.Observed

open Silmaril.Numeric.Ieee754 Silmaril.Wasm Silmaril.Wasm.Numerics
open Float.Model Float.Model.UnpackedFloat
open Silmaril.Wasm.Wasmi.Observed

/-! ## The rounding functions on a NaN -/

theorem unpack_nan32 {F : F32} (hF : F.IsNaN) : F.model.unpack = .notANumber := by
  have hb : UnpackedFloat.unpack .binary32 F.bits.toBitVec = .notANumber := by
    have h := (Silmaril.Numeric.Float.isNaN32 F.bits.toBitVec).mp (by simpa [asF32] using hF)
    exact (Silmaril.Numeric.Float.Bits.value_eq_notANumber_iff _).mpr h
  change UnpackedFloat.unpack .binary32 (UnpackedFloat.pack .binary32
    (UnpackedFloat.unpack .binary32 F.bits.toBitVec)) = _
  rw [hb]
  exact (Silmaril.Numeric.Float.Bits.value_eq_notANumber_iff (fmt := .binary32) _).mpr
    (by decide +kernel)

theorem unpack_nan64 {F : F64} (hF : F.IsNaN) : F.model.unpack = .notANumber := by
  have hb : UnpackedFloat.unpack .binary64 F.bits.toBitVec = .notANumber := by
    have h := (Silmaril.Numeric.Float.isNaN64 F.bits.toBitVec).mp (by simpa [asF64] using hF)
    exact (Silmaril.Numeric.Float.Bits.value_eq_notANumber_iff _).mpr h
  change UnpackedFloat.unpack .binary64 (UnpackedFloat.pack .binary64
    (UnpackedFloat.unpack .binary64 F.bits.toBitVec)) = _
  rw [hb]
  exact (Silmaril.Numeric.Float.Bits.value_eq_notANumber_iff (fmt := .binary64) _).mpr
    (by decide +kernel)

theorem roundIntegral_nan32 (mode : RoundingMode) {F : F32} (hF : F.IsNaN) :
    F32.roundIntegral mode F = ⟨UInt32.ofBitVec (packedNaN .binary32)⟩ := by
  show (⟨UInt32.ofBitVec (Rounding.integralRounded .binary32 mode F.model.unpack)⟩ : F32) = _
  rw [unpack_nan32 hF]
  show (⟨UInt32.ofBitVec (Rounding.packRounded .binary32 mode .notANumber)⟩ : F32) = _
  rw [Rounding.packRounded_notANumber]

theorem roundIntegral_nan64 (mode : RoundingMode) {F : F64} (hF : F.IsNaN) :
    F64.roundIntegral mode F = ⟨UInt64.ofBitVec (packedNaN .binary64)⟩ := by
  show (⟨UInt64.ofBitVec (Rounding.integralRounded .binary64 mode F.model.unpack)⟩ : F64) = _
  rw [unpack_nan64 hF]
  show (⟨UInt64.ofBitVec (Rounding.packRounded .binary64 mode .notANumber)⟩ : F64) = _
  rw [Rounding.packRounded_notANumber]

theorem isNaN_of_B {t : FloatType} {x : FloatValue t} (hx : isNaNB t x = true) :
    match t, x with
    | .f32, x => (asF32 x).IsNaN
    | .f64, x => (asF64 x).IsNaN := by
  cases t <;> simpa [isNaNB, F32.isNaN, F64.isNaN] using hx

/-- **Every rounding operator maps every NaN to the positive canonical NaN.** -/
theorem round_nan {t : FloatType} {op : FloatUnOp} (hop : IsRound op = true) {x : FloatValue t}
    (hx : isNaNB t x = true) : floatUnOp t op x = posNaN t := by
  have hF := isNaN_of_B hx
  cases t with
  | f32 =>
    have h : ∀ mode, ((F32.roundIntegral mode (asF32 x)).bits.toBitVec : BitVec 32) =
        posNaN .f32 := fun mode => by
      rw [roundIntegral_nan32 mode hF]
      exact (by decide +kernel : (packedNaN .binary32 : BitVec 32) = 0x7fc00000#32)
    cases op <;> first | exact h _ | simp [IsRound] at hop
  | f64 =>
    have h : ∀ mode, ((F64.roundIntegral mode (asF64 x)).bits.toBitVec : BitVec 64) =
        posNaN .f64 := fun mode => by
      rw [roundIntegral_nan64 mode hF]
      exact (by decide +kernel : (packedNaN .binary64 : BitVec 64) = 0x7ff8000000000000#64)
    cases op <;> first | exact h _ | simp [IsRound] at hop

/-! ## The scalar disagreements -/

/-- The spec's relation at a rounding operator is the unary-result relation. -/
theorem rel_round32 {op : FloatUnOp} (hop : IsRound op = true) {x z : FloatValue .f32}
    (h : F32.unaryResult (floatUnOp32 op) (asF32 x) (asF32 z)) : floatUnOpRel .f32 op x z := by
  cases op <;> first | exact h | simp [IsRound] at hop

theorem rel_round64 {op : FloatUnOp} (hop : IsRound op = true) {x z : FloatValue .f64}
    (h : F64.unaryResult (floatUnOp64 op) (asF64 x) (asF64 z)) : floatUnOpRel .f64 op x z := by
  cases op <;> first | exact h | simp [IsRound] at hop

theorem self32 {e : F32 → F32} {F : F32} (he : (e F).IsNaN) (hF : F.IsNaN)
    (ha : F.IsArithmeticNaN) : F32.unaryResult e F F := by
  unfold F32.unaryResult
  rw [ite_eq_left he]
  split
  · rename_i hc
    rcases hc with hn | hc
    · exact absurd hF hn
    · exact hc
  · exact ha

theorem self64 {e : F64 → F64} {F : F64} (he : (e F).IsNaN) (hF : F.IsNaN)
    (ha : F.IsArithmeticNaN) : F64.unaryResult e F F := by
  unfold F64.unaryResult
  rw [ite_eq_left he]
  split
  · rename_i hc
    rcases hc with hn | hc
    · exact absurd hF hn
    · exact hc
  · exact ha

theorem quiet32 {op : FloatUnOp} (hop : IsRound op = true) {x : FloatValue .f32}
    (hx : isNaNB .f32 x = true) (hq : ¬ SNaN .f32 x) : floatUnOpRel .f32 op x x := by
  have hF : (asF32 x).IsNaN := isNaN_of_B hx
  have ha : (asF32 x).IsArithmeticNaN := Classical.byContradiction fun h => hq ⟨hF, h⟩
  have h : floatUnOp .f32 op x = posNaN .f32 := round_nan hop hx
  have he : (floatUnOp32 op (asF32 x)).IsNaN := by
    rw [← asF32_bits (floatUnOp32 op (asF32 x))]
    change (asF32 (floatUnOp .f32 op x)).IsNaN
    rw [h]
    decide +kernel
  exact rel_round32 hop (self32 he hF ha)

theorem quiet64 {op : FloatUnOp} (hop : IsRound op = true) {x : FloatValue .f64}
    (hx : isNaNB .f64 x = true) (hq : ¬ SNaN .f64 x) : floatUnOpRel .f64 op x x := by
  have hF : (asF64 x).IsNaN := isNaN_of_B hx
  have ha : (asF64 x).IsArithmeticNaN := Classical.byContradiction fun h => hq ⟨hF, h⟩
  have h : floatUnOp .f64 op x = posNaN .f64 := round_nan hop hx
  have he : (floatUnOp64 op (asF64 x)).IsNaN := by
    rw [← asF64_bits (floatUnOp64 op (asF64 x))]
    change (asF64 (floatUnOp .f64 op x)).IsNaN
    rw [h]
    decide +kernel
  exact rel_round64 hop (self64 he hF ha)

/-- At the spec's NaN policy, returning a quiet NaN input of a rounding operator is allowed. -/
theorem quiet_allowed {P : Profile} (hP : P.nan = .spec) {t : FloatType} {op : FloatUnOp}
    (hop : IsRound op = true) {x : FloatValue t} (hx : isNaNB t x = true) (hq : ¬ SNaN t x) :
    floatUnOpP P t op x x := by
  unfold floatUnOpP
  rw [hP]
  cases t with
  | f32 => exact quiet32 hop hx hq
  | f64 => exact quiet64 hop hx hq

/-- The deterministic result is allowed at every profile. -/
theorem floatUnOpP_self (P : Profile) (t : FloatType) (op : FloatUnOp) (x : FloatValue t) :
    floatUnOpP P t op x (floatUnOp t op x) := by
  unfold floatUnOpP
  cases P.nan with
  | spec => exact floatUnOpRel_self t op x
  | canonical => rfl

theorem snan_isNaN {t : FloatType} {x : FloatValue t} (h : SNaN t x) : isNaNB t x = true := by
  cases t <;> simpa [isNaNB, F32.isNaN, F64.isNaN] using h.1

/-- **At the spec's NaN policy, wasmi 0.40.0's result is allowed unless the operator rounds and
the input is a signalling NaN.** -/
theorem allowed_spec {P : Profile} (hP : P.nan = .spec) (t : FloatType) (op : FloatUnOp)
    (x : FloatValue t) :
    floatUnOpP P t op x (wUnOp t op x) ↔ ¬ (IsRound op = true ∧ SNaN t x) := by
  by_cases hq : IsRound op = true ∧ isNaNB t x = true
  · have hw : wUnOp t op x = x := by simp [wUnOp, hq.1, hq.2]
    rw [hw]
    constructor
    · rintro h ⟨-, hs⟩
      exact unOp_ne hq.1 hs h rfl
    · intro h
      exact quiet_allowed hP hq.1 hq.2 fun hs => h ⟨hq.1, hs⟩
  · have hw : wUnOp t op x = floatUnOp t op x := by
      unfold wUnOp
      rw [ite_eq_right (by simpa using hq)]
    rw [hw]
    exact iff_of_true (floatUnOpP_self P t op x) fun h => hq ⟨h.1, snan_isNaN h.2⟩

/-- **At the canonical NaN policy, wasmi 0.40.0's result is allowed unless the operator rounds
and the input is a NaN other than the positive canonical one.** -/
theorem allowed_canonical {P : Profile} (hP : P.nan = .canonical) (t : FloatType)
    (op : FloatUnOp) (x : FloatValue t) :
    floatUnOpP P t op x (wUnOp t op x) ↔
      ¬ (IsRound op = true ∧ isNaNB t x = true ∧ x ≠ posNaN t) := by
  unfold floatUnOpP
  rw [hP]
  by_cases hq : IsRound op = true ∧ isNaNB t x = true
  · have hw : wUnOp t op x = x := by simp [wUnOp, hq.1, hq.2]
    rw [hw, round_nan hq.1 hq.2]
    simp [hq.1, hq.2]
  · have hw : wUnOp t op x = floatUnOp t op x := by
      unfold wUnOp
      rw [ite_eq_right (by simpa using hq)]
    rw [hw]
    exact iff_of_true rfl fun h => hq ⟨h.1, h.2.1⟩

/-! ## The testsuite's NaN inputs -/

/-- Membership of a bit vector, read on its value. -/
theorem mem_toNat {w : Nat} {a : BitVec w} {l : List (BitVec w)} :
    a ∈ l ↔ a.toNat ∈ l.map BitVec.toNat := by
  refine ⟨List.mem_map_of_mem, fun h => ?_⟩
  obtain ⟨b, hb, he⟩ := List.mem_map.mp h
  rwa [BitVec.eq_of_toNat_eq he] at hb

theorem nanIns_facts32 (x : FloatValue .f32) (hx : x ∈ nanIns32) :
    isNaNB .f32 x = true ∧ (SNaN .f32 x ↔ x ∈ sNaN32) := by
  show isNaNB .f32 x = true ∧ (((asF32 x).IsNaN ∧ ¬ (asF32 x).IsArithmeticNaN) ↔
    (x : BitVec 32) ∈ (sNaN32 : List (BitVec 32)))
  rw [mem_toNat]
  rcases hx with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, hx⟩⟩⟩⟩
  any_goals decide +kernel
  cases hx

theorem nanIns_facts64 (x : FloatValue .f64) (hx : x ∈ nanIns64) :
    isNaNB .f64 x = true ∧ (SNaN .f64 x ↔ x ∈ sNaN64) := by
  show isNaNB .f64 x = true ∧ (((asF64 x).IsNaN ∧ ¬ (asF64 x).IsArithmeticNaN) ↔
    (x : BitVec 64) ∈ (sNaN64 : List (BitVec 64)))
  rw [mem_toNat]
  rcases hx with _ | ⟨_, _ | ⟨_, _ | ⟨_, _ | ⟨_, hx⟩⟩⟩⟩
  any_goals decide +kernel
  cases hx

/-- **The testsuite's NaN inputs are NaNs, and the signalling ones are `sNaNs`.** -/
theorem nanIns_facts {t : FloatType} {x : FloatValue t} (hx : x ∈ nanIns t) :
    isNaNB t x = true ∧ (SNaN t x ↔ x ∈ sNaNs t) := by
  cases t with
  | f32 => exact nanIns_facts32 x hx
  | f64 => exact nanIns_facts64 x hx

end Silmaril.Proofs.Wasm.Wasmi.Observed
