module

public import Silmaril.Wasm.Wasmi.Observed.Defs
public import Silmaril.Numeric.Ieee754.Relations

/-!
# Signalling NaNs and the rounding operators (proofs)

For a NaN input that is not an arithmetic NaN (a signalling NaN), no result the spec allows for
a rounding operator equals the input, at either NaN policy (`unOp_ne`): the spec's results are
the correctly rounded value when it is not a NaN, and otherwise an arithmetic (or canonical) NaN;
the deterministic result is non-NaN or canonical. The proof never evaluates the rounding
functions: it uses only that their results are non-NaN or canonical
(`roundIntegral_isCanonicalized`).

For a quiet NaN input, returning the input is allowed (`wUnOp_quiet`): this is why only the
signalling inputs of the testsuite fail.

The NaN classes of the testsuite's eight inputs are kernel evaluations of the bit-level
classifiers (`sNaN_facts`). New proofs.
-/

@[expose] public section

namespace Silmaril.Proofs.Wasm.Wasmi.Observed

open Silmaril.Numeric.Ieee754 Silmaril.Wasm Silmaril.Wasm.Numerics
open Silmaril.Wasm.Wasmi.Observed

/-! ## Binary32 -/

theorem not_unaryResult32 {e : F32 → F32} {F : F32} (_he : (e F).IsNonNaNOrCanonicalNaN)
    (hF : F.IsNaN) (hna : ¬ F.IsArithmeticNaN) : ¬ F32.unaryResult e F F := by
  unfold F32.unaryResult
  split
  · split
    · rename_i hc
      exact fun h => hna h.isArithmeticNaN
    · exact fun h => hna h
  · rename_i hn
    intro h
    exact hn (h ▸ hF)

theorem eval_ne32 {e : F32 → F32} {F : F32} (he : (e F).IsNonNaNOrCanonicalNaN)
    (hF : F.IsNaN) (hna : ¬ F.IsArithmeticNaN) : e F ≠ F := by
  intro h
  rw [h] at he
  rcases he with hn | hc
  · exact hn hF
  · exact hna hc.isArithmeticNaN

theorem round32_canon {op : FloatUnOp} (hop : IsRound op = true) (F : F32) :
    (floatUnOp32 op F).IsNonNaNOrCanonicalNaN := by
  cases op with
  | floor => exact F32.roundIntegral_isCanonicalized .towardNegative F
  | ceil => exact F32.roundIntegral_isCanonicalized .towardPositive F
  | trunc => exact F32.roundIntegral_isCanonicalized .towardZero F
  | nearest => exact F32.roundIntegral_isCanonicalized .nearestTiesToEven F
  | _ => simp [IsRound] at hop

/-! ## Binary64 -/

theorem not_unaryResult64 {e : F64 → F64} {F : F64} (_he : (e F).IsNonNaNOrCanonicalNaN)
    (hF : F.IsNaN) (hna : ¬ F.IsArithmeticNaN) : ¬ F64.unaryResult e F F := by
  unfold F64.unaryResult
  split
  · split
    · rename_i hc
      exact fun h => hna h.isArithmeticNaN
    · exact fun h => hna h
  · rename_i hn
    intro h
    exact hn (h ▸ hF)

theorem eval_ne64 {e : F64 → F64} {F : F64} (he : (e F).IsNonNaNOrCanonicalNaN)
    (hF : F.IsNaN) (hna : ¬ F.IsArithmeticNaN) : e F ≠ F := by
  intro h
  rw [h] at he
  rcases he with hn | hc
  · exact hn hF
  · exact hna hc.isArithmeticNaN

theorem round64_canon {op : FloatUnOp} (hop : IsRound op = true) (F : F64) :
    (floatUnOp64 op F).IsNonNaNOrCanonicalNaN := by
  cases op with
  | floor => exact F64.roundIntegral_isCanonicalized .towardNegative F
  | ceil => exact F64.roundIntegral_isCanonicalized .towardPositive F
  | trunc => exact F64.roundIntegral_isCanonicalized .towardZero F
  | nearest => exact F64.roundIntegral_isCanonicalized .nearestTiesToEven F
  | _ => simp [IsRound] at hop

/-! ## Both types -/

/-- A NaN that is not arithmetic, at either float type. -/
def SNaN : (t : FloatType) → FloatValue t → Prop
  | .f32, x => (asF32 x).IsNaN ∧ ¬ (asF32 x).IsArithmeticNaN
  | .f64, x => (asF64 x).IsNaN ∧ ¬ (asF64 x).IsArithmeticNaN

theorem asF32_bits (r : F32) : asF32 r.bits.toBitVec = r := by
  simp [asF32]

theorem asF64_bits (r : F64) : asF64 r.bits.toBitVec = r := by
  simp [asF64]

theorem fixed_ne32 {P : Profile} {op : FloatUnOp} (hop : IsRound op = true) {z : FloatValue .f32}
    (hx : SNaN .f32 z) (hz : floatUnOpP P .f32 op z z) : False := by
  obtain ⟨hF, hna⟩ := hx
  unfold floatUnOpP at hz
  cases hP : P.nan with
  | spec =>
    have hr : floatUnOpRel .f32 op z z := by simp only [hP] at hz; exact hz
    have h' : F32.unaryResult (floatUnOp32 op) (asF32 z) (asF32 z) := by
      clear hz
      cases op <;> first | exact hr | simp [IsRound] at hop
    exact not_unaryResult32 (round32_canon hop _) hF hna h'
  | canonical =>
    have hc : z = floatUnOp .f32 op z := by simp only [hP] at hz; exact hz
    have h' : asF32 z = floatUnOp32 op (asF32 z) := by
      conv_lhs => rw [hc]
      exact asF32_bits _
    exact eval_ne32 (round32_canon hop _) hF hna h'.symm

theorem fixed_ne64 {P : Profile} {op : FloatUnOp} (hop : IsRound op = true) {z : FloatValue .f64}
    (hx : SNaN .f64 z) (hz : floatUnOpP P .f64 op z z) : False := by
  obtain ⟨hF, hna⟩ := hx
  unfold floatUnOpP at hz
  cases hP : P.nan with
  | spec =>
    have hr : floatUnOpRel .f64 op z z := by simp only [hP] at hz; exact hz
    have h' : F64.unaryResult (floatUnOp64 op) (asF64 z) (asF64 z) := by
      clear hz
      cases op <;> first | exact hr | simp [IsRound] at hop
    exact not_unaryResult64 (round64_canon hop _) hF hna h'
  | canonical =>
    have hc : z = floatUnOp .f64 op z := by simp only [hP] at hz; exact hz
    have h' : asF64 z = floatUnOp64 op (asF64 z) := by
      conv_lhs => rw [hc]
      exact asF64_bits _
    exact eval_ne64 (round64_canon hop _) hF hna h'.symm

/-- **No allowed result of a rounding operator on a signalling NaN is the input**, at either
NaN policy. -/
theorem unOp_ne {P : Profile} {t : FloatType} {op : FloatUnOp} (hop : IsRound op = true)
    {x z : FloatValue t} (hx : SNaN t x) (hz : floatUnOpP P t op x z) : z ≠ x := by
  rintro rfl
  cases t with
  | f32 => exact fixed_ne32 hop hx hz
  | f64 => exact fixed_ne64 hop hx hz

/-- A testsuite input: NaN, not arithmetic, quiet bit clear (kernel evaluations). -/
theorem sNaN_facts32 (x : FloatValue .f32) (hx : x ∈ sNaN32) :
    SNaN .f32 x ∧ isNaNB .f32 x = true ∧ isSNaNB .f32 x = true := by
  unfold SNaN
  rcases hx with _ | ⟨_, hx⟩
  · decide +kernel
  rcases hx with _ | ⟨_, hx⟩
  · decide +kernel
  cases hx

/-- The `f64` inputs. -/
theorem sNaN_facts64 (x : FloatValue .f64) (hx : x ∈ sNaN64) :
    SNaN .f64 x ∧ isNaNB .f64 x = true ∧ isSNaNB .f64 x = true := by
  unfold SNaN
  rcases hx with _ | ⟨_, hx⟩
  · decide +kernel
  rcases hx with _ | ⟨_, hx⟩
  · decide +kernel
  cases hx

/-- **The testsuite's inputs are signalling NaNs.** -/
theorem sNaN_facts {t : FloatType} {x : FloatValue t} (hx : x ∈ sNaNs t) :
    SNaN t x ∧ isNaNB t x = true ∧ isSNaNB t x = true := by
  cases t with
  | f32 => exact sNaN_facts32 x hx
  | f64 => exact sNaN_facts64 x hx

end Silmaril.Proofs.Wasm.Wasmi.Observed
