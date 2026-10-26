module

public import Silmaril.Numeric.Ieee754.Flags.Denormal
public import Silmaril.Numeric.Ieee754.Environment

/-!
# Exception flags of binary32 and binary64 operations

These definitions apply the format-generic flag functions of
`Numeric.Ieee754.Flags.Operations` to raw `F32` and `F64` encodings, including
signaling NaNs, which the core arithmetic model does not distinguish. Each takes
the rounding direction and the tininess convention explicitly;
`Environment.signal` supplies both from an `Environment` and accumulates the
flags stickily (IEEE 754-2019 §7.1).

The flags do not depend on how a result value is computed. NaN payloads and
zero signs are not specified here. `Numeric.Ieee754.Flags.Executable` relates
the flags to the values of `F32.addWith` and its siblings, and
`Numeric.Ieee754.Flags.Outcome` gives the operation outcomes that a value
computation can share.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754

open Float.Model FlagSpec

namespace F32

/-- Flags of binary32 addition. -/
def addFlags (mode : RoundingMode) (tininess : Tininess) (x y : F32) : Flags :=
  FlagSpec.add Format.binary32 mode tininess x.datum y.datum
/-- Flags of binary32 subtraction. -/
def subFlags (mode : RoundingMode) (tininess : Tininess) (x y : F32) : Flags :=
  FlagSpec.sub Format.binary32 mode tininess x.datum y.datum
/-- Flags of binary32 multiplication. -/
def mulFlags (mode : RoundingMode) (tininess : Tininess) (x y : F32) : Flags :=
  FlagSpec.mul Format.binary32 mode tininess x.datum y.datum
/-- Flags of binary32 division. -/
def divFlags (mode : RoundingMode) (tininess : Tininess) (x y : F32) : Flags :=
  FlagSpec.div Format.binary32 mode tininess x.datum y.datum
/-- Flags of binary32 square root. -/
def sqrtFlags (mode : RoundingMode) (tininess : Tininess) (x : F32) : Flags :=
  FlagSpec.sqrt Format.binary32 mode tininess x.datum
/-- Flags of binary32 fused multiply-add `x · y + z`. -/
def fmaFlags (policy : FmaQuietAddend) (mode : RoundingMode) (tininess : Tininess)
    (x y z : F32) : Flags :=
  FlagSpec.fma policy Format.binary32 mode tininess x.datum y.datum z.datum
/-- Flags of binary32-to-binary64 conversion. -/
def toF64Flags (mode : RoundingMode) (tininess : Tininess) (x : F32) : Flags :=
  FlagSpec.convert Format.binary64 mode tininess x.datum
/-- Flags of conversion to a bounded integer (§5.8). -/
def toIntFlags (target : IntFormat) (mode : RoundingMode) (signalsInexact : Bool) (x : F32) :
    Flags :=
  FlagSpec.toInt target mode signalsInexact x.datum
/-- Flags of integer-to-binary32 conversion. -/
def ofIntFlags (mode : RoundingMode) (tininess : Tininess) (n : ℤ) : Flags :=
  FlagSpec.ofInt Format.binary32 mode tininess n
/-- Flags of rounding to an integral binary32 value (§5.9). -/
def roundToIntegralFlags (mode : RoundingMode) (signalsInexact : Bool) (x : F32) : Flags :=
  FlagSpec.roundToIntegral mode signalsInexact x.datum

end F32

namespace F64

/-- Flags of binary64 addition. -/
def addFlags (mode : RoundingMode) (tininess : Tininess) (x y : F64) : Flags :=
  FlagSpec.add Format.binary64 mode tininess x.datum y.datum
/-- Flags of binary64 subtraction. -/
def subFlags (mode : RoundingMode) (tininess : Tininess) (x y : F64) : Flags :=
  FlagSpec.sub Format.binary64 mode tininess x.datum y.datum
/-- Flags of binary64 multiplication. -/
def mulFlags (mode : RoundingMode) (tininess : Tininess) (x y : F64) : Flags :=
  FlagSpec.mul Format.binary64 mode tininess x.datum y.datum
/-- Flags of binary64 division. -/
def divFlags (mode : RoundingMode) (tininess : Tininess) (x y : F64) : Flags :=
  FlagSpec.div Format.binary64 mode tininess x.datum y.datum
/-- Flags of binary64 square root. -/
def sqrtFlags (mode : RoundingMode) (tininess : Tininess) (x : F64) : Flags :=
  FlagSpec.sqrt Format.binary64 mode tininess x.datum
/-- Flags of binary64 fused multiply-add `x · y + z`. -/
def fmaFlags (policy : FmaQuietAddend) (mode : RoundingMode) (tininess : Tininess)
    (x y z : F64) : Flags :=
  FlagSpec.fma policy Format.binary64 mode tininess x.datum y.datum z.datum
/-- Flags of binary64-to-binary32 conversion. -/
def toF32Flags (mode : RoundingMode) (tininess : Tininess) (x : F64) : Flags :=
  FlagSpec.convert Format.binary32 mode tininess x.datum
/-- Flags of conversion to a bounded integer (§5.8). -/
def toIntFlags (target : IntFormat) (mode : RoundingMode) (signalsInexact : Bool) (x : F64) :
    Flags :=
  FlagSpec.toInt target mode signalsInexact x.datum
/-- Flags of integer-to-binary64 conversion. -/
def ofIntFlags (mode : RoundingMode) (tininess : Tininess) (n : ℤ) : Flags :=
  FlagSpec.ofInt Format.binary64 mode tininess n
/-- Flags of rounding to an integral binary64 value (§5.9). -/
def roundToIntegralFlags (mode : RoundingMode) (signalsInexact : Bool) (x : F64) : Flags :=
  FlagSpec.roundToIntegral mode signalsInexact x.datum

end F64

/-! ## Finite operands -/

theorem F32.datum_finite_of_isFinite {x : F32} (h : x.IsFinite) :
    ∃ negative value, x.datum = .finite negative value := by
  rw [F32.datum_eq]
  unfold Datum.ofDecoded finiteValue
  have h' : ¬ (decode32 x.bits.toNat).exponent = maxExponentField binary32ExponentBits := h
  simp only [beq_iff_eq, h', ↓reduceIte]
  split_ifs <;> exact ⟨_, _, rfl⟩

theorem F64.datum_finite_of_isFinite {x : F64} (h : x.IsFinite) :
    ∃ negative value, x.datum = .finite negative value := by
  rw [F64.datum_eq]
  unfold Datum.ofDecoded finiteValue
  have h' : ¬ (decode64 x.bits.toNat).exponent = maxExponentField binary64ExponentBits := h
  simp only [beq_iff_eq, h', ↓reduceIte]
  split_ifs <;> exact ⟨_, _, rfl⟩

theorem F32.datum_zero : (F32.ofBits 0).datum = .finite false 0 := by decide +kernel
theorem F32.datum_negZero : (F32.ofBits 0x80000000).datum = .finite true 0 := by decide +kernel
theorem F32.datum_one : (F32.ofBits 0x3f800000).datum = .finite false 1 := by decide +kernel
theorem F64.datum_zero : (F64.ofBits 0).datum = .finite false 0 := by decide +kernel
theorem F64.datum_one : (F64.ofBits 0x3ff0000000000000).datum = .finite false 1 := by
  decide +kernel

/-! ## Characterisations -/

section Binary32

variable (mode : RoundingMode) (tininess : Tininess)

/-- A signaling NaN operand raises invalid and nothing else. -/
theorem F32.addFlags_of_signaling {x y : F32} (h : (x.isSignalingNaN || y.isSignalingNaN) = true) :
    x.addFlags mode tininess y = invalid := by
  apply add_of_signaling
  simpa [F32.datum_isSignaling] using h

theorem F32.mulFlags_of_signaling {x y : F32} (h : (x.isSignalingNaN || y.isSignalingNaN) = true) :
    x.mulFlags mode tininess y = invalid := by
  apply mul_of_signaling
  simpa [F32.datum_isSignaling] using h

theorem F32.divFlags_of_signaling {x y : F32} (h : (x.isSignalingNaN || y.isSignalingNaN) = true) :
    x.divFlags mode tininess y = invalid := by
  apply div_of_signaling
  simpa [F32.datum_isSignaling] using h

/-- Adding positive zero to a finite binary32 value raises no flags. -/
theorem F32.addFlags_zero {x : F32} (h : x.IsFinite) :
    x.addFlags mode tininess (F32.ofBits 0) = Flags.empty := by
  obtain ⟨n, v, hx⟩ := F32.datum_finite_of_isFinite h
  rw [F32.addFlags, hx, F32.datum_zero]
  exact add_zero_eq_empty _ _ _ _ _ (F32.datum_finite_representable x hx)

/-- Multiplying a finite binary32 value by one raises no flags. -/
theorem F32.mulFlags_one {x : F32} (h : x.IsFinite) :
    x.mulFlags mode tininess (F32.ofBits 0x3f800000) = Flags.empty := by
  obtain ⟨n, v, hx⟩ := F32.datum_finite_of_isFinite h
  rw [F32.mulFlags, hx, F32.datum_one]
  exact mul_one_eq_empty _ _ _ _ _ (F32.datum_finite_representable x hx)

/-- Widening to binary64 raises only invalid, and only for a signaling NaN. -/
theorem F32.toF64Flags_eq (x : F32) :
    x.toF64Flags mode tininess = if x.isSignalingNaN then invalid else Flags.empty := by
  rw [← F32.datum_isSignaling, F32.toF64Flags]
  cases hx : x.datum with
  | nan s => cases s <;> rfl
  | infinity n => rfl
  | finite n v =>
    exact convert_binary32_to_binary64 mode tininess n (F32.datum_finite_representable x hx)

end Binary32

section Binary64

variable (mode : RoundingMode) (tininess : Tininess)

theorem F64.addFlags_of_signaling {x y : F64} (h : (x.isSignalingNaN || y.isSignalingNaN) = true) :
    x.addFlags mode tininess y = invalid := by
  apply add_of_signaling
  simpa [F64.datum_isSignaling] using h

theorem F64.mulFlags_of_signaling {x y : F64} (h : (x.isSignalingNaN || y.isSignalingNaN) = true) :
    x.mulFlags mode tininess y = invalid := by
  apply mul_of_signaling
  simpa [F64.datum_isSignaling] using h

theorem F64.divFlags_of_signaling {x y : F64} (h : (x.isSignalingNaN || y.isSignalingNaN) = true) :
    x.divFlags mode tininess y = invalid := by
  apply div_of_signaling
  simpa [F64.datum_isSignaling] using h

theorem F64.addFlags_zero {x : F64} (h : x.IsFinite) :
    x.addFlags mode tininess (F64.ofBits 0) = Flags.empty := by
  obtain ⟨n, v, hx⟩ := F64.datum_finite_of_isFinite h
  rw [F64.addFlags, hx, F64.datum_zero]
  exact add_zero_eq_empty _ _ _ _ _ (F64.datum_finite_representable x hx)

theorem F64.mulFlags_one {x : F64} (h : x.IsFinite) :
    x.mulFlags mode tininess (F64.ofBits 0x3ff0000000000000) = Flags.empty := by
  obtain ⟨n, v, hx⟩ := F64.datum_finite_of_isFinite h
  rw [F64.mulFlags, hx, F64.datum_one]
  exact mul_one_eq_empty _ _ _ _ _ (F64.datum_finite_representable x hx)

/-- Every integer of magnitude below `2 ^ 53`, and in particular every 32-bit
integer, converts to binary64 without flags. -/
theorem F64.ofIntFlags_of_natAbs_lt {n : ℤ} (h : n.natAbs < 2 ^ 53) :
    F64.ofIntFlags mode tininess n = Flags.empty := by
  apply ofInt_eq_empty_of_representable
  have hn : |n| < 2 ^ 53 := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast h
  refine ⟨n, 0, by simp, hn.trans_eq (by decide), by decide, ?_⟩
  have hq : |(n : ℚ)| < 2 ^ 53 := by exact_mod_cast hn
  have hmax : (2 : ℚ) ^ 53 ≤ FlagSpec.maxFinite Format.binary64 := by decide +kernel
  linarith

end Binary64

/-! ## Sticky accumulation in an environment -/

namespace Environment

/-- Default exception handling (§7.1): raise the flags of an operation evaluated
under this environment's rounding direction (§4.3) and tininess convention
(§7.5). Flags already raised stay raised. -/
def signal (env : Environment) (flags : RoundingMode → Tininess → Flags) : Environment :=
  env.raiseFlags (flags env.rounding env.tininess)

@[simp] theorem signal_flags (env : Environment) (flags : RoundingMode → Tininess → Flags) :
    (env.signal flags).flags = env.flags.union (flags env.rounding env.tininess) := rfl

@[simp] theorem signal_rounding (env : Environment) (flags : RoundingMode → Tininess → Flags) :
    (env.signal flags).rounding = env.rounding := rfl

@[simp] theorem signal_tininess (env : Environment) (flags : RoundingMode → Tininess → Flags) :
    (env.signal flags).tininess = env.tininess := rfl

theorem mem_signal (env : Environment) (flags : RoundingMode → Tininess → Flags) (e : Exception) :
    e ∈ (env.signal flags).flags ↔ e ∈ env.flags ∨ e ∈ flags env.rounding env.tininess :=
  Flags.mem_union _ _ _

/-- Signaling never clears a flag. -/
theorem signal_sticky (env : Environment) (flags : RoundingMode → Tininess → Flags) :
    env.flags.Subset (env.signal flags).flags := Flags.subset_union_left _ _

/-- The accumulated status does not depend on the order of two operations. -/
theorem signal_comm (env : Environment) (first second : RoundingMode → Tininess → Flags) :
    (env.signal first).signal second = (env.signal second).signal first := by
  simp only [signal, raiseFlags, Environment.mk.injEq, true_and]
  rw [Flags.union_assoc, Flags.union_comm (first _ _), ← Flags.union_assoc]

/-- An exact operation leaves the environment unchanged. -/
theorem signal_empty (env : Environment) : env.signal (fun _ _ => Flags.empty) = env :=
  raiseFlags_empty env

/-- Signaling agrees with committing a `Result` whose flags are the operation's
flags under the environment's attributes. -/
theorem signal_eq_commit {α : Type*} (env : Environment) (value : α)
    (flags : RoundingMode → Tininess → Flags) :
    env.signal flags = (env.commit ⟨value, flags env.rounding env.tininess⟩).2 := rfl

end Environment

end Silmaril.Numeric.Ieee754
