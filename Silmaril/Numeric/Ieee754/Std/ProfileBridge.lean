module

public import Silmaril.Numeric.Ieee754.Std.Bridge
public import Silmaril.Numeric.Ieee754.Std.CoreBridge
public import Silmaril.Numeric.Ieee754.Std.WasmBridge
public import Silmaril.Numeric.Float.Wasm

/-!
# Proved bridges from `Numeric.Float` profiles to `Std`

`Silmaril.Numeric.Float.Profile` is the older profile-parametric bit-level
implementation (`Profile.x86SSE`, `Profile.riscvFD`, ...). `Std.Bridge` checks it
against `Std` executably on TestFloat operands; this module proves the parts of
that agreement that hold for all operands:

* **NaN results.** `toFields` reads a `Numeric.Float` encoding as `Std` fields.
  It commutes with the NaN test, quieting and the default NaN, so a profile's NaN
  choice `Profile.pickNaN` is a `Std` NaN function: `pickNaN_firstNaN` (the x86
  rule, `NaNFun.x86SSE`) and `pickNaN_defaultNaN` (`NaNFun.riscv`). In particular
  `x86SSE_pickNaN` and `riscvFD_pickNaN` say the two profiles choose exactly the
  NaN that `Isa.x86SSE` and `Isa.riscv` choose for the same operand list, and
  `x86SSE_pickNaN_wasm` places the x86 profile's NaNs in WebAssembly's NaN rule.
* **Numeric results.** Without input or output flushing, a profile's binary
  arithmetic result on non-NaN operands is the core model's correctly rounded
  result (`binary_value`). So in binary32 and binary64, for every rounding
  direction, finite operands and a non-overflowing result, `add`, `sub` and
  `mul` of such a profile have the value of the same operation of every `Std`
  profile (`add32` ... `mul64`, through `Std.CoreBridge`); `x86SSE_add32` and
  `riscvFD_add32` etc. instantiate this for `Profile.x86SSE` (DAZ and FZ clear)
  with `Isa.x86SSE`, and `Profile.riscvFD` with `Isa.riscv`. These are value
  statements: the two zeros are identified.

What is not proved here (and is checked only executably, by `Std.Bridge` over the
TestFloat level-1 operand sets): flags, overflow, division, square root, `fma`,
conversions, comparisons and min/max of the profiles.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Std.ProfileBridge

open Float.Model Float.Model.UnpackedFloat
open Silmaril.Numeric.Ieee754 Silmaril.Numeric.Ieee754.Std Silmaril.Numeric.Float
open Silmaril.Numeric.Ieee754.Conformance Silmaril.Numeric.Ieee754.Std.CoreBridge
local notation "coreFormat" => Silmaril.Numeric.Ieee754.Std.Bridge.coreFormat

/-! ## Encodings -/

variable (F : Interchange)

/-- A `Numeric.Float` encoding of an interchange format as `Std` fields. -/
def toFields (b : Float.Bits (coreFormat F)) : Fields :=
  ⟨Bits.signBit b, (unpackExponent b).toNat, (unpackMantissa b).toNat⟩

theorem neg_one_toNat (w : ℕ) : (-1#w).toNat = 2 ^ w - 1 := by
  rw [BitVec.neg_one_eq_allOnes, BitVec.toNat_allOnes]

theorem isNaN_toFields (b : Float.Bits (coreFormat F)) :
    F.encoding.isNaN (toFields F b) = Bits.isNaN b := by
  have he : ((unpackExponent b).toNat == 2 ^ F.w - 1) = (unpackExponent b == -1#_) := by
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, BitVec.toNat_eq, neg_one_toNat]
    rfl
  have hm : ((unpackMantissa b).toNat != 0) = (unpackMantissa b != 0#_) := by
    rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne, ne_eq, ne_eq, BitVec.toNat_eq]
    rfl
  simp only [Interchange.encoding, Interchange.isNaN, Interchange.expMax, toFields, Bits.isNaN]
  rw [← he, ← hm]

theorem unpackSign_packComponents {fmt : Format} (s : Sign) (e : BitVec fmt.exponentBits)
    (m : BitVec fmt.mantissaBitsWithoutImplicit) :
    unpackSign (packComponents fmt s e m) = s.toBitVec := by
  ext i hi
  have hi0 : i = 0 := by omega
  subst hi0
  simp [unpackSign, packComponents, BitVec.getLsbD_append, BitVec.getElem_append]

theorem toBitVec_ofBitVec : ∀ v : BitVec 1, (Sign.ofBitVec v).toBitVec = v := by decide

theorem signBit_quiet {fmt : Format} (b : Float.Bits fmt) : Bits.signBit (Bits.quiet b) = Bits.signBit b := by
  simp only [Bits.signBit, Bits.quiet, Bits.sign, unpackSign_packComponents, toBitVec_ofBitVec]

theorem signBit_defaultNaN (fmt : Format) (neg : Bool) :
    Bits.signBit (Bits.defaultNaN fmt neg) = neg := by
  cases neg <;> simp [Bits.signBit, Bits.defaultNaN, Sign.toBitVec]

theorem toFields_quiet (b : Float.Bits (coreFormat F)) :
    toFields F (Bits.quiet b) = F.encoding.quiet (toFields F b) := by
  simp only [toFields, signBit_quiet, Bits.unpackExponent_quiet, Bits.unpackMantissa_quiet,
    Interchange.encoding, Interchange.quiet, BitVec.toNat_or, Bits.quietMask_toNat]
  rfl

theorem toFields_defaultNaN (neg : Bool) :
    toFields F (Bits.defaultNaN (coreFormat F) neg) = F.encoding.defaultNaN neg := by
  simp only [toFields, signBit_defaultNaN, Bits.unpackExponent_defaultNaN,
    Bits.unpackMantissa_defaultNaN, Bits.quietMask_toNat, neg_one_toNat, Interchange.encoding]
  rfl

/-! ## NaN results -/

theorem find?_map_toFields (ops : List (Float.Bits (coreFormat F))) :
    (ops.map (toFields F)).find? (fun i => F.encoding.isNaN i) =
      (ops.find? Bits.isNaN).map (toFields F) := by
  simp [List.find?_map, isNaN_toFields]

/-- A first-NaN profile chooses the `Std` x86 NaN with its own default NaN. -/
theorem pickNaN_firstNaN (p : Profile) (h : p.propagation = .firstNaN)
    (ops : List (Float.Bits (coreFormat F))) :
    toFields F (p.pickNaN ops) =
      NaNFun.x86SSE F.encoding (F.encoding.defaultNaN p.defaultNaNNegative) (ops.map (toFields F)) := by
  unfold Profile.pickNaN NaNFun.x86SSE
  rw [h, find?_map_toFields]
  cases ops.find? Bits.isNaN with
  | none => exact toFields_defaultNaN F _
  | some b => exact toFields_quiet F b

/-- A default-NaN profile chooses the `Std` canonical-NaN function. -/
theorem pickNaN_defaultNaN (p : Profile) (h : p.propagation = .defaultNaN)
    (ops : List (Float.Bits (coreFormat F))) :
    toFields F (p.pickNaN ops) =
      NaNFun.riscv (F.encoding.defaultNaN p.defaultNaNNegative) (ops.map (toFields F)) := by
  unfold Profile.pickNaN NaNFun.riscv
  rw [h]
  exact toFields_defaultNaN F _

/-- `Profile.x86SSE` (any MXCSR setting) and `Isa.x86SSE` choose the same NaN. -/
theorem x86SSE_pickNaN (c : MXCSRControl) (ops : List (Float.Bits (coreFormat F))) :
    toFields F ((Profile.x86SSE c).pickNaN ops) = Isa.x86SSE.nan F.encoding (ops.map (toFields F)) :=
  pickNaN_firstNaN F _ rfl ops

/-- `Profile.riscvFD` and `Isa.riscv` choose the same NaN. -/
theorem riscvFD_pickNaN (ops : List (Float.Bits (coreFormat F))) :
    toFields F (Profile.riscvFD.pickNaN ops) = Isa.riscv.nan F.encoding (ops.map (toFields F)) :=
  pickNaN_defaultNaN F _ rfl ops

/-- The x86 profile's NaN choice is one WebAssembly admits (`NaNSpec.wasm`). -/
theorem x86SSE_pickNaN_wasm (c : MXCSRControl) (ops : List (Float.Bits (coreFormat F))) :
    NaNSpec.wasm F (ops.map (toFields F)) (toFields F ((Profile.x86SSE c).pickNaN ops)) :=
  NaNSpec.x86SSE_le_wasm F _ _ (x86SSE_pickNaN F c ops)

/-- The RISC-V profile's NaN choice is one WebAssembly admits. -/
theorem riscvFD_pickNaN_wasm (ops : List (Float.Bits (coreFormat F))) :
    NaNSpec.wasm F (ops.map (toFields F)) (toFields F (Profile.riscvFD.pickNaN ops)) :=
  NaNSpec.riscv_le_wasm F _ _ (riscvFD_pickNaN F ops)

/-- A first-NaN profile's NaN choice is in the propagating policy. -/
theorem pickNaN_firstNaN_propagating (p : Profile) (h : p.propagation = .firstNaN)
    (ops : List (Float.Bits (coreFormat F))) :
    NaNSpec.propagating F.encoding (ops.map (toFields F)) (toFields F (p.pickNaN ops)) :=
  NaNSpec.x86SSE_le_propagating F.encoding _ (F.encoding.defaultNaN_quiet _) _ _
    (pickNaN_firstNaN F p h ops)

/-! ## Numeric results -/

/-- Without flushing, a profile's binary arithmetic on non-NaN operands, when the
core result is not a NaN, is the core model's correctly rounded result. -/
theorem binary_value (p : Profile) {fmt : Format} (core : ArithOp) (mode : RoundingMode)
    (x y : Float.Bits fmt) (hin : p.flushInputs = false) (hout : p.flushResults = false)
    (hx : x.isNaN = false) (hy : y.isNaN = false)
    (hr : ((core.core x.value y.value).round fmt mode).isNaN = false) :
    (p.binary fmt core mode x y).value = (core.core x.value y.value).round fmt mode := by
  simp only [Profile.binary, Profile.flushInput_of_false p _ hin, Profile.nanOrElse,
    List.any_cons, List.any_nil, hx, hy, Bool.or_false, Bool.false_eq_true, ite_false,
    Profile.finish, Profile.flushSign?, hout, hr]

theorem isNaN_false_of_value? {fmt : Format} {b : Float.Bits fmt} {q : ℚ}
    (h : value? (Bits.value b) = some q) : b.isNaN = false := by
  cases hb : b.isNaN
  · rfl
  · rw [(Bits.value_eq_notANumber_iff b).mpr hb] at h
    simp [value?] at h

section Binary32

/-- The `F32` wrapper of a binary32 encoding. -/
abbrev f32 (x : BitVec 32) : F32 := ⟨UInt32.ofBitVec x⟩

theorem value?_value32 (x : BitVec 32) : value? (Bits.value (fmt := .binary32) x) = (f32 x).toRat? :=
  F32.value?_unpack_bits (f32 x)

theorem binary32 (p : Profile) (hin : p.flushInputs = false) (hout : p.flushResults = false)
    (core : ArithOp) (mode : RoundingMode) (x y : BitVec 32) {a b : ℚ}
    (hx : (f32 x).toRat? = some a) (hy : (f32 y).toRat? = some b) {q : ℚ}
    (hr : (f32 ((core.core (Bits.value (fmt := .binary32) x) (Bits.value (fmt := .binary32) y)).round
      .binary32 mode)).toRat? = some q) :
    (p.binary .binary32 core mode x y).value =
      (core.core (Bits.value (fmt := .binary32) x) (Bits.value (fmt := .binary32) y)).round .binary32 mode :=
  binary_value (fmt := .binary32) p core mode x y hin hout
    (isNaN_false_of_value? ((value?_value32 x).trans hx))
    (isNaN_false_of_value? ((value?_value32 y).trans hy))
    (isNaN_false_of_value? ((value?_value32 _).trans hr))

/-- binary32 addition: a profile without flushing (`Profile.x86SSE` with DAZ and FZ
clear, `Profile.riscvFD`, ...) has the value of the addition of every `Std`
profile `I`, for finite operands and a non-overflowing result, in every rounding
direction. -/
theorem add32 (p : Profile) (hin : p.flushInputs = false) (hout : p.flushResults = false) (I : Isa)
    (mode : RoundingMode) (x y : BitVec 32) {a b : ℚ}
    (hx : (f32 x).toRat? = some a) (hy : (f32 y).toRat? = some b)
    (inRange : NoExponentOverflow .binary32 (Rounding.roundUnpacked .binary32 mode
      (Rounding.addExact mode (f32 x).model.unpack (f32 y).model.unpack))) :
    (f32 (p.add .binary32 mode x y).value).toRat? =
      datumValue? (Interchange.binary32.decode
        (I.add Interchange.binary32.encoding mode (f32 x).toStd (f32 y).toStd).1) := by
  rw [F32.isa_add _ mode _ _ hx hy inRange]
  have hw : F32.addWith mode (f32 x) (f32 y) =
      f32 ((ArithOp.add.core (Bits.value (fmt := .binary32) x) (Bits.value (fmt := .binary32) y)).round
        .binary32 mode) := by
    simp only [F32.addWith, show (f32 x).model.unpack = Bits.value (fmt := .binary32) x from
      model_unpack32 x, show (f32 y).model.unpack = Bits.value (fmt := .binary32) y from model_unpack32 y]
    rfl
  obtain ⟨q, hq⟩ : ∃ q, (F32.addWith mode (f32 x) (f32 y)).toRat? = some q :=
    ⟨_, F32.packRounded_toRat? mode _ (value?_addExact mode ((value?_model_unpack32 _).trans hx)
      ((value?_model_unpack32 _).trans hy)) inRange⟩
  rw [hw] at hq ⊢
  unfold Profile.add
  rw [binary32 p hin hout .add mode x y hx hy hq]

/-- binary32 subtraction (as `add32`). -/
theorem sub32 (p : Profile) (hin : p.flushInputs = false) (hout : p.flushResults = false) (I : Isa)
    (mode : RoundingMode) (x y : BitVec 32) {a b : ℚ}
    (hx : (f32 x).toRat? = some a) (hy : (f32 y).toRat? = some b)
    (inRange : NoExponentOverflow .binary32 (Rounding.roundUnpacked .binary32 mode
      (Rounding.addExact mode (f32 x).model.unpack (f32 y).model.unpack.neg))) :
    (f32 (p.sub .binary32 mode x y).value).toRat? =
      datumValue? (Interchange.binary32.decode
        (I.sub Interchange.binary32.encoding mode (f32 x).toStd (f32 y).toStd).1) := by
  rw [F32.isa_sub _ mode _ _ hx hy inRange]
  have hw : F32.subWith mode (f32 x) (f32 y) =
      f32 ((ArithOp.sub.core (Bits.value (fmt := .binary32) x) (Bits.value (fmt := .binary32) y)).round
        .binary32 mode) := by
    simp only [F32.subWith, show (f32 x).model.unpack = Bits.value (fmt := .binary32) x from
      model_unpack32 x, show (f32 y).model.unpack = Bits.value (fmt := .binary32) y from model_unpack32 y]
    rfl
  obtain ⟨q, hq⟩ : ∃ q, (F32.subWith mode (f32 x) (f32 y)).toRat? = some q :=
    ⟨_, F32.packRounded_toRat? mode _ (value?_subExact mode ((value?_model_unpack32 _).trans hx)
      ((value?_model_unpack32 _).trans hy)) inRange⟩
  rw [hw] at hq ⊢
  unfold Profile.sub
  rw [binary32 p hin hout .sub mode x y hx hy hq]

/-- binary32 multiplication (as `add32`). -/
theorem mul32 (p : Profile) (hin : p.flushInputs = false) (hout : p.flushResults = false) (I : Isa)
    (mode : RoundingMode) (x y : BitVec 32) {a b : ℚ}
    (hx : (f32 x).toRat? = some a) (hy : (f32 y).toRat? = some b)
    (inRange : NoExponentOverflow .binary32 (Rounding.roundUnpacked .binary32 mode
      (Rounding.mulExact (f32 x).model.unpack (f32 y).model.unpack))) :
    (f32 (p.mul .binary32 mode x y).value).toRat? =
      datumValue? (Interchange.binary32.decode
        (I.mul Interchange.binary32.encoding mode (f32 x).toStd (f32 y).toStd).1) := by
  rw [F32.isa_mul _ mode _ _ hx hy inRange]
  have hw : F32.mulWith mode (f32 x) (f32 y) =
      f32 ((ArithOp.mul.core (Bits.value (fmt := .binary32) x) (Bits.value (fmt := .binary32) y)).round
        .binary32 mode) := by
    simp only [F32.mulWith, show (f32 x).model.unpack = Bits.value (fmt := .binary32) x from
      model_unpack32 x, show (f32 y).model.unpack = Bits.value (fmt := .binary32) y from model_unpack32 y]
    rfl
  obtain ⟨q, hq⟩ : ∃ q, (F32.mulWith mode (f32 x) (f32 y)).toRat? = some q :=
    ⟨_, F32.packRounded_toRat? mode _ (value?_mulExact ((value?_model_unpack32 _).trans hx)
      ((value?_model_unpack32 _).trans hy)) inRange⟩
  rw [hw] at hq ⊢
  unfold Profile.mul
  rw [binary32 p hin hout .mul mode x y hx hy hq]

end Binary32

section Binary64

/-- The `F64` wrapper of a binary64 encoding. -/
abbrev f64 (x : BitVec 64) : F64 := ⟨UInt64.ofBitVec x⟩

theorem value?_value64 (x : BitVec 64) : value? (Bits.value (fmt := .binary64) x) = (f64 x).toRat? :=
  F64.value?_unpack_bits (f64 x)

theorem binary64 (p : Profile) (hin : p.flushInputs = false) (hout : p.flushResults = false)
    (core : ArithOp) (mode : RoundingMode) (x y : BitVec 64) {a b : ℚ}
    (hx : (f64 x).toRat? = some a) (hy : (f64 y).toRat? = some b) {q : ℚ}
    (hr : (f64 ((core.core (Bits.value (fmt := .binary64) x) (Bits.value (fmt := .binary64) y)).round
      .binary64 mode)).toRat? = some q) :
    (p.binary .binary64 core mode x y).value =
      (core.core (Bits.value (fmt := .binary64) x) (Bits.value (fmt := .binary64) y)).round .binary64 mode :=
  binary_value (fmt := .binary64) p core mode x y hin hout
    (isNaN_false_of_value? ((value?_value64 x).trans hx))
    (isNaN_false_of_value? ((value?_value64 y).trans hy))
    (isNaN_false_of_value? ((value?_value64 _).trans hr))

/-- binary64 addition (as `add32`). -/
theorem add64 (p : Profile) (hin : p.flushInputs = false) (hout : p.flushResults = false) (I : Isa)
    (mode : RoundingMode) (x y : BitVec 64) {a b : ℚ}
    (hx : (f64 x).toRat? = some a) (hy : (f64 y).toRat? = some b)
    (inRange : NoExponentOverflow .binary64 (Rounding.roundUnpacked .binary64 mode
      (Rounding.addExact mode (f64 x).model.unpack (f64 y).model.unpack))) :
    (f64 (p.add .binary64 mode x y).value).toRat? =
      datumValue? (Interchange.binary64.decode
        (I.add Interchange.binary64.encoding mode (f64 x).toStd (f64 y).toStd).1) := by
  rw [F64.isa_add _ mode _ _ hx hy inRange]
  have hw : F64.addWith mode (f64 x) (f64 y) =
      f64 ((ArithOp.add.core (Bits.value (fmt := .binary64) x) (Bits.value (fmt := .binary64) y)).round
        .binary64 mode) := by
    simp only [F64.addWith, show (f64 x).model.unpack = Bits.value (fmt := .binary64) x from
      model_unpack64 x, show (f64 y).model.unpack = Bits.value (fmt := .binary64) y from model_unpack64 y]
    rfl
  obtain ⟨q, hq⟩ : ∃ q, (F64.addWith mode (f64 x) (f64 y)).toRat? = some q :=
    ⟨_, F64.packRounded_toRat? mode _ (value?_addExact mode ((value?_model_unpack64 _).trans hx)
      ((value?_model_unpack64 _).trans hy)) inRange⟩
  rw [hw] at hq ⊢
  unfold Profile.add
  rw [binary64 p hin hout .add mode x y hx hy hq]

/-- binary64 subtraction (as `add32`). -/
theorem sub64 (p : Profile) (hin : p.flushInputs = false) (hout : p.flushResults = false) (I : Isa)
    (mode : RoundingMode) (x y : BitVec 64) {a b : ℚ}
    (hx : (f64 x).toRat? = some a) (hy : (f64 y).toRat? = some b)
    (inRange : NoExponentOverflow .binary64 (Rounding.roundUnpacked .binary64 mode
      (Rounding.addExact mode (f64 x).model.unpack (f64 y).model.unpack.neg))) :
    (f64 (p.sub .binary64 mode x y).value).toRat? =
      datumValue? (Interchange.binary64.decode
        (I.sub Interchange.binary64.encoding mode (f64 x).toStd (f64 y).toStd).1) := by
  rw [F64.isa_sub _ mode _ _ hx hy inRange]
  have hw : F64.subWith mode (f64 x) (f64 y) =
      f64 ((ArithOp.sub.core (Bits.value (fmt := .binary64) x) (Bits.value (fmt := .binary64) y)).round
        .binary64 mode) := by
    simp only [F64.subWith, show (f64 x).model.unpack = Bits.value (fmt := .binary64) x from
      model_unpack64 x, show (f64 y).model.unpack = Bits.value (fmt := .binary64) y from model_unpack64 y]
    rfl
  obtain ⟨q, hq⟩ : ∃ q, (F64.subWith mode (f64 x) (f64 y)).toRat? = some q :=
    ⟨_, F64.packRounded_toRat? mode _ (value?_subExact mode ((value?_model_unpack64 _).trans hx)
      ((value?_model_unpack64 _).trans hy)) inRange⟩
  rw [hw] at hq ⊢
  unfold Profile.sub
  rw [binary64 p hin hout .sub mode x y hx hy hq]

/-- binary64 multiplication (as `add32`). -/
theorem mul64 (p : Profile) (hin : p.flushInputs = false) (hout : p.flushResults = false) (I : Isa)
    (mode : RoundingMode) (x y : BitVec 64) {a b : ℚ}
    (hx : (f64 x).toRat? = some a) (hy : (f64 y).toRat? = some b)
    (inRange : NoExponentOverflow .binary64 (Rounding.roundUnpacked .binary64 mode
      (Rounding.mulExact (f64 x).model.unpack (f64 y).model.unpack))) :
    (f64 (p.mul .binary64 mode x y).value).toRat? =
      datumValue? (Interchange.binary64.decode
        (I.mul Interchange.binary64.encoding mode (f64 x).toStd (f64 y).toStd).1) := by
  rw [F64.isa_mul _ mode _ _ hx hy inRange]
  have hw : F64.mulWith mode (f64 x) (f64 y) =
      f64 ((ArithOp.mul.core (Bits.value (fmt := .binary64) x) (Bits.value (fmt := .binary64) y)).round
        .binary64 mode) := by
    simp only [F64.mulWith, show (f64 x).model.unpack = Bits.value (fmt := .binary64) x from
      model_unpack64 x, show (f64 y).model.unpack = Bits.value (fmt := .binary64) y from model_unpack64 y]
    rfl
  obtain ⟨q, hq⟩ : ∃ q, (F64.mulWith mode (f64 x) (f64 y)).toRat? = some q :=
    ⟨_, F64.packRounded_toRat? mode _ (value?_mulExact ((value?_model_unpack64 _).trans hx)
      ((value?_model_unpack64 _).trans hy)) inRange⟩
  rw [hw] at hq ⊢
  unfold Profile.mul
  rw [binary64 p hin hout .mul mode x y hx hy hq]

end Binary64


/-! ## The x86 SSE and RISC-V profiles -/

theorem x86SSE_add32 (mode : RoundingMode) (x y : BitVec 32) {a b : ℚ}
    (hx : (f32 x).toRat? = some a) (hy : (f32 y).toRat? = some b)
    (inRange : NoExponentOverflow .binary32 (Rounding.roundUnpacked .binary32 mode
      (Rounding.addExact mode (f32 x).model.unpack (f32 y).model.unpack))) :
    (f32 ((Profile.x86SSE {}).add .binary32 mode x y).value).toRat? =
      datumValue? (Interchange.binary32.decode
        (Isa.x86SSE.add Interchange.binary32.encoding mode (f32 x).toStd (f32 y).toStd).1) :=
  add32 _ rfl rfl _ mode x y hx hy inRange

theorem riscvFD_add32 (mode : RoundingMode) (x y : BitVec 32) {a b : ℚ}
    (hx : (f32 x).toRat? = some a) (hy : (f32 y).toRat? = some b)
    (inRange : NoExponentOverflow .binary32 (Rounding.roundUnpacked .binary32 mode
      (Rounding.addExact mode (f32 x).model.unpack (f32 y).model.unpack))) :
    (f32 ((Profile.riscvFD).add .binary32 mode x y).value).toRat? =
      datumValue? (Interchange.binary32.decode
        (Isa.riscv.add Interchange.binary32.encoding mode (f32 x).toStd (f32 y).toStd).1) :=
  add32 _ rfl rfl _ mode x y hx hy inRange

theorem x86SSE_sub32 (mode : RoundingMode) (x y : BitVec 32) {a b : ℚ}
    (hx : (f32 x).toRat? = some a) (hy : (f32 y).toRat? = some b)
    (inRange : NoExponentOverflow .binary32 (Rounding.roundUnpacked .binary32 mode
      (Rounding.addExact mode (f32 x).model.unpack (f32 y).model.unpack.neg))) :
    (f32 ((Profile.x86SSE {}).sub .binary32 mode x y).value).toRat? =
      datumValue? (Interchange.binary32.decode
        (Isa.x86SSE.sub Interchange.binary32.encoding mode (f32 x).toStd (f32 y).toStd).1) :=
  sub32 _ rfl rfl _ mode x y hx hy inRange

theorem riscvFD_sub32 (mode : RoundingMode) (x y : BitVec 32) {a b : ℚ}
    (hx : (f32 x).toRat? = some a) (hy : (f32 y).toRat? = some b)
    (inRange : NoExponentOverflow .binary32 (Rounding.roundUnpacked .binary32 mode
      (Rounding.addExact mode (f32 x).model.unpack (f32 y).model.unpack.neg))) :
    (f32 ((Profile.riscvFD).sub .binary32 mode x y).value).toRat? =
      datumValue? (Interchange.binary32.decode
        (Isa.riscv.sub Interchange.binary32.encoding mode (f32 x).toStd (f32 y).toStd).1) :=
  sub32 _ rfl rfl _ mode x y hx hy inRange

theorem x86SSE_mul32 (mode : RoundingMode) (x y : BitVec 32) {a b : ℚ}
    (hx : (f32 x).toRat? = some a) (hy : (f32 y).toRat? = some b)
    (inRange : NoExponentOverflow .binary32 (Rounding.roundUnpacked .binary32 mode
      (Rounding.mulExact (f32 x).model.unpack (f32 y).model.unpack))) :
    (f32 ((Profile.x86SSE {}).mul .binary32 mode x y).value).toRat? =
      datumValue? (Interchange.binary32.decode
        (Isa.x86SSE.mul Interchange.binary32.encoding mode (f32 x).toStd (f32 y).toStd).1) :=
  mul32 _ rfl rfl _ mode x y hx hy inRange

theorem riscvFD_mul32 (mode : RoundingMode) (x y : BitVec 32) {a b : ℚ}
    (hx : (f32 x).toRat? = some a) (hy : (f32 y).toRat? = some b)
    (inRange : NoExponentOverflow .binary32 (Rounding.roundUnpacked .binary32 mode
      (Rounding.mulExact (f32 x).model.unpack (f32 y).model.unpack))) :
    (f32 ((Profile.riscvFD).mul .binary32 mode x y).value).toRat? =
      datumValue? (Interchange.binary32.decode
        (Isa.riscv.mul Interchange.binary32.encoding mode (f32 x).toStd (f32 y).toStd).1) :=
  mul32 _ rfl rfl _ mode x y hx hy inRange

theorem x86SSE_add64 (mode : RoundingMode) (x y : BitVec 64) {a b : ℚ}
    (hx : (f64 x).toRat? = some a) (hy : (f64 y).toRat? = some b)
    (inRange : NoExponentOverflow .binary64 (Rounding.roundUnpacked .binary64 mode
      (Rounding.addExact mode (f64 x).model.unpack (f64 y).model.unpack))) :
    (f64 ((Profile.x86SSE {}).add .binary64 mode x y).value).toRat? =
      datumValue? (Interchange.binary64.decode
        (Isa.x86SSE.add Interchange.binary64.encoding mode (f64 x).toStd (f64 y).toStd).1) :=
  add64 _ rfl rfl _ mode x y hx hy inRange

theorem riscvFD_add64 (mode : RoundingMode) (x y : BitVec 64) {a b : ℚ}
    (hx : (f64 x).toRat? = some a) (hy : (f64 y).toRat? = some b)
    (inRange : NoExponentOverflow .binary64 (Rounding.roundUnpacked .binary64 mode
      (Rounding.addExact mode (f64 x).model.unpack (f64 y).model.unpack))) :
    (f64 ((Profile.riscvFD).add .binary64 mode x y).value).toRat? =
      datumValue? (Interchange.binary64.decode
        (Isa.riscv.add Interchange.binary64.encoding mode (f64 x).toStd (f64 y).toStd).1) :=
  add64 _ rfl rfl _ mode x y hx hy inRange

theorem x86SSE_sub64 (mode : RoundingMode) (x y : BitVec 64) {a b : ℚ}
    (hx : (f64 x).toRat? = some a) (hy : (f64 y).toRat? = some b)
    (inRange : NoExponentOverflow .binary64 (Rounding.roundUnpacked .binary64 mode
      (Rounding.addExact mode (f64 x).model.unpack (f64 y).model.unpack.neg))) :
    (f64 ((Profile.x86SSE {}).sub .binary64 mode x y).value).toRat? =
      datumValue? (Interchange.binary64.decode
        (Isa.x86SSE.sub Interchange.binary64.encoding mode (f64 x).toStd (f64 y).toStd).1) :=
  sub64 _ rfl rfl _ mode x y hx hy inRange

theorem riscvFD_sub64 (mode : RoundingMode) (x y : BitVec 64) {a b : ℚ}
    (hx : (f64 x).toRat? = some a) (hy : (f64 y).toRat? = some b)
    (inRange : NoExponentOverflow .binary64 (Rounding.roundUnpacked .binary64 mode
      (Rounding.addExact mode (f64 x).model.unpack (f64 y).model.unpack.neg))) :
    (f64 ((Profile.riscvFD).sub .binary64 mode x y).value).toRat? =
      datumValue? (Interchange.binary64.decode
        (Isa.riscv.sub Interchange.binary64.encoding mode (f64 x).toStd (f64 y).toStd).1) :=
  sub64 _ rfl rfl _ mode x y hx hy inRange

theorem x86SSE_mul64 (mode : RoundingMode) (x y : BitVec 64) {a b : ℚ}
    (hx : (f64 x).toRat? = some a) (hy : (f64 y).toRat? = some b)
    (inRange : NoExponentOverflow .binary64 (Rounding.roundUnpacked .binary64 mode
      (Rounding.mulExact (f64 x).model.unpack (f64 y).model.unpack))) :
    (f64 ((Profile.x86SSE {}).mul .binary64 mode x y).value).toRat? =
      datumValue? (Interchange.binary64.decode
        (Isa.x86SSE.mul Interchange.binary64.encoding mode (f64 x).toStd (f64 y).toStd).1) :=
  mul64 _ rfl rfl _ mode x y hx hy inRange

theorem riscvFD_mul64 (mode : RoundingMode) (x y : BitVec 64) {a b : ℚ}
    (hx : (f64 x).toRat? = some a) (hy : (f64 y).toRat? = some b)
    (inRange : NoExponentOverflow .binary64 (Rounding.roundUnpacked .binary64 mode
      (Rounding.mulExact (f64 x).model.unpack (f64 y).model.unpack))) :
    (f64 ((Profile.riscvFD).mul .binary64 mode x y).value).toRat? =
      datumValue? (Interchange.binary64.decode
        (Isa.riscv.mul Interchange.binary64.encoding mode (f64 x).toStd (f64 y).toStd).1) :=
  mul64 _ rfl rfl _ mode x y hx hy inRange

end Silmaril.Numeric.Ieee754.Std.ProfileBridge
