module

public import Silmaril.Numeric.Ieee754.Operations

/-!
# Binary interchange inspection and ordering

IEEE 754-2019 §5.7.2 requires ten-way classification, format radix, canonical
encoding inspection, and total ordering with and without signs. `DatumClass`
distinguishes both zero signs and quiet versus signaling NaNs. The original
five-way `Class` remains useful for arithmetic cases.

Every binary32/binary64 interchange bit pattern is a canonical IEEE encoding
(§3.4). Consequently `isCanonical` is true even for signaling NaNs or arbitrary
NaN payloads. This predicate is distinct from the WebAssembly payload invariant
`IsNonNaNOrCanonicalNaN` and the `Canonicalized` refinement.

The existing `totalOrder` follows IEEE §5.10's bitwise order, including reversed
NaN quietness/payload order for negative NaNs. Its laws below apply to every raw
encoding, including signaling NaNs; no arithmetic model canonicalization is
involved. `totalOrderMag` ignores only the sign, so its antisymmetry identifies
absolute encodings rather than the original values. All inspection operations
are non-computational and signal no exceptions (§5.7.2).

Reference: <https://standards.ieee.org/ieee/754/6210/>.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754

/-- The ten mutually exclusive IEEE classes from §5.7.2. -/
inductive DatumClass where
  | signalingNaN
  | quietNaN
  | negativeInfinity
  | negativeNormal
  | negativeSubnormal
  | negativeZero
  | positiveZero
  | positiveSubnormal
  | positiveNormal
  | positiveInfinity
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

private def bitOrderKey {w : Nat} (x : BitVec (w + 1)) : BitVec (w + 1) :=
  if x.msb then ~~~x else x ^^^ BitVec.twoPow (w + 1) w
private theorem bitOrderKey_msb {w : Nat} (x : BitVec (w + 1)) :
    (bitOrderKey x).msb = !x.msb := by
  unfold bitOrderKey
  have hm : (BitVec.twoPow (w + 1) w).msb = true := by
    simp [BitVec.msb_eq_getLsbD_last]
  cases hx : x.msb <;> simp [hx, hm]
private theorem bitOrderKey_injective {w : Nat} : Function.Injective (@bitOrderKey w) := by
  intro x y h
  have hs : x.msb = y.msb := by
    have hh := congrArg BitVec.msb h
    simp only [bitOrderKey_msb] at hh
    simpa using congrArg Bool.not hh
  unfold bitOrderKey at h
  rw [hs] at h
  cases hy : y.msb
  · simp only [hy, Bool.false_eq_true, ↓reduceIte] at h
    exact (BitVec.xor_left_inj _).mp h
  · simp only [hy, ↓reduceIte] at h
    exact BitVec.not_inj.mp h

private theorem bit_abs_neg {w : Nat} (x mask : BitVec w) :
    (x ^^^ mask) &&& ~~~mask = x &&& ~~~mask := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_and, BitVec.getElem_xor, BitVec.getElem_not]
  cases x[i] <;> cases mask[i] <;> rfl

private theorem bit_abs_copySign {w : Nat} (x y mask : BitVec w) :
    ((x &&& ~~~mask) ||| (y &&& mask)) &&& ~~~mask = x &&& ~~~mask := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not]
  cases x[i] <;> cases y[i] <;> cases mask[i] <;> rfl

private theorem bit_copySign_self {w : Nat} (x mask : BitVec w) :
    (x &&& ~~~mask) ||| (x &&& mask) = x := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not]
  cases x[i] <;> cases mask[i] <;> rfl

namespace F32

/-- IEEE's full ten-way datum classification, retaining signed categories. -/
def classifyDatum (x : F32) : DatumClass :=
  match x.classification with
  | .nan => if x.isSignalingNaN then .signalingNaN else .quietNaN
  | .infinity => if x.signBit then .negativeInfinity else .positiveInfinity
  | .normal => if x.signBit then .negativeNormal else .positiveNormal
  | .subnormal => if x.signBit then .negativeSubnormal else .positiveSubnormal
  | .zero => if x.signBit then .negativeZero else .positiveZero

/-- The radix of this binary format (IEEE §5.7.2). -/
def radix (_ : F32) : Nat := 2

/-- Every raw encoding is canonical in IEEE's binary interchange sense.
This does not restrict NaN payloads or require a quiet NaN. -/
def isCanonical (_ : F32) : Bool := true

/-- Total order on absolute encodings (IEEE §5.7.2 and §5.10). -/
def totalOrderMag (x y : F32) : Bool := totalOrder (abs x) (abs y)

/-- The unsigned order key for IEEE totalOrder. Negative encodings are complemented;
nonnegative encodings have the high bit set. This is a bijection on raw bits. -/
def orderKey (x : F32) : UInt32 :=
  if x.signBit then ~~~x.bits else x.bits ^^^ 0x80000000

/-- The bit-level definition of totalOrder is unsigned comparison of its keys. -/
theorem totalOrder_eq (x y : F32) : totalOrder x y = decide (x.orderKey ≤ y.orderKey) := rfl

@[simp] theorem totalOrder_iff (x y : F32) :
    totalOrder x y = true ↔ x.orderKey ≤ y.orderKey := by simp [totalOrder_eq]

/-- The extracted interchange sign agrees with the most significant raw bit. -/
theorem signBit_eq_msb (x : F32) : x.signBit = x.bits.toBitVec.msb := by
  apply Bool.eq_iff_iff.mpr
  simp only [signBit, bne_iff_ne, UInt32.ne_iff_toBitVec_ne, UInt32.toBitVec_and]
  change x.bits.toBitVec &&& BitVec.twoPow 32 31 ≠ 0 ↔ x.bits.toBitVec.msb = true
  rw [BitVec.and_twoPow]
  change (if x.bits.toBitVec.msb then BitVec.twoPow 32 31 else 0) ≠ 0 ↔
    x.bits.toBitVec.msb = true
  cases x.bits.toBitVec.msb <;> simp [BitVec.twoPow]

private theorem orderKey_toBitVec (x : F32) :
    x.orderKey.toBitVec = bitOrderKey (w := 31) x.bits.toBitVec := by
  unfold orderKey bitOrderKey
  rw [signBit_eq_msb]
  cases x.bits.toBitVec.msb <;> rfl

/-- Distinct raw encodings have distinct order keys, including both zeros and all NaNs. -/
theorem orderKey_injective : Function.Injective orderKey := by
  intro x y h
  have hbits : x.bits.toBitVec = y.bits.toBitVec :=
    bitOrderKey_injective (w := 31) (by
      simpa only [orderKey_toBitVec] using congrArg UInt32.toBitVec h)
  have hraw := UInt32.eq_of_toBitVec_eq hbits
  cases x
  cases y
  cases hraw
  rfl

@[simp] theorem totalOrder_refl (x : F32) : totalOrder x x = true :=
  (totalOrder_iff x x).mpr (UInt32.le_refl _)

theorem totalOrder_trans {x y z : F32} (hxy : totalOrder x y = true)
    (hyz : totalOrder y z = true) : totalOrder x z = true :=
  (totalOrder_iff x z).mpr (UInt32.le_trans
    ((totalOrder_iff x y).mp hxy) ((totalOrder_iff y z).mp hyz))

theorem totalOrder_total (x y : F32) : totalOrder x y = true ∨ totalOrder y x = true := by
  rcases UInt32.le_total x.orderKey y.orderKey with h | h
  · exact Or.inl ((totalOrder_iff x y).mpr h)
  · exact Or.inr ((totalOrder_iff y x).mpr h)

/-- Antisymmetry uses raw encoding equality, rather than IEEE numeric equality. -/
theorem totalOrder_antisymm {x y : F32} (hxy : totalOrder x y = true)
    (hyx : totalOrder y x = true) : x = y :=
  orderKey_injective (UInt32.le_antisymm
    ((totalOrder_iff x y).mp hxy) ((totalOrder_iff y x).mp hyx))

theorem totalOrder_both_iff (x y : F32) :
    totalOrder x y = true ∧ totalOrder y x = true ↔ x = y := by
  constructor
  · rintro ⟨hxy, hyx⟩
    exact totalOrder_antisymm hxy hyx
  · rintro rfl
    exact ⟨totalOrder_refl x, totalOrder_refl x⟩

/-- Negating twice preserves every encoding, including signaling NaN payloads. -/
@[simp] theorem neg_neg (x : F32) : neg (neg x) = x := by
  cases x
  simp [neg, UInt32.xor_assoc]

@[simp] theorem abs_neg (x : F32) : abs (neg x) = abs x := by
  simp only [neg, abs, F32.mk.injEq]
  apply UInt32.eq_of_toBitVec_eq
  change (x.bits.toBitVec ^^^ (0x80000000#32)) &&& ~~~(0x80000000#32) =
    x.bits.toBitVec &&& ~~~(0x80000000#32)
  exact bit_abs_neg _ _

@[simp] theorem abs_abs (x : F32) : abs (abs x) = abs x := by
  simp [abs, UInt32.and_assoc]

@[simp] theorem abs_copySign (x y : F32) : abs (copySign x y) = abs x := by
  simp only [abs, copySign, F32.mk.injEq]
  apply UInt32.eq_of_toBitVec_eq
  change ((x.bits.toBitVec &&& ~~~(0x80000000#32)) |||
    (y.bits.toBitVec &&& (0x80000000#32))) &&& ~~~(0x80000000#32) =
    x.bits.toBitVec &&& ~~~(0x80000000#32)
  exact bit_abs_copySign _ _ _

@[simp] theorem copySign_self (x : F32) : copySign x x = x := by
  cases x with
  | mk bits =>
    simp only [copySign, F32.mk.injEq]
    apply UInt32.eq_of_toBitVec_eq
    change (bits.toBitVec &&& ~~~(0x80000000#32)) |||
      (bits.toBitVec &&& (0x80000000#32)) = bits.toBitVec
    exact bit_copySign_self _ _

@[simp] theorem signBit_copySign (x y : F32) : (copySign x y).signBit = y.signBit := by
  simp only [signBit_eq_msb, copySign, UInt32.toBitVec_or, UInt32.toBitVec_and,
    BitVec.msb_or, BitVec.msb_and]
  change (x.bits.toBitVec.msb && false || y.bits.toBitVec.msb && true) = y.bits.toBitVec.msb
  simp

@[simp] theorem signBit_neg (x : F32) : (neg x).signBit = !x.signBit := by
  simp only [signBit_eq_msb, neg, UInt32.toBitVec_xor, BitVec.msb_xor]
  change (x.bits.toBitVec.msb ^^ true) = !x.bits.toBitVec.msb
  simp

@[simp] theorem signBit_abs (x : F32) : (abs x).signBit = false := by
  simp only [signBit_eq_msb, abs, UInt32.toBitVec_and, BitVec.msb_and]
  change (x.bits.toBitVec.msb && false) = false
  simp

@[simp] theorem totalOrderMag_refl (x : F32) : totalOrderMag x x = true := totalOrder_refl _

theorem totalOrderMag_trans {x y z : F32} (hxy : totalOrderMag x y = true)
    (hyz : totalOrderMag y z = true) : totalOrderMag x z = true :=
  totalOrder_trans hxy hyz

theorem totalOrderMag_total (x y : F32) :
    totalOrderMag x y = true ∨ totalOrderMag y x = true := totalOrder_total _ _

theorem totalOrderMag_antisymm {x y : F32} (hxy : totalOrderMag x y = true)
    (hyx : totalOrderMag y x = true) : abs x = abs y := totalOrder_antisymm hxy hyx

theorem totalOrderMag_both_iff (x y : F32) :
    totalOrderMag x y = true ∧ totalOrderMag y x = true ↔ abs x = abs y :=
  totalOrder_both_iff _ _

@[simp] theorem totalOrderMag_neg_left (x y : F32) :
    totalOrderMag (neg x) y = totalOrderMag x y := by simp [totalOrderMag]

@[simp] theorem totalOrderMag_neg_right (x y : F32) :
    totalOrderMag x (neg y) = totalOrderMag x y := by simp [totalOrderMag]

@[simp] theorem totalOrderMag_copySign_left (x y z : F32) :
    totalOrderMag (copySign x z) y = totalOrderMag x y := by simp [totalOrderMag]

@[simp] theorem totalOrderMag_copySign_right (x y z : F32) :
    totalOrderMag x (copySign y z) = totalOrderMag x y := by simp [totalOrderMag]

@[simp] theorem radix_eq_two (x : F32) : radix x = 2 := rfl
@[simp] theorem isCanonical_eq_true (x : F32) : isCanonical x = true := rfl

end F32

namespace F64

/-- IEEE's full ten-way datum classification, retaining signed categories. -/
def classifyDatum (x : F64) : DatumClass :=
  match x.classification with
  | .nan => if x.isSignalingNaN then .signalingNaN else .quietNaN
  | .infinity => if x.signBit then .negativeInfinity else .positiveInfinity
  | .normal => if x.signBit then .negativeNormal else .positiveNormal
  | .subnormal => if x.signBit then .negativeSubnormal else .positiveSubnormal
  | .zero => if x.signBit then .negativeZero else .positiveZero

/-- The radix of this binary format (IEEE §5.7.2). -/
def radix (_ : F64) : Nat := 2

/-- Every raw encoding is canonical in IEEE's binary interchange sense.
This does not restrict NaN payloads or require a quiet NaN. -/
def isCanonical (_ : F64) : Bool := true

/-- Total order on absolute encodings (IEEE §5.7.2 and §5.10). -/
def totalOrderMag (x y : F64) : Bool := totalOrder (abs x) (abs y)

/-- The unsigned order key for IEEE totalOrder. Negative encodings are complemented;
nonnegative encodings have the high bit set. This is a bijection on raw bits. -/
def orderKey (x : F64) : UInt64 :=
  if x.signBit then ~~~x.bits else x.bits ^^^ 0x8000000000000000

/-- The bit-level definition of totalOrder is unsigned comparison of its keys. -/
theorem totalOrder_eq (x y : F64) : totalOrder x y = decide (x.orderKey ≤ y.orderKey) := rfl

@[simp] theorem totalOrder_iff (x y : F64) :
    totalOrder x y = true ↔ x.orderKey ≤ y.orderKey := by simp [totalOrder_eq]

/-- The extracted interchange sign agrees with the most significant raw bit. -/
theorem signBit_eq_msb (x : F64) : x.signBit = x.bits.toBitVec.msb := by
  apply Bool.eq_iff_iff.mpr
  simp only [signBit, bne_iff_ne, UInt64.ne_iff_toBitVec_ne, UInt64.toBitVec_and]
  change x.bits.toBitVec &&& BitVec.twoPow 64 63 ≠ 0 ↔ x.bits.toBitVec.msb = true
  rw [BitVec.and_twoPow]
  change (if x.bits.toBitVec.msb then BitVec.twoPow 64 63 else 0) ≠ 0 ↔
    x.bits.toBitVec.msb = true
  cases x.bits.toBitVec.msb <;> simp [BitVec.twoPow]

private theorem orderKey_toBitVec (x : F64) :
    x.orderKey.toBitVec = bitOrderKey (w := 63) x.bits.toBitVec := by
  unfold orderKey bitOrderKey
  rw [signBit_eq_msb]
  cases x.bits.toBitVec.msb <;> rfl

/-- Distinct raw encodings have distinct order keys, including both zeros and all NaNs. -/
theorem orderKey_injective : Function.Injective orderKey := by
  intro x y h
  have hbits : x.bits.toBitVec = y.bits.toBitVec :=
    bitOrderKey_injective (w := 63) (by
      simpa only [orderKey_toBitVec] using congrArg UInt64.toBitVec h)
  have hraw := UInt64.eq_of_toBitVec_eq hbits
  cases x
  cases y
  cases hraw
  rfl

@[simp] theorem totalOrder_refl (x : F64) : totalOrder x x = true :=
  (totalOrder_iff x x).mpr (UInt64.le_refl _)

theorem totalOrder_trans {x y z : F64} (hxy : totalOrder x y = true)
    (hyz : totalOrder y z = true) : totalOrder x z = true :=
  (totalOrder_iff x z).mpr (UInt64.le_trans
    ((totalOrder_iff x y).mp hxy) ((totalOrder_iff y z).mp hyz))

theorem totalOrder_total (x y : F64) : totalOrder x y = true ∨ totalOrder y x = true := by
  rcases UInt64.le_total x.orderKey y.orderKey with h | h
  · exact Or.inl ((totalOrder_iff x y).mpr h)
  · exact Or.inr ((totalOrder_iff y x).mpr h)

/-- Antisymmetry uses raw encoding equality, rather than IEEE numeric equality. -/
theorem totalOrder_antisymm {x y : F64} (hxy : totalOrder x y = true)
    (hyx : totalOrder y x = true) : x = y :=
  orderKey_injective (UInt64.le_antisymm
    ((totalOrder_iff x y).mp hxy) ((totalOrder_iff y x).mp hyx))

theorem totalOrder_both_iff (x y : F64) :
    totalOrder x y = true ∧ totalOrder y x = true ↔ x = y := by
  constructor
  · rintro ⟨hxy, hyx⟩
    exact totalOrder_antisymm hxy hyx
  · rintro rfl
    exact ⟨totalOrder_refl x, totalOrder_refl x⟩

/-- Negating twice preserves every encoding, including signaling NaN payloads. -/
@[simp] theorem neg_neg (x : F64) : neg (neg x) = x := by
  cases x
  simp [neg, UInt64.xor_assoc]

@[simp] theorem abs_neg (x : F64) : abs (neg x) = abs x := by
  simp only [neg, abs, F64.mk.injEq]
  apply UInt64.eq_of_toBitVec_eq
  change (x.bits.toBitVec ^^^ (0x8000000000000000#64)) &&& ~~~(0x8000000000000000#64) =
    x.bits.toBitVec &&& ~~~(0x8000000000000000#64)
  exact bit_abs_neg _ _

@[simp] theorem abs_abs (x : F64) : abs (abs x) = abs x := by
  simp [abs, UInt64.and_assoc]

@[simp] theorem abs_copySign (x y : F64) : abs (copySign x y) = abs x := by
  simp only [abs, copySign, F64.mk.injEq]
  apply UInt64.eq_of_toBitVec_eq
  change ((x.bits.toBitVec &&& ~~~(0x8000000000000000#64)) |||
    (y.bits.toBitVec &&& (0x8000000000000000#64))) &&& ~~~(0x8000000000000000#64) =
    x.bits.toBitVec &&& ~~~(0x8000000000000000#64)
  exact bit_abs_copySign _ _ _

@[simp] theorem copySign_self (x : F64) : copySign x x = x := by
  cases x with
  | mk bits =>
    simp only [copySign, F64.mk.injEq]
    apply UInt64.eq_of_toBitVec_eq
    change (bits.toBitVec &&& ~~~(0x8000000000000000#64)) |||
      (bits.toBitVec &&& (0x8000000000000000#64)) = bits.toBitVec
    exact bit_copySign_self _ _

@[simp] theorem signBit_copySign (x y : F64) : (copySign x y).signBit = y.signBit := by
  simp only [signBit_eq_msb, copySign, UInt64.toBitVec_or, UInt64.toBitVec_and,
    BitVec.msb_or, BitVec.msb_and]
  change (x.bits.toBitVec.msb && false || y.bits.toBitVec.msb && true) = y.bits.toBitVec.msb
  simp

@[simp] theorem signBit_neg (x : F64) : (neg x).signBit = !x.signBit := by
  simp only [signBit_eq_msb, neg, UInt64.toBitVec_xor, BitVec.msb_xor]
  change (x.bits.toBitVec.msb ^^ true) = !x.bits.toBitVec.msb
  simp

@[simp] theorem signBit_abs (x : F64) : (abs x).signBit = false := by
  simp only [signBit_eq_msb, abs, UInt64.toBitVec_and, BitVec.msb_and]
  change (x.bits.toBitVec.msb && false) = false
  simp

@[simp] theorem totalOrderMag_refl (x : F64) : totalOrderMag x x = true := totalOrder_refl _

theorem totalOrderMag_trans {x y z : F64} (hxy : totalOrderMag x y = true)
    (hyz : totalOrderMag y z = true) : totalOrderMag x z = true :=
  totalOrder_trans hxy hyz

theorem totalOrderMag_total (x y : F64) :
    totalOrderMag x y = true ∨ totalOrderMag y x = true := totalOrder_total _ _

theorem totalOrderMag_antisymm {x y : F64} (hxy : totalOrderMag x y = true)
    (hyx : totalOrderMag y x = true) : abs x = abs y := totalOrder_antisymm hxy hyx

theorem totalOrderMag_both_iff (x y : F64) :
    totalOrderMag x y = true ∧ totalOrderMag y x = true ↔ abs x = abs y :=
  totalOrder_both_iff _ _

@[simp] theorem totalOrderMag_neg_left (x y : F64) :
    totalOrderMag (neg x) y = totalOrderMag x y := by simp [totalOrderMag]

@[simp] theorem totalOrderMag_neg_right (x y : F64) :
    totalOrderMag x (neg y) = totalOrderMag x y := by simp [totalOrderMag]

@[simp] theorem totalOrderMag_copySign_left (x y z : F64) :
    totalOrderMag (copySign x z) y = totalOrderMag x y := by simp [totalOrderMag]

@[simp] theorem totalOrderMag_copySign_right (x y z : F64) :
    totalOrderMag x (copySign y z) = totalOrderMag x y := by simp [totalOrderMag]

@[simp] theorem radix_eq_two (x : F64) : radix x = 2 := rfl
@[simp] theorem isCanonical_eq_true (x : F64) : isCanonical x = true := rfl

end F64

/-! The classification has all ten cases, and binary encoding canonicality does
not depend on the canonical-NaN payload restriction. -/

example : F32.classifyDatum ⟨0x7f800001⟩ = .signalingNaN := by decide
example : F32.classifyDatum ⟨0xffc00001⟩ = .quietNaN := by decide
example : F32.classifyDatum ⟨0xff800000⟩ = .negativeInfinity := by decide
example : F32.classifyDatum ⟨0xbf800000⟩ = .negativeNormal := by decide
example : F32.classifyDatum ⟨0x80000001⟩ = .negativeSubnormal := by decide
example : F32.classifyDatum ⟨0x80000000⟩ = .negativeZero := by decide
example : F32.classifyDatum ⟨0⟩ = .positiveZero := by decide
example : F32.classifyDatum ⟨1⟩ = .positiveSubnormal := by decide
example : F32.classifyDatum ⟨0x3f800000⟩ = .positiveNormal := by decide
example : F32.classifyDatum ⟨0x7f800000⟩ = .positiveInfinity := by decide
example : F64.classifyDatum ⟨0x7ff0000000000001⟩ = .signalingNaN := by decide
example : F64.classifyDatum ⟨0x8000000000000000⟩ = .negativeZero := by decide
example : F32.isCanonical ⟨0x7f800001⟩ = true ∧
    ¬(F32.ofBits 0x7f800001).IsNonNaNOrCanonicalNaN := by decide
example : F64.totalOrderMag ⟨0xbff0000000000000⟩ ⟨0x3ff0000000000000⟩ = true := by decide

end Silmaril.Numeric.Ieee754
