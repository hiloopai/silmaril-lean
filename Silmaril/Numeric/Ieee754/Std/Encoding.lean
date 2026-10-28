module

public import Silmaril.Numeric.Ieee754.Std.Sqrt

/-!
# Bit encodings: IEEE interchange formats and x87 double extended

`Fields` is an encoding split into sign, biased exponent and significand field.
An `Encoding` packages a `BinFormat` with decoding to value-level `Datum`s,
encoding of non-NaN data, and the NaN predicates and quieting used by NaN
policies (`Std.NaN`).

*Interchange formats* (IEEE 754-2019 §3.4): `w` exponent bits and `t` trailing
significand bits; binary16/32/64/128 and bfloat16 are instances. The
significand's leading bit is implicit.

*x87 double extended* (Intel SDM Vol. 1 §4.2.2, §8.2.2, Table 8-3): 15
exponent bits and a 64-bit significand with an *explicit* integer bit `J`.
Encodings outside the IEEE value set have their own classes (`X87Class`):
pseudo-denormals (exponent 0, `J = 1`) denote `M * 2^(-16445)` like denormals
and are accepted as operands by the x87 FPU; unnormals (exponent in range,
`J = 0`), pseudo-infinities and pseudo-NaNs (all-ones exponent, `J = 0`) are
invalid operands on the 80387 and later. SoftFloat instead reads them by value
(unnormals) or ignores `J` (all-ones exponent). Both readings are variants
(`X87Reading`), and the chaotic variant (`Std.NaN`) allows either.
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Std

open Silmaril.Numeric.Ieee754

/-- Sign, biased exponent and significand field of an encoding. -/
structure Fields where
  sign : Bool
  exp : ℕ
  frac : ℕ
  deriving DecidableEq, Repr

/-- A bit encoding of a binary format. -/
structure Encoding where
  fmt : BinFormat
  expBits : ℕ
  fracBits : ℕ
  decode : Fields → Datum
  /-- Encoding of a non-NaN datum (NaN encodings are chosen by a NaN policy). -/
  encode : Datum → Fields
  isNaN : Fields → Bool
  /-- Quiet NaN encodings. -/
  isQuiet : Fields → Bool
  /-- Quieting of a NaN encoding, preserving its payload. -/
  quiet : Fields → Fields
  isQuiet_quiet : ∀ b, isNaN b = true → isNaN (quiet b) = true ∧ isQuiet (quiet b) = true
  /-- Decoded finite magnitudes are nonnegative. -/
  decode_nonneg : ∀ b s m, decode b = .fin s m → 0 ≤ m
  /-- Number of payload bits below the quiet bit position, counted as in
  SoftFloat's common NaN form (the explicit integer bit is not payload). -/
  payloadBits : ℕ
  /-- The default NaN of a given sign. -/
  defaultNaN : Bool → Fields
  defaultNaN_quiet : ∀ s, isNaN (defaultNaN s) = true ∧ isQuiet (defaultNaN s) = true
  /-- Quieting an all-ones exponent encoding gives a quiet NaN, whatever the payload. -/
  quiet_allOnes : ∀ s f, isNaN (quiet ⟨s, 2 ^ expBits - 1, f⟩) = true ∧
    isQuiet (quiet ⟨s, 2 ^ expBits - 1, f⟩) = true

namespace Fields

/-- Pack into a natural number: sign, exponent, then significand field. -/
def toNat (E : Encoding) (b : Fields) : ℕ :=
  (if b.sign then 2 ^ (E.expBits + E.fracBits) else 0) + b.exp * 2 ^ E.fracBits + b.frac

/-- Unpack a natural number. -/
def ofNat (E : Encoding) (n : ℕ) : Fields :=
  ⟨n.testBit (E.expBits + E.fracBits), n / 2 ^ E.fracBits % 2 ^ E.expBits, n % 2 ^ E.fracBits⟩

end Fields

/-! ## Interchange formats -/

/-- An IEEE interchange format with `w` exponent and `t` trailing significand bits. -/
structure Interchange where
  w : ℕ
  t : ℕ
  hw : 2 ≤ w := by decide
  ht : 1 ≤ t := by decide
  deriving DecidableEq, Repr

namespace Interchange

variable (F : Interchange)

theorem two_le_pow : 2 ≤ 2 ^ (F.w - 1) := by
  have := F.hw
  calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ (F.w - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

def fmt : BinFormat where
  prec := F.t + 1
  emax := 2 ^ (F.w - 1) - 1
  two_le_prec := by have := F.ht; omega
  one_le_emax := by have := F.two_le_pow; omega

def binary16 : Interchange := ⟨5, 10, by decide, by decide⟩
def binary32 : Interchange := ⟨8, 23, by decide, by decide⟩
def binary64 : Interchange := ⟨11, 52, by decide, by decide⟩
def binary128 : Interchange := ⟨15, 112, by decide, by decide⟩
def bfloat16 : Interchange := ⟨8, 7, by decide, by decide⟩

def expMax : ℕ := 2 ^ F.w - 1

def isNaN (b : Fields) : Bool := b.exp == F.expMax && b.frac != 0

def isQuiet (b : Fields) : Bool := F.isNaN b && b.frac.testBit (F.t - 1)

def quiet (b : Fields) : Fields := { b with frac := b.frac ||| 2 ^ (F.t - 1) }

/-- Value of an encoding (IEEE 754-2019 §3.4). -/
def decode (b : Fields) : Datum :=
  if b.exp = F.expMax then
    (if b.frac = 0 then .inf b.sign else .nan (!b.frac.testBit (F.t - 1)))
  else if b.exp = 0 then .fin b.sign ((b.frac : ℚ) * 2 ^ F.fmt.qmin)
  else .fin b.sign (((2 ^ F.t + b.frac : ℕ) : ℚ) * 2 ^ ((b.exp : ℤ) - 1 + F.fmt.qmin))

/-- Encoding of a non-NaN datum: the canonical (normalized or subnormal) form.
Finite magnitudes must be representable and at most `maxFinite`. -/
def encode : Datum → Fields
  | .inf s => ⟨s, F.expMax, 0⟩
  | .nan _ => ⟨false, F.expMax, 2 ^ (F.t - 1)⟩
  | .fin s r =>
    if r = 0 then ⟨s, 0, 0⟩ else
    let q := F.fmt.grid.qexpQ r
    let n := ⌊r / 2 ^ q⌋₊
    if n < 2 ^ F.t then ⟨s, 0, n⟩ else ⟨s, (q - F.fmt.qmin + 1).toNat, n - 2 ^ F.t⟩

theorem testBit_or_two_pow (n i : ℕ) : (n ||| 2 ^ i).testBit i = true := by
  simp [Nat.testBit_or, Nat.testBit_two_pow_self]

theorem or_two_pow_ne_zero (n i : ℕ) : n ||| 2 ^ i ≠ 0 := by
  intro h
  have := testBit_or_two_pow n i
  rw [h] at this
  simp at this

def encoding : Encoding where
  fmt := F.fmt
  expBits := F.w
  fracBits := F.t
  decode := F.decode
  encode := F.encode
  isNaN := F.isNaN
  isQuiet := F.isQuiet
  quiet := F.quiet
  isQuiet_quiet b h := by
    simp only [isNaN, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
    simp [isQuiet, isNaN, quiet, h.1]
  decode_nonneg b s m h := by
    unfold decode at h
    split_ifs at h <;> simp only [Datum.fin.injEq] at h <;>
      (obtain ⟨-, rfl⟩ := h; positivity)
  payloadBits := F.t
  defaultNaN s := ⟨s, F.expMax, 2 ^ (F.t - 1)⟩
  defaultNaN_quiet s := by
    simp [isNaN, isQuiet, Nat.testBit_two_pow_self]
  quiet_allOnes s f := by
    simp [isNaN, isQuiet, quiet, expMax]

end Interchange

/-! ## x87 double extended -/

/-- Classes of x87 double extended encodings (Intel SDM Vol. 1 Table 8-3). -/
inductive X87Class where
  | zero
  | denormal
  | pseudoDenormal
  | normal
  | unnormal
  | infinity
  | pseudoInfinity
  | quietNaN
  | signalingNaN
  | pseudoNaN
  deriving DecidableEq, Repr

/-- How encodings outside the IEEE value set are read. -/
inductive X87Reading where
  /-- 80387 and later: unnormals, pseudo-infinities and pseudo-NaNs are invalid
  operands (read as a signaling NaN, so every arithmetic use signals invalid
  and produces a NaN). -/
  | hardware
  /-- SoftFloat 3e `extF80`: unnormals by value, `J` ignored at exponent 0x7FFF. -/
  | softfloat
  deriving DecidableEq, Repr

namespace X87

def jBit : ℕ := 2 ^ 63
def expMax : ℕ := 0x7FFF

def classify (b : Fields) : X87Class :=
  let j := b.frac.testBit 63
  let low := b.frac % 2 ^ 63
  if b.exp = 0 then
    (if b.frac = 0 then .zero else if j then .pseudoDenormal else .denormal)
  else if b.exp = expMax then
    if !j then (if low = 0 then .pseudoInfinity else .pseudoNaN)
    else if low = 0 then .infinity
    else if b.frac.testBit 62 then .quietNaN else .signalingNaN
  else if j then .normal else .unnormal

/-- Value of a finite encoding, `M * 2^(E - 16383 - 63)` (`E = 1` for exponent 0). -/
def finiteValue (b : Fields) : ℚ :=
  (b.frac : ℚ) * 2 ^ ((max b.exp 1 : ℕ) - (16383 : ℤ) - 63)

def decode (reading : X87Reading) (b : Fields) : Datum :=
  match classify b, reading with
  | .zero, _ | .denormal, _ | .pseudoDenormal, _ | .normal, _ => .fin b.sign (finiteValue b)
  | .infinity, _ => .inf b.sign
  | .quietNaN, _ => .nan false
  | .signalingNaN, _ => .nan true
  | .unnormal, .softfloat => .fin b.sign (finiteValue b)
  | .pseudoInfinity, .softfloat => .inf b.sign
  | .pseudoNaN, .softfloat => .nan (!b.frac.testBit 62)
  | .unnormal, .hardware | .pseudoInfinity, .hardware | .pseudoNaN, .hardware => .nan true

def isNaN (reading : X87Reading) (b : Fields) : Bool :=
  match classify b, reading with
  | .quietNaN, _ | .signalingNaN, _ => true
  | .pseudoNaN, .softfloat => true
  | _, _ => false

/-- SoftFloat and the x87 FPU quiet a NaN by setting `J` and the quiet bit. -/
def quiet (b : Fields) : Fields := { b with frac := b.frac ||| 0xC000000000000000 }

def encode : Datum → Fields
  | .inf s => ⟨s, expMax, jBit⟩
  | .nan _ => ⟨true, expMax, 0xC000000000000000⟩
  | .fin s r =>
    if r = 0 then ⟨s, 0, 0⟩ else
    let q := BinFormat.x87Extended.grid.qexpQ r
    let n := ⌊r / 2 ^ q⌋₊
    if n < jBit then ⟨s, 0, n⟩ else ⟨s, (q + 16383 + 63).toNat, n⟩

theorem quiet_classify (b : Fields) (hexp : b.exp = expMax) :
    classify (quiet b) = .quietNaN := by
  have h63 : (b.frac ||| 0xC000000000000000).testBit 63 = true := by
    simp only [Nat.testBit_or, Bool.or_eq_true]; exact Or.inr (by decide)
  have h62 : (b.frac ||| 0xC000000000000000).testBit 62 = true := by
    simp only [Nat.testBit_or, Bool.or_eq_true]; exact Or.inr (by decide)
  have hlow : (b.frac ||| 0xC000000000000000) % 9223372036854775808 ≠ 0 := by
    intro h
    have : ((b.frac ||| 0xC000000000000000) % 2 ^ 63).testBit 62 = true := by
      rw [Nat.testBit_mod_two_pow]; simp [h62]
    norm_num at this
    rw [h] at this; simp at this
  simp [classify, quiet, hexp, expMax, h63, h62, hlow]

def encoding (reading : X87Reading) : Encoding where
  fmt := .x87Extended
  expBits := 15
  fracBits := 64
  decode := decode reading
  encode := encode
  isNaN := isNaN reading
  isQuiet b := classify b == .quietNaN
  quiet := quiet
  isQuiet_quiet b h := by
    have hexp : b.exp = expMax := by
      unfold isNaN classify at h
      split at h <;> simp_all <;> split_ifs at * <;> simp_all
    simp [isNaN, quiet_classify b hexp]
  decode_nonneg b s m h := by
    unfold decode at h
    split at h <;> simp only [Datum.fin.injEq, reduceCtorEq] at h <;>
      (obtain ⟨-, rfl⟩ := h; unfold finiteValue; positivity)
  payloadBits := 63
  defaultNaN s := ⟨s, expMax, 0xC000000000000000⟩
  defaultNaN_quiet s := by
    have h : classify ⟨s, expMax, 0xC000000000000000⟩ = .quietNaN := by cases s <;> decide
    cases reading <;> simp [isNaN, h]
  quiet_allOnes s f := by
    have h := quiet_classify ⟨s, 32767, f⟩ rfl
    cases reading <;> simp [isNaN, h]

end X87

end Silmaril.Numeric.Ieee754.Std
