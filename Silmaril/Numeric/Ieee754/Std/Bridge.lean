module

public import Silmaril.Numeric.Ieee754.Std.TestFloat
public import Silmaril.Numeric.Float.Ops
public import Silmaril.Numeric.Float.Instances
public import Silmaril.Numeric.Ieee754

/-!
# Bridges to Lean core's `Float.Model` and to `Numeric.Float` profiles

The repository's other floating-point models are kept unchanged:

* `Silmaril.Numeric.Ieee754.F32`/`F64` wrap Lean core's `Float32.Model` and
  `Float.Model` (round to nearest, ties to even; NaNs canonicalized);
* `Silmaril.Numeric.Float.Profile` (`Profile.x86SSE`, `Profile.riscvFD`, …) is a
  profile-parametric bit-level implementation on Lean core's `Float.Model.Format`,
  and `Silmaril.Numeric.Float.Wasm` proves which of its results WebAssembly admits.

This module states the correspondence with `Std` as executable agreement checks
(`agreeProfile`, `agreeCore`). They compare encodings and flags bit for bit on
the operands of a TestFloat vector line (the expected result is ignored), and are
run over vector samples at build time (`Std.BridgeTests`) and over the full
level-1 operand sets by `scripts/ieee754/BridgeCheck.lean`.

The proved bridges are `Std.CoreBridge` (the `Float.Model` rounding stage computes
the `Std` rounding in every format and direction; `F32`/`F64` arithmetic and Lean
core's model have the value of every result `Std` specifies) and `Std.WasmBridge`
(WebAssembly's NaN rule `NaNSpec.wasm` contains the x86 SSE and RISC-V NaN rules).
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Std.Bridge

open Silmaril.Numeric.Ieee754 Silmaril.Numeric.Ieee754.Std TestFloat
open Silmaril.Numeric.Float

/-- Lean core's format for an interchange format. -/
def coreFormat (F : Interchange) : Float.Model.Format where
  mantissaBitsWithoutImplicit := F.t
  hm := F.ht
  exponentBits := F.w
  he := F.hw

def interchange? : String → Option Interchange
  | "f16" => some .binary16
  | "f32" => some .binary32
  | "f64" => some .binary64
  | "f128" => some .binary128
  | _ => none

/-- The x86 FMA3 NaN rule observed in hardware for `a * b + c` with the operands in
expression order: first NaN operand; `fma(∞, 0, qNaN)` returns the addend without
signaling invalid. -/
def x86HardwareFmaNaNRule : FmaNaNRule where
  priority := [.multiplicand1, .multiplicand2, .addend]
  infZeroQuietNaNIsDefault := false
  infZeroQuietNaNInvalid := false

def numericIntFormat (t : String) : Option (Silmaril.Numeric.IntFormat × Std.IntFormat) :=
  match t with
  | "i32" => some (⟨32, .signed, by decide⟩, .signed 32)
  | "ui32" => some (⟨32, .unsigned, by decide⟩, .unsigned 32)
  | "i64" => some (⟨64, .signed, by decide⟩, .signed 64)
  | "ui64" => some (⟨64, .unsigned, by decide⟩, .unsigned 64)
  | _ => none

/-- Compare a `Numeric.Float` profile with a `Std` profile on the operands of one
vector line. `none` when the function is not covered. -/
def agreeProfile (p : Profile) (fmaRule : FmaNaNRule) (I : Isa) (fn : String)
    (mode : RoundingMode) (exact : Bool) (line : String) : Option Bool := do
  let words := (line.splitOn " ").filter (· ≠ "")
  let nums ← words.mapM parseHex?
  let parts := fn.splitOn "_"
  match parts with
  | [src, "to", dst] =>
    match interchange? src, interchange? dst, numericIntFormat dst, numericIntFormat src with
    | some F₁, some F₂, _, _ => do
      let a ← nums.head?
      let r₁ := p.convert (coreFormat F₁) (coreFormat F₂) mode (BitVec.ofNat _ a)
      let r₂ := I.convert F₁.encoding F₂.encoding mode (Fields.ofNat F₁.encoding a)
      pure (r₁.value.toNat == r₂.1.toNat F₂.encoding && r₁.flags == r₂.2)
    | some F, none, some (tn, ts), _ => do
      let a ← nums.head?
      let p' := { p with toIntSignalsInexact := exact }
      let r₁ := p'.toInt (coreFormat F) tn mode (BitVec.ofNat _ a)
      let r₂ := I.toInt F.encoding ts mode exact (Fields.ofNat F.encoding a)
      pure (r₁.value.toNat == twos tn.width r₂.1 && r₁.flags == r₂.2)
    | none, some F, _, some (tn, _) => do
      let a ← nums.head?
      let n : ℤ := if tn.signedness = .signed then ofTwos tn.width a else a
      let r₁ := p.ofInt (coreFormat F) mode n
      let r₂ := I.ofInt F.encoding mode n
      pure (r₁.value.toNat == r₂.1.toNat F.encoding && r₁.flags == r₂.2)
    | _, _, _, _ => none
  | src :: rest => do
    let F ← interchange? src
    let C := coreFormat F
    let E := F.encoding
    let op := "_".intercalate rest
    let bv (n : ℕ) : Float.Bits C := BitVec.ofNat _ n
    let fd (n : ℕ) : Fields := Fields.ofNat E n
    let same (r₁ : Outcome (Float.Bits C)) (r₂ : Fields × Flags) : Bool :=
      r₁.value.toNat == r₂.1.toNat E && r₁.flags == r₂.2
    match op, nums with
    | "add", a :: b :: _ => pure (same (p.add C mode (bv a) (bv b)) (I.add E mode (fd a) (fd b)))
    | "sub", a :: b :: _ => pure (same (p.sub C mode (bv a) (bv b)) (I.sub E mode (fd a) (fd b)))
    | "mul", a :: b :: _ => pure (same (p.mul C mode (bv a) (bv b)) (I.mul E mode (fd a) (fd b)))
    | "div", a :: b :: _ => pure (same (p.div C mode (bv a) (bv b)) (I.div E mode (fd a) (fd b)))
    | "sqrt", a :: _ => pure (same (p.sqrt C mode (bv a)) (I.sqrt E mode (fd a)))
    | "mulAdd", a :: b :: c :: _ =>
      pure (same (p.fmaWith C fmaRule mode (bv a) (bv b) (bv c)) (I.fma E mode (fd a) (fd b) (fd c)))
    | "roundToInt", a :: _ =>
      pure (same (p.roundToIntegral C mode exact (bv a)) (I.roundToIntegral E mode exact (fd a)))
    | "eq", a :: b :: _ => cmp C E false (bv a) (bv b) (fd a) (fd b)
    | "lt", a :: b :: _ => cmp C E true (bv a) (bv b) (fd a) (fd b)
    | "le_quiet", a :: b :: _ => cmp C E false (bv a) (bv b) (fd a) (fd b)
    | _, _ => none
  | _ => none
where
  cmp (C : Float.Model.Format) (E : Encoding) (signaling : Bool) (a b : Float.Bits C)
      (x y : Fields) : Option Bool :=
    let r₁ := p.compare signaling a b
    let r₂ := Isa.compare E signaling x y
    some (r₁.value == r₂.1 && r₁.flags == r₂.2)

/-- Compare Lean core's `Float32.Model`/`Float.Model` arithmetic (through the
`F32`/`F64` wrappers; round to nearest, ties to even) with `Std` x86 SSE on one
vector line: equal encodings, or both NaN (the core model canonicalizes NaNs and
has no flags). -/
def agreeCore (fn : String) (line : String) : Option Bool := do
  let words := (line.splitOn " ").filter (· ≠ "")
  let nums ← words.mapM parseHex?
  let I := Isa.x86SSE
  let mode := RoundingMode.nearestTiesToEven
  match fn.splitOn "_" with
  | ["f32", op] =>
    let E := Interchange.binary32.encoding
    let f (n : ℕ) : F32 := F32.ofBits (UInt32.ofNat n)
    let fd (n : ℕ) : Fields := Fields.ofNat E n
    let same (r₁ : F32) (r₂ : Fields × Flags) : Bool :=
      r₁.bits.toNat == r₂.1.toNat E || (r₁.isNaN && E.isNaN r₂.1)
    match op, nums with
    | "add", a :: b :: _ => pure (same (F32.add (f a) (f b)) (I.add E mode (fd a) (fd b)))
    | "sub", a :: b :: _ => pure (same (F32.sub (f a) (f b)) (I.sub E mode (fd a) (fd b)))
    | "mul", a :: b :: _ => pure (same (F32.mul (f a) (f b)) (I.mul E mode (fd a) (fd b)))
    | "div", a :: b :: _ => pure (same (F32.div (f a) (f b)) (I.div E mode (fd a) (fd b)))
    | "sqrt", a :: _ => pure (same (F32.sqrt (f a)) (I.sqrt E mode (fd a)))
    | "mulAdd", a :: b :: c :: _ =>
      pure (same (F32.fma (f a) (f b) (f c)) (I.fma E mode (fd a) (fd b) (fd c)))
    | _, _ => none
  | ["f64", op] =>
    let E := Interchange.binary64.encoding
    let f (n : ℕ) : F64 := F64.ofBits (UInt64.ofNat n)
    let fd (n : ℕ) : Fields := Fields.ofNat E n
    let same (r₁ : F64) (r₂ : Fields × Flags) : Bool :=
      r₁.bits.toNat == r₂.1.toNat E || (r₁.isNaN && E.isNaN r₂.1)
    match op, nums with
    | "add", a :: b :: _ => pure (same (F64.add (f a) (f b)) (I.add E mode (fd a) (fd b)))
    | "sub", a :: b :: _ => pure (same (F64.sub (f a) (f b)) (I.sub E mode (fd a) (fd b)))
    | "mul", a :: b :: _ => pure (same (F64.mul (f a) (f b)) (I.mul E mode (fd a) (fd b)))
    | "div", a :: b :: _ => pure (same (F64.div (f a) (f b)) (I.div E mode (fd a) (fd b)))
    | "sqrt", a :: _ => pure (same (F64.sqrt (f a)) (I.sqrt E mode (fd a)))
    | "mulAdd", a :: b :: c :: _ =>
      pure (same (F64.fma (f a) (f b) (f c)) (I.fma E mode (fd a) (fd b) (fd c)))
    | _, _ => none
  | _ => none

end Silmaril.Numeric.Ieee754.Std.Bridge
