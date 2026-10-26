module

public import Silmaril.Numeric.Ieee754.Std.EncodingCorrect

/-!
# Chaotic variants for state the exact profiles fix

The exact profiles of `Std.Isa` fix machine state that a program can change. Each
section below gives a sound coarse variant that leaves that state open, and proves
that the exact profile is contained in it, so a statement that does not know the
state can use the coarse variant.

* **MXCSR flush modes.** `Isa.x86SSE` is SSE/AVX arithmetic with `MXCSR.DAZ =
  MXCSR.FTZ = 0`. `Mxcsr.Spec m op` takes the flush bits as an explicit parameter:
  with both clear it is exactly `op` (`Mxcsr.spec_noFlush`); otherwise it is
  `Mxcsr.FlushChaos`, in which each operand with biased exponent `0` may be read as
  the signed zero (DAZ), a result with biased exponent at most `1` may be replaced
  by the signed zero (FTZ, which flushes results that are tiny after rounding),
  and the flags are left open. `Mxcsr.Unknown` (both bits possibly set) contains
  every setting (`Mxcsr.spec_le_unknown`) and the non-flushing result
  (`Mxcsr.flushChaos_self`). The x86-only denormal-operand flag `MXCSR.DE` is not
  part of `Flags` in any variant, so a semantics of MXCSR must treat it as unknown
  after an SSE operation.
* **`fma` NaN choice.** For SoftFloat's `8086-SSE` and for x87 the invalid product
  of `fma(∞, 0, NaN)` enters NaN selection as the default NaN (SoftFloat
  `propagateNaN(defaultNaN, c)`), which can win, so the NaN lattice inclusions for `fma`
  (`Isa.fma_spec`, `NaNSpec.propagating`) are relative to `Isa.fmaNaNOperands`,
  not to the operands `[x, y, z]`. `fma_softfloat8086SSE_not_propagating` and
  `fma_x87_not_propagating` (signaling addend) show that the operand-level reading
  fails.
  `Isa.FmaChaos` and `Isa.fma_chaos` (any NaN) are operand-independent.
* **x87 readings.** `X87.ReadingChaos` is the union of the 387+ hardware reading
  and SoftFloat's. `X87.ReadingAny` is the chaotic reading: any datum for the three
  non-IEEE classes (unnormal, pseudo-infinity, pseudo-NaN), the common reading
  otherwise. `X87.BinChaos` lifts it to two-operand arithmetic, and the x87 profile
  under both readings is contained in it (`X87.add_binChaos_hardware`,
  `X87.add_binChaos_softfloat`, and the same for `sub`, `mul`, `div`).
-/

@[expose] public section

namespace Silmaril.Numeric.Ieee754.Std

open Silmaril.Numeric.Ieee754

/-! ## MXCSR flush-to-zero and denormals-are-zero -/

/-- The MXCSR control bits that `Isa.x86SSE` fixes to `0`. Rounding control is the
explicit `RoundingMode` argument of every operation. -/
structure MxcsrFlush where
  daz : Bool
  ftz : Bool
  deriving DecidableEq, Repr

namespace Mxcsr

/-- `x'` is a possible reading of operand `x`: `x` itself, or, under DAZ, the signed
zero when the biased exponent is `0` (denormals, and zeros, which stay zeros). -/
def InputCand (daz : Bool) (x x' : Fields) : Prop :=
  x' = x ∨ (daz = true ∧ x.exp = 0 ∧ x' = ⟨x.sign, 0, 0⟩)

/-- `out` is a possible delivered result for the non-flushing result `r`: `r`
itself, or, under FTZ, the signed zero when `r` has biased exponent at most `1`
(every result that is tiny after rounding has this form). -/
def OutputCand (ftz : Bool) (r out : Fields) : Prop :=
  out = r ∨ (ftz = true ∧ r.exp ≤ 1 ∧ out = ⟨r.sign, 0, 0⟩)

/-- The chaotic flush semantics of an operation `op` on interchange encodings:
read the operands under DAZ, run the non-flushing operation, flush the result
under FTZ. The flags are left open. -/
def FlushChaos (m : MxcsrFlush) (op : List Fields → Fields × Flags) (args : List Fields)
    (out : Fields) (_fl : Flags) : Prop :=
  ∃ args', List.Forall₂ (InputCand m.daz) args args' ∧ OutputCand m.ftz (op args').1 out

/-- An SSE/AVX operation under MXCSR flush bits `m`: exact when neither flush bit is
set, chaotic otherwise. -/
def Spec (m : MxcsrFlush) (op : List Fields → Fields × Flags) (args : List Fields)
    (out : Fields) (fl : Flags) : Prop :=
  if m.daz = false ∧ m.ftz = false then (out, fl) = op args else FlushChaos m op args out fl

/-- Unknown flush bits. -/
def Unknown (op : List Fields → Fields × Flags) (args : List Fields) (out : Fields)
    (fl : Flags) : Prop :=
  FlushChaos ⟨true, true⟩ op args out fl

theorem spec_noFlush (op : List Fields → Fields × Flags) (args : List Fields) (out : Fields)
    (fl : Flags) : Spec ⟨false, false⟩ op args out fl ↔ (out, fl) = op args := by
  simp [Spec]

/-- The non-flushing result is a flush-chaos result, for every setting. -/
theorem flushChaos_self (m : MxcsrFlush) (op : List Fields → Fields × Flags)
    (args : List Fields) (fl : Flags) : FlushChaos m op args (op args).1 fl :=
  ⟨args, List.forall₂_same.mpr fun _ _ => Or.inl rfl, Or.inl rfl⟩

theorem flushChaos_mono {m : MxcsrFlush} {op : List Fields → Fields × Flags}
    {args : List Fields} {out : Fields} {fl fl' : Flags} (h : FlushChaos m op args out fl) :
    Unknown op args out fl' := by
  obtain ⟨args', ha, ho⟩ := h
  refine ⟨args', ha.imp fun x x' hx => ?_, ?_⟩
  · rcases hx with hx | ⟨-, hx⟩
    · exact Or.inl hx
    · exact Or.inr ⟨rfl, hx⟩
  · rcases ho with ho | ⟨-, ho⟩
    · exact Or.inl ho
    · exact Or.inr ⟨rfl, ho⟩

/-- Every MXCSR flush setting is contained in the unknown one. -/
theorem spec_le_unknown {m : MxcsrFlush} {op : List Fields → Fields × Flags}
    {args : List Fields} {out : Fields} {fl : Flags} (h : Spec m op args out fl) :
    Unknown op args out fl := by
  unfold Spec at h
  split_ifs at h
  · have hout : out = (op args).1 := by rw [← h]
    subst hout
    exact flushChaos_mono (flushChaos_self m op args fl)
  · exact flushChaos_mono h

/-- Two-operand operations as functions of an operand list. -/
def lift2 (f : Fields → Fields → Fields × Flags) : List Fields → Fields × Flags
  | [x, y] => f x y
  | _ => (⟨false, 0, 0⟩, {})

/-- The `Std` x86 SSE results satisfy the unknown-MXCSR variant. -/
theorem x86SSE_add_unknown (E : Encoding) (mode : RoundingMode) (x y : Fields) :
    Unknown (lift2 (Isa.x86SSE.add E mode)) [x, y] (Isa.x86SSE.add E mode x y).1
      (Isa.x86SSE.add E mode x y).2 :=
  flushChaos_mono (flushChaos_self ⟨false, false⟩ (lift2 (Isa.x86SSE.add E mode)) [x, y] {})

/-! Non-vacuity: under FTZ, halving the least binary32 normal may give `+0`
(the exact result is the subnormal `0x00400000`), and under DAZ `denormal + 1`
may be exactly `1`; without flushing neither is allowed. -/

local notation "E32" => Interchange.binary32.encoding

example : Unknown (lift2 (Isa.x86SSE.mul E32 .nearestTiesToEven))
    [Fields.ofNat E32 0x00800000, Fields.ofNat E32 0x3F000000] ⟨false, 0, 0⟩ {} := by
  refine ⟨[Fields.ofNat E32 0x00800000, Fields.ofNat E32 0x3F000000],
    List.forall₂_same.mpr fun _ _ => Or.inl rfl, Or.inr ⟨rfl, ?_, ?_⟩⟩ <;> decide +kernel

example : Unknown (lift2 (Isa.x86SSE.add E32 .nearestTiesToEven))
    [Fields.ofNat E32 0x00000001, Fields.ofNat E32 0x3F800000] (Fields.ofNat E32 0x3F800000)
    {} := by
  refine ⟨[⟨false, 0, 0⟩, Fields.ofNat E32 0x3F800000], ?_, Or.inl ?_⟩
  · refine List.Forall₂.cons (Or.inr ⟨rfl, by decide +kernel, by decide +kernel⟩) ?_
    exact List.Forall₂.cons (Or.inl rfl) List.Forall₂.nil
  · decide +kernel

example : ¬ Spec ⟨false, false⟩ (lift2 (Isa.x86SSE.mul E32 .nearestTiesToEven))
    [Fields.ofNat E32 0x00800000, Fields.ofNat E32 0x3F000000] ⟨false, 0, 0⟩ {} := by
  rw [spec_noFlush]; decide +kernel

end Mxcsr

/-! ## The `fma` NaN lattice is relative to `fmaNaNOperands` -/

namespace Isa

local notation "E32" => Interchange.binary32.encoding

/-- SoftFloat `8086-SSE`: `fma(+∞, +0, qNaN 0x7FC12345)` is the default NaN, which is
not one of the operands quieted. -/
theorem fma_softfloat8086SSE_not_propagating :
    ¬ NaNSpec.propagating E32
      [Fields.ofNat E32 0x7F800000, Fields.ofNat E32 0, Fields.ofNat E32 0x7FC12345]
      (softfloat8086SSE.fma E32 .nearestTiesToEven (Fields.ofNat E32 0x7F800000)
        (Fields.ofNat E32 0) (Fields.ofNat E32 0x7FC12345)).1 := by
  unfold NaNSpec.propagating NaNSpec.quietNaN
  decide +kernel

/-- The same for the x87 profile (SoftFloat `8086`) on binary32, with a signaling
addend: the quiet default NaN beats it, so the result is the default NaN rather than
the addend quieted. (With a quiet addend x87 picks the addend, which has the larger
significand or the positive sign.) -/
theorem fma_x87_not_propagating :
    ¬ NaNSpec.propagating E32
      [Fields.ofNat E32 0x7F800000, Fields.ofNat E32 0, Fields.ofNat E32 0x7F800001]
      (x87.fma E32 .nearestTiesToEven (Fields.ofNat E32 0x7F800000)
        (Fields.ofNat E32 0) (Fields.ofNat E32 0x7F800001)).1 := by
  unfold NaNSpec.propagating NaNSpec.quietNaN
  decide +kernel

/-- The x86 hardware rule does propagate the addend there. -/
example :
    NaNSpec.propagating E32
      [Fields.ofNat E32 0x7F800000, Fields.ofNat E32 0, Fields.ofNat E32 0x7FC12345]
      (x86SSE.fma E32 .nearestTiesToEven (Fields.ofNat E32 0x7F800000)
        (Fields.ofNat E32 0) (Fields.ofNat E32 0x7FC12345)).1 := by
  unfold NaNSpec.propagating NaNSpec.quietNaN
  decide +kernel

end Isa

/-! ## Chaotic x87 readings, lifted to arithmetic -/

namespace X87

/-- The non-IEEE classes, read differently by the 387+ hardware, SoftFloat and the
8087/287. -/
def nonIEEE (b : Fields) : Bool :=
  classify b == .unnormal || classify b == .pseudoInfinity || classify b == .pseudoNaN

/-- The chaotic reading: any datum for a non-IEEE class, the common reading of
SoftFloat and the 387+ hardware otherwise. -/
def ReadingAny (b : Fields) (d : Datum) : Prop := nonIEEE b = true ∨ d = decode .hardware b

theorem readingChaos_le_readingAny {b : Fields} {d : Datum} (h : ReadingChaos b d) :
    ReadingAny b d := by
  obtain ⟨r, rfl⟩ := h
  by_cases hn : nonIEEE b = true
  · exact Or.inl hn
  · refine Or.inr ?_
    cases r
    · rfl
    · simp only [nonIEEE, Bool.or_eq_true, beq_iff_eq, not_or] at hn
      exact (decode_hardware_eq_softfloat b hn.1.1 hn.1.2 hn.2).symm

/-- Chaotic two-operand x87 arithmetic: operands read by `ReadingAny`, any NaN. -/
def BinChaos (op : Datum → Datum → Exact ℚ) (mode : RoundingMode) (x y out : Fields)
    (fl : Flags) : Prop :=
  ∃ dx dy, ReadingAny x dx ∧ ReadingAny y dy ∧
    OpSpec (encoding .hardware) (NaNSpec.anyNaN (encoding .hardware)) .afterRounding mode
      [x, y] (op dx dy) out fl

/-- A quiet NaN of the SoftFloat reading is a NaN of the hardware reading, and both
readings share the format and the encoder, so specifications transfer. -/
theorem opSpec_softfloat_to_hardware {tin : TininessDetection} {mode : RoundingMode}
    {ins : List Fields} {e : Exact ℚ} {out : Fields} {fl : Flags}
    (h : OpSpec (encoding .softfloat) (NaNSpec.quietNaN (encoding .softfloat)) tin mode ins e
      out fl) :
    OpSpec (encoding .hardware) (NaNSpec.anyNaN (encoding .hardware)) tin mode ins e out fl := by
  obtain ⟨res, hd, hn, he⟩ := h
  refine ⟨res, hd, fun h' => ?_, he⟩
  have hq := (hn h').2
  simp only [encoding, beq_iff_eq] at hq
  simp [NaNSpec.anyNaN, encoding, isNaN, hq]

theorem binChaos_hardware {op : Datum → Datum → Exact ℚ} {mode : RoundingMode}
    {x y out : Fields} {fl : Flags}
    (h : OpSpec (encoding .hardware) (NaNSpec.anyNaN (encoding .hardware)) .afterRounding mode
      [x, y] (op (decode .hardware x) (decode .hardware y)) out fl) :
    BinChaos op mode x y out fl :=
  ⟨_, _, Or.inr rfl, Or.inr rfl, h⟩

theorem binChaos_softfloat {op : Datum → Datum → Exact ℚ} {mode : RoundingMode}
    {x y out : Fields} {fl : Flags}
    (h : OpSpec (encoding .softfloat) (NaNSpec.quietNaN (encoding .softfloat)) .afterRounding
      mode [x, y] (op (decode .softfloat x) (decode .softfloat y)) out fl) :
    BinChaos op mode x y out fl :=
  ⟨_, _, readingChaos_le_readingAny ⟨_, rfl⟩, readingChaos_le_readingAny ⟨_, rfl⟩,
    opSpec_softfloat_to_hardware h⟩

theorem nan_le_quietNaN (r : X87Reading) :
    NaNSpec.ofFun (Isa.x87.nan (encoding r)) ≤ NaNSpec.quietNaN (encoding r) :=
  (Isa.x87_nan_le_propagating _).trans (NaNSpec.propagating_le_quietNaN _)

theorem add_binChaos_hardware (mode : RoundingMode) (x y : Fields) :
    BinChaos (exactAdd mode) mode x y (Isa.x87.add (encoding .hardware) mode x y).1
      (Isa.x87.add (encoding .hardware) mode x y).2 :=
  binChaos_hardware (Isa.x87.add_chaos _ Isa.x87_nanSound mode x y)

theorem add_binChaos_softfloat (mode : RoundingMode) (x y : Fields) :
    BinChaos (exactAdd mode) mode x y (Isa.x87.add (encoding .softfloat) mode x y).1
      (Isa.x87.add (encoding .softfloat) mode x y).2 :=
  binChaos_softfloat ((Isa.x87.add_spec _ mode x y).mono (nan_le_quietNaN _))

theorem sub_binChaos_hardware (mode : RoundingMode) (x y : Fields) :
    BinChaos (exactSub mode) mode x y (Isa.x87.sub (encoding .hardware) mode x y).1
      (Isa.x87.sub (encoding .hardware) mode x y).2 :=
  binChaos_hardware ((Isa.x87.sub_spec _ mode x y).mono
    (Isa.x87.nanSpec_le_anyNaN _ Isa.x87_nanSound))

theorem sub_binChaos_softfloat (mode : RoundingMode) (x y : Fields) :
    BinChaos (exactSub mode) mode x y (Isa.x87.sub (encoding .softfloat) mode x y).1
      (Isa.x87.sub (encoding .softfloat) mode x y).2 :=
  binChaos_softfloat ((Isa.x87.sub_spec _ mode x y).mono (nan_le_quietNaN _))

theorem mul_binChaos_hardware (mode : RoundingMode) (x y : Fields) :
    BinChaos (fun a b => exactMul a b) mode x y (Isa.x87.mul (encoding .hardware) mode x y).1
      (Isa.x87.mul (encoding .hardware) mode x y).2 :=
  binChaos_hardware (Isa.x87.mul_chaos _ Isa.x87_nanSound mode x y)

theorem mul_binChaos_softfloat (mode : RoundingMode) (x y : Fields) :
    BinChaos (fun a b => exactMul a b) mode x y (Isa.x87.mul (encoding .softfloat) mode x y).1
      (Isa.x87.mul (encoding .softfloat) mode x y).2 :=
  binChaos_softfloat ((Isa.x87.mul_spec _ mode x y).mono (nan_le_quietNaN _))

theorem div_binChaos_hardware (mode : RoundingMode) (x y : Fields) :
    BinChaos (fun a b => exactDiv a b) mode x y (Isa.x87.div (encoding .hardware) mode x y).1
      (Isa.x87.div (encoding .hardware) mode x y).2 :=
  binChaos_hardware (Isa.x87.div_chaos _ Isa.x87_nanSound mode x y)

theorem div_binChaos_softfloat (mode : RoundingMode) (x y : Fields) :
    BinChaos (fun a b => exactDiv a b) mode x y (Isa.x87.div (encoding .softfloat) mode x y).1
      (Isa.x87.div (encoding .softfloat) mode x y).2 :=
  binChaos_softfloat ((Isa.x87.div_spec _ mode x y).mono (nan_le_quietNaN _))

/-- `ReadingAny` is strictly coarser than the union of the two readings: an
unnormal may be read as any datum. -/
example : ReadingAny ⟨false, 0x3FFF, 0x4000000000000000⟩ (.inf false) ∧
    ¬ ReadingChaos ⟨false, 0x3FFF, 0x4000000000000000⟩ (.inf false) := by
  refine ⟨Or.inl (by decide), ?_⟩
  rintro ⟨r, hr⟩
  cases r <;> revert hr <;> decide

end X87

end Silmaril.Numeric.Ieee754.Std
