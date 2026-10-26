# The `Std` IEEE 754-2019 core

`Silmaril.Numeric.Ieee754.Std` is one generic IEEE 754-2019 binary
floating-point core: a mathematical specification, an executable implementation
proved to compute exactly the specified result, a lattice of implementation
variants related by proved inclusions, and validation against Berkeley TestFloat
3e and against x86 hardware. The older models (`Numeric.Ieee754` `F32`/`F64` on
Lean core's `Float.Model`, and `Numeric.Float` profiles) are unchanged; the
bridges below relate them to `Std`. See [IEEE 754 proof status](IEEEConformance.md)
for the older modules.

## Modules

| Module | Contents |
| --- | --- |
| `Std.Round` | `Grid` (precision, optional least quantum exponent). Order-theoretic rounding specification `Grid.RoundMag` (greatest representable below, least above, choice by direction; ties to even by the parity of the significand) over any ordered field with a floor, its uniqueness, and the executable rational rounder `Grid.roundMagQ` with `roundMagQ_spec`. |
| `Std.Format` | `BinFormat` (`binary16/32/64/128`, `bfloat16`, `x87Extended`, x87 precision-control formats), `Datum`, overflow per direction (§7.4), `RoundSpec`/`Deliver` (result *and* flags, tininess before/after rounding as a parameter, §7.5), executable `roundQ`/`deliverQ`, `deliver_iff` (the executable result is the only specified one). |
| `Std.Ops` | Exact outcomes of add, sub, mul, div, fma, remainder, roundToIntegral, format conversion, integer→float, float→integer (with an `IntOverflowPolicy`), comparisons (quiet and signaling), with NaN, infinity, signed-zero and invalid/division-by-zero rules (§§5–7). |
| `Std.IntegerRound` | `roundIntMag` (roundToIntegral, remainder, float→integer) is grid rounding onto the integers, so it meets `Grid.RoundMag`. |
| `Std.Sqrt` | Real-valued specification of square root and the executable `sqrtQ` (integer square roots, decisions by squaring), `sqrtQ_spec`. |
| `Std.Encoding`, `Std.EncodingCorrect` | Interchange encodings for every `(w, t)`; x87 80-bit extended with the explicit integer bit and its classes (pseudo-denormal, unnormal, pseudo-infinity, pseudo-NaN), read the hardware way or the SoftFloat way. `decode_encode_fin`, `decode_roundSpec`, `OpSpec.decode_out`: delivered non-NaN data are encoded faithfully. |
| `Std.NaN` | NaN policies as a lattice (`NaNSpec`), per-ISA NaN functions, `OpSpec` (bit-level specification for a policy), `runOp` and `runOp_spec_iff`. |
| `Std.Isa` | ISA profiles and their operations; `*_spec` and `*_chaos` theorems; min/max variants; `FmaChaos`. |
| `Std.WasmBridge` | WebAssembly's NaN rule `NaNSpec.wasm` and its place in the lattice. |
| `Std.Chaos` | Chaotic variants for state the exact profiles fix: MXCSR flush bits (`Mxcsr.Spec`, `Mxcsr.Unknown`), the chaotic x87 reading `X87.ReadingAny` lifted to arithmetic (`X87.BinChaos`), and counterexamples to the operand-level reading of the `fma` NaN inclusions. |
| `Std.CoreBridge` | Proved agreement with the `Float.Model` rounding engine, `F32`/`F64` and Lean core's model. |
| `Std.TestFloat`, `Std.Vectors`, `Std.KernelExamples`, `Std.Bridge`, `Std.BridgeTests` | TestFloat line checker, `#guard` vector samples, `decide +kernel` samples, executable differential bridges to `Numeric.Float` profiles and Lean core, and their build-time samples. |

## Specification and implementation

An operation's exact outcome (`Exact`: a NaN with or without invalid, an exact
infinity with or without division by zero, or a signed exact magnitude) is
delivered by `Deliver f tin mode`: the magnitude is rounded as though the
exponent range were unbounded above (`RoundMag` on `f.grid`, which includes the
subnormal quantum, so gradual underflow is built in); a result above `maxFinite`
becomes `overflowResult` for the direction; `inexact`, `overflow` and
`underflow` (tiny *and* inexact, with tininess detected before rounding or after
rounding at precision `p` with unbounded exponent) are raised accordingly; an
exact zero takes the sign chosen by the operation (§6.3). `RoundSpec.unique`
shows the specification is functional, and `deliver_iff` that the executable
`deliverQ` computes the unique specified pair (result, flags).

At the bit level `OpSpec E P tin mode ins e out flags` says that `out`/`flags`
are the specified ones, with a NaN result constrained only by the NaN policy `P`.
An ISA's operation is `runOp` with that ISA's NaN function, and
`runOp_spec_iff` proves it is the *only* output satisfying `OpSpec` for the
singleton policy of that function.

All five rounding directions are supported everywhere, including
`roundTiesToAway`.

## Variants and how they relate

Every implementation choice IEEE 754 leaves open is a parameter, and each has a
chaotic (least specified) variant that contains the exact ones by a proved
inclusion. A statement can assume only the chaotic variant and then holds for
every ISA.

| Choice | Variants | Proved relation |
| --- | --- | --- |
| NaN result (§6.2.3) | `ofFun (x86SSE.nan E)` (first NaN operand quieted, else the negative default NaN), `ofFun (x87.nan E)` (x87 operand choice, pairwise from left to right with the intermediate NaN quieted, as SoftFloat's `8086` `fma`), `ofFun (riscv.nan E)` (canonical NaN), `wasm F` (WebAssembly), `propagating`, `quietNaN`, `anyNaN`, `anything` | `x86SSE ≤ propagating`, `x87 ≤ propagating`, `propagating ≤ quietNaN ≤ anyNaN ≤ anything`; `riscv ≤ quietNaN`, `¬ riscv ≤ propagating`; `x86SSE ≤ wasm`, `riscv ≤ wasm ≤ quietNaN`, `¬ quietNaN ≤ wasm`, `¬ x86SSE ≤ riscv`. `OpSpec.mono` transports every operation's specification up the lattice (`Isa.add_chaos_all`, `Isa.x86SSE_add_wasm`, ...). For `fma` the NaN function receives `Isa.fmaNaNOperands`, which for SoftFloat `8086-SSE` and x87 replaces an invalid `∞ × 0` product by the default NaN, so `propagating` there is relative to that list, not to `[x, y, z]` (`Isa.fma_softfloat8086SSE_not_propagating`, `Isa.fma_x87_not_propagating`); `anyNaN` and `FmaChaos` are operand-independent. |
| Tininess (§7.5) | `beforeRounding`, `afterRounding` | Both are `RoundSpec` parameters. x86 SSE/AVX, x87 and RISC-V detect tininess after rounding (SoftFloat's `8086`, `8086-SSE` and `RISCV` specializations set `softfloat_tininess_afterRounding`). |
| `fma(∞, 0, qNaN)` (§7.2(c)) | x86 hardware (returns the quiet addend, no invalid), SoftFloat `8086-SSE` and RISC-V (invalid, default NaN) | `FmaChaos` contains both (`Isa.fma_fmaChaos`). |
| Invalid float→integer results (§5.8) | `x86Indefinite`, `riscvSaturate`, `saturateNaNZero` (Arm, Wasm `trunc_sat`) | `ToIntChaos`: any in-range integer; every policy with in-range values is in it. |
| min/max | x86 `MINSS/MAXSS` (operand order), IEEE 754-2008 `minNum/maxNum`, 2019 `minimum/maximum`, 2019 `minimumNumber/maximumNumber` (RISC-V `FMIN/FMAX`) | `MinMaxChaos` (an operand or a quiet NaN) contains every rule for every quiet NaN function (`minMax_chaos`). |
| x87 non-IEEE encodings | `X87Reading.hardware` (387+: unnormals, pseudo-infinities and pseudo-NaNs are invalid operands), `.softfloat`, the union `ReadingChaos`, the chaotic `ReadingAny` (any datum for those three classes; 8087/287 readings are not modeled exactly) | They agree outside those classes (`decode_hardware_eq_softfloat`); `ReadingChaos ≤ ReadingAny` (`readingChaos_le_readingAny`), strictly. `X87.BinChaos` (operands read by `ReadingAny`, any NaN) contains `Isa.x87` add/sub/mul/div under both readings (`X87.add_binChaos_hardware`, `X87.add_binChaos_softfloat`, ...). |
| MXCSR flush bits | `Isa.x86SSE` (`DAZ = FTZ = 0`), `Mxcsr.Spec m` (exact for `DAZ = FTZ = 0`, otherwise `FlushChaos m`: operands with exponent field `0` may be read as signed zero under DAZ, results with exponent field at most `1` may be flushed to signed zero under FTZ, flags open), `Mxcsr.Unknown` | `Mxcsr.spec_noFlush`, `Mxcsr.flushChaos_self` (the non-flushing result is in every variant), `Mxcsr.spec_le_unknown` (every setting is in `Unknown`). `MXCSR.DE` is not among the IEEE flags in any variant. |

x87 precision control as a mode is not part of the profiles; precision control is
available as the formats `x87PrecisionSingle/Double`.

Scope of the profiles as hardware models: `Isa.x86SSE` is SSE/AVX with
`DAZ = FTZ = 0` (use `Mxcsr.Spec` or `Mxcsr.Unknown` when MXCSR is not known).
`Isa.x87` is the x87 FPU only on the x87 extended encoding and the
precision-control formats; on binary32/binary64 it is SoftFloat's `8086`
functions, which no x87 instruction sequence implements (`FLD m32; FADD; FSTP m32`
rounds twice). `rem` has no SSE/AVX or RISC-V instruction (libm level); on x87 it
is `FPREM1`.

## What is proved, validated, chaotic

| Operation | Proved | Vector-validated (TestFloat level 1) | x86 hardware cross-check |
| --- | --- | --- | --- |
| add, sub, mul, div | executable = unique `Deliver` result (`runOp_spec_iff`), all formats, directions, tininess | f16/f32/f64/f128 (x86 and RISC-V profiles), extF80 incl. precision control 24/53 (x87) | f32/f64 SSE, extF80 x87 |
| fma | as above; both `fma(∞,0,qNaN)` variants | f16/f32/f64/f128, every 32nd level-1 vector, plus every vector with a NaN operand | f32/f64 FMA3 (every 32nd vector, plus every vector with a NaN operand; `VFMADD132/213/231` agree) |
| sqrt | `sqrtQ_spec` (real-valued specification) | all formats | f32/f64, extF80 |
| remainder | exact outcome + `runOp_spec_iff` | all formats | extF80 (`FPREM1`) |
| roundToIntegral (both exactness variants) | delivery proved; the integer rounding `roundIntMag` is the order-theoretic rounding onto the integer grid (`roundIntMag_spec`, `roundIntMag_unique`) | all formats and directions | f32/f64 (`ROUNDSS/SD`), extF80 (`FRNDINT`) |
| conversions between formats | `convert_spec` | all pairs | f32↔f64 (`CVTSS2SD/CVTSD2SS`), f32↔f16 (F16C `VCVTPS2PH/VCVTPH2PS`) |
| integer → float | `ofInt_spec` | i32/ui32/i64/ui64 → all formats | i32/i64 → f32/f64 (`CVTSI2SS/SD`) |
| float → integer | integer rounding by `roundIntMag_spec`; range check and invalid results by policy (a definition), chaos `ToIntChaos` | all formats → i32/ui32/i64/ui64, both exactness variants | f32/f64 → i32/i64 (`CVTSS2SI`, `CVTTSS2SI`, `CVTSD2SI`, `CVTTSD2SI`) |
| compare (quiet/signaling) | definition | eq, le, lt, eq_signaling, le_quiet, lt_quiet | f32/f64 (`VCMPSS`/`VCMPSD` predicates), extF80 (`FCOMI`/`FUCOMI`) |
| min/max | four rule definitions; `MinMaxChaos` contains all | (TestFloat has none) | x86 rule on f32/f64 (`MINSS/MAXSS`) |

## Bridges (proved)

* `Std.CoreBridge.value_roundUnpacked`: for every `Float.Model.Format`, rounding
  direction and input with a rational value, the value of
  `Rounding.roundUnpacked` (the rounding stage of all `Float.Model` arithmetic)
  is the `Std` grid rounding of that value. `mantissaRounds_eq_pick` relates the
  older significand specification to `Std.pick`.
* `Std.CoreBridge.finiteValue_eq`: the `F32`/`F64` decoder (`toRat?`) is the
  value of the `Std` interchange decoder, for every bit pattern.
* `F32.addWith_deliver`, `subWith_deliver`, `mulWith_deliver`,
  `fmaWith_deliver` (and `F64`): for finite operands and a non-overflowing
  result (the `NoExponentOverflow` hypothesis of `ArithmeticCorrectness`), in
  every direction, the result's value is that of every datum `Std`'s `Deliver`
  allows. `F32.add_deliver` etc. are the round-to-nearest-even cases, which are
  Lean core's `Float32.Model`/`Float.Model` operations (`addWith_rne`).
  `F32.isa_add` etc. state it for the executable result of any `Isa` profile, and
  `x86SSE_add_eq_core` for x86 SSE and Lean core's addition. These are value
  statements: `toRat?` identifies the two zeros.
* `Std.WasmBridge`: WebAssembly's NaN rule (above).
* `Std.ProfileBridge` (`Numeric.Float` profiles): `toFields` reads a profile
  encoding as `Std` fields and commutes with the NaN test, quieting and the
  default NaN. `x86SSE_pickNaN` and `riscvFD_pickNaN`: `Profile.x86SSE` (any
  MXCSR setting) and `Profile.riscvFD` choose exactly the NaN `Isa.x86SSE` and
  `Isa.riscv` choose for the same operands (`pickNaN_firstNaN`,
  `pickNaN_defaultNaN` for any profile), hence one WebAssembly admits
  (`x86SSE_pickNaN_wasm`). `binary_value`: without flushing, a profile's
  arithmetic on non-NaN operands is the core model's rounded result; so
  `add32`/`sub32`/`mul32` (and `64`): for finite operands and a non-overflowing
  result, in every direction, a non-flushing profile's result has the value of
  the same operation of every `Isa` (`x86SSE_add32`, `riscvFD_add32`, ...).

Executable bridges, checked bit for bit and flag for flag on vector operands:
`Bridge.agreeProfile` (`Numeric.Float.Profile.x86SSE` with the x86 hardware FMA
rule against `Isa.x86SSE`, `Profile.riscvFD` against `Isa.riscv`) and
`Bridge.agreeCore` (Lean core's model against `Isa.x86SSE`, round to nearest
even, NaNs only as NaNs), at build time in `Std.BridgeTests` and over full vector
sets by `scripts/ieee754/BridgeCheck.lean`.

## Validation

Berkeley SoftFloat 3e and TestFloat 3e are built outside the repository from
pinned commits, from GitHub source archives verified by SHA-256:

| Source | Commit | Archive SHA-256 |
| --- | --- | --- |
| `ucb-bar/berkeley-softfloat-3` | `b64af41c3276f97f0e181920400ee056b9c88037` | `faae889814ea6a292f7ca03d9b36e6c7e95bab2a64777804883cc822b8d48757` |
| `ucb-bar/berkeley-testfloat-3` | `06b20075dd3c1a5d0dd007a93643282832221612` | `38ea6ca7727ba5f22f53cf35128bb74cc5fde9ffbb02d87b01a7499e9e25f122` |

Each is built three times, with `SPECIALIZE_TYPE=8086-SSE` (x86 SSE),
`RISCV` and `8086` (x87). Then:

```
scripts/ieee754/testfloat-check.sh sf8086SSE <tf-8086-SSE>/testfloat_gen OUT [JOBS] [MULADD_STRIDE]
scripts/ieee754/testfloat-check.sh riscv     <tf-RISCV>/testfloat_gen    OUT
scripts/ieee754/testfloat-check.sh x87       <tf-8086>/testfloat_gen     OUT
scripts/ieee754/x86-hw-check.sh <tf-8086-SSE>/testfloat_gen OUT
scripts/ieee754/fma-nan-check.sh x87 <tf-8086>/testfloat_gen OUT "f32 f64"
scripts/ieee754/fma-nan-check.sh x86hw <tf-8086-SSE>/testfloat_gen OUT "f32 f64"
lake env lean --run scripts/ieee754/BridgeCheck.lean OUT/manifest.txt
```

`testfloat-check.sh` generates level-1 vectors for every operation, rounding
direction (all five) and format of the profile, plus tininess-before-rounding
variants of mul and div, and checks result and flags with
`scripts/ieee754/TestFloatCheck.lean`. It keeps every 32nd level-1 `mulAdd` vector;
`fma-nan-check.sh` checks every level-1 `mulAdd` vector with a NaN operand (with
`x86hw`, recomputed on this host by all three FMA forms, which must agree). `x86-hw-check.sh` recomputes the same
operands with this host's instructions (`scripts/ieee754/x86-hw-vectors.c`: SSE,
AVX, FMA3, F16C and x87, flags from MXCSR or the x87 status word; four
directions, since x86 has no ties-to-away) and checks them against `Isa.x86SSE`
and `Isa.x87`. Results of the runs are reported in the pull requests that change
this code.
