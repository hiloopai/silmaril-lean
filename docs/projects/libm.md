# libm specifications

A specification lattice for the C99/POSIX math library, built on the IEEE 754
model of `Silmaril.Numeric.Ieee754` and Mathlib's real numbers. It states what
it means for a binary (an ELF shared object, a Wasm module, a Lean function) to
export a valid `sin`, and what it means to export a valid libm, at chosen
levels of accuracy.

Status: the `double` (binary64) functions of batches 1 and 2 below are
specified. `float`, `long double`, `erf`/`erfc`, the Bessel functions, `fma`,
`nextafter`, `ilogb`/`logb`, `remquo` and `lrint`/`lround` are not yet.

## Modules

| Module | Contents |
| --- | --- |
| `Silmaril.Numeric.Libm.Lattice.Defs` | `Spec`, `Outcome`, `SpecialCase`, the nodes, `Accuracy`, `Entry`, `ValidLibm` |
| `Silmaril.Numeric.Libm.Lattice.Thms` | the edges of the lattice |
| `Silmaril.Numeric.Libm.Binary64.Defs` | binary64 classifiers, special-case builders, sample inputs |
| `Silmaril.Numeric.Libm.Exact.{Defs,Thms,Tests}` | batch 1: references, specifications, proofs, sample checks |
| `Silmaril.Numeric.Libm.Elementary.Defs` | batch 2: specifications from Mathlib's real functions |
| `Silmaril.Numeric.Libm.Glibc.{Defs,Thms}` | glibc 2.40's documented error bounds |
| `Silmaril.Numeric.Libm.Catalogue.{Defs,Thms}` | the catalogue, profiles and whole-libm problems |
| `Silmaril.Numeric.Libm.Musl.{Defs,Thms,Tests}` | a fixed implementation: musl's `sin` and `cos` |
| `Silmaril.Numeric.Libm.Wasm.{Defs,Thms}` | "this Wasm module exports a valid `f` at node N", and proofs for single-instruction exports |

## The model

A function is a `Spec α τ`: its name, its exact real result `exact : α → Option ℝ`
on the inputs where one exists, and its list of `SpecialCase`s. An
implementation is a function `α → Outcome τ`, where an `Outcome` carries the
returned encoding, the IEEE flags raised and the `errno` set. Value-only models
(Lean functions, Wasm without a floating-point environment) use
`Outcome.pure`, and only the value nodes apply to them.

Units in the last place are those of the exact result, `ulp r = 2 ^ quantum r`
(`FlagSpec.quantum`, never finer than the subnormal spacing). An infinity is
measured against `2 ^ (emax + 1)`, so that the 1/2-ulp bound coincides with
IEEE round-to-nearest overflow. Correct rounding is `FlagSpec.deliver` (IEEE
§4.3 with §7.4 overflow) of the exact result, read through `F64.rounded?`.

## Lattice nodes, for one function `f`

| Node | Definition | Meaning |
| --- | --- | --- |
| (a) | `SpecialValues`, `SpecialFlags`, `SpecialErrno`, `Special` | Annex F and POSIX special cases: values, flags, `errno` |
| (b) | `ErrorOn D k` | within `k` ulps of the exact result on the inputs `D` |
| (c) | `ErrorGlobal k` | within `k` ulps everywhere |
| (d) | `CorrectlyRounded` | the round-to-nearest result (≤ 1/2 ulp) |
| (d) | `CRWithin n` | within `n` ulps of the correctly rounded result (glibc's measure) |
| (d) | `Exact` | the exact result (functions whose results are representable) |
| (e) | `BitExact impl ref`, `BitExactWhere impl ref` | the encodings of a fixed pure Lean function, everywhere or where the reference is defined |

`Accuracy` names the accuracy nodes: `none`, `ulps k`, `glibc n`,
`correctlyRounded`, `exact`. "Exports a valid `f` at accuracy `a`" is
`Spec.Valid impl a` (special cases and the accuracy node); `Spec.ValidValues`
drops flags and `errno`.

## Proved edges (`Lattice.Thms`)

- (c) → (b): `Spec.ErrorGlobal.errorOn`; (b) is monotone (`Spec.ErrorOn.mono`).
- (d) → (c): `Spec.CorrectlyRounded.errorGlobal_half`, from
  `RoundsTo.ulpClose_half`: a round-to-nearest result is within half an ulp,
  overflow included (the proof bounds `roundAt` and locates the overflow
  threshold, in `Silmaril.Proofs.Numeric.Libm.Lattice`).
- Inside (d): `Exact → CorrectlyRounded → CRWithin n`, `CRWithin 0 →
  CorrectlyRounded`, `CRWithin` monotone.
- (e) → (a values), (b), (c), (d): `BitExact.specialValues`, `.errorOn`,
  `.errorGlobal`, `.correctlyRounded`, `.crWithin`, `.exact`, `.accurate`;
  `BitExactWhere.errorOn` for partial references.
- `Spec.accurate_mono`: every case of `Accuracy.Implies`.

## Batch 1: exact and correctly rounded functions (`Exact`)

| Function | Reference | Exact result | Nodes proved for the reference |
| --- | --- | --- | --- |
| `floor`, `ceil`, `trunc` | `F64.floor`, `F64.ceil`, `F64.trunc` | `roundInt` | `Exact` (`floor_exact`, …), hence (d), (c) |
| `round` | `roundIntegral .nearestTiesToAway` | `roundInt` | `Exact` |
| `rint`, `nearbyint` | `F64.nearest` (default rounding direction) | `roundInt` | `Exact` |
| `sqrt` | `F64.sqrt` | `Real.sqrt` | `CorrectlyRounded`, `ErrorGlobal (1/2)` |
| `fabs`, `copysign` | `F64.abs`, `F64.copySign` | `|a|`, sign of `y` | samples only |
| `fmod`, `remainder` | `F64.fmod`, `F64.remainder` | `a - n·b` | samples only |
| `fmin`, `fmax` | `F64.minimumNumber`, `F64.maximumNumber` | `min`, `max` | samples only |
| `ldexp`, `scalbn` | `F64.scaleB` | `a · 2ⁿ` | samples only |
| `frexp`, `modf` | `Ref.frexp`, `Ref.modf` | `FrexpOk`, `ModfOk` | samples only |

`Exact.Tests` evaluates every reference on signed zeros, halfway cases,
subnormals and overflow, and checks every applicable special case of each
specification on `B64.samples` (23 inputs) or `B64.samplePairs` (144 pairs).
The unproved nodes are stated as `Double.Task.*` (`fabs_exact`, `fmod_exact`,
`ldexp_correctlyRounded`, `frexp_ok`, …).

## Batch 2: elementary functions (`Elementary`)

`exp`, `exp2`, `exp10`, `expm1`, `log`, `log2`, `log10`, `log1p`, `pow`, `cbrt`,
`hypot`, `sin`, `cos`, `tan`, `asin`, `acos`, `atan`, `atan2`, `sinh`, `cosh`,
`tanh`, `asinh`, `acosh`, `atanh`, `tgamma`, `lgamma`. The exact result is the
Mathlib function (`Real.exp`, `Real.log`, `Real.logb`, `x ^ y` for `Real.rpow`,
`Complex.arg` for `atan2`, `Real.arsinh`, `Real.Gamma`, …) on the finite inputs
of the domain. The special cases follow Annex F.10, with domain errors (NaN,
invalid, `EDOM`), pole errors (exact infinity, divide-by-zero, `ERANGE`) and
overflow range errors (overflow, inexact, `ERANGE`). Constants such as
`atan(+∞) = π/2` are required correctly rounded. These specifications carry no
reference implementation; their nodes are stated, not proved.

## Sane bounds (`Glibc`)

`Glibc.double240` records glibc 2.40's `libm-test-ulps` entries for the
round-to-nearest `double` functions of batch 2: `most` is the larger of the
x86-64 and AArch64 entries, `all` the maximum over eleven ports (file hashes in
the module). They are observed maxima of glibc's test suite, measured in ulps of
the correctly rounded result (`CRWithin`), so they are assumptions, not
theorems. `mostPlatforms_implies_allPlatforms` orders them.

## Combined problems (`Catalogue`)

`catalogue` is the list of all specified `double` entries. A `Profile` assigns a
level to each function:

| Profile | Batch 1 | `sqrt`, `ldexp`, `scalbn` | Batch 2 |
| --- | --- | --- | --- |
| `correctlyRounded` | `exact` | `correctlyRounded` | `correctlyRounded` |
| `glibcMost` | `exact` | `correctlyRounded` | `glibc (most)` |
| `glibcAll` | `exact` | `correctlyRounded` | `glibc (all)` |
| `faithful` | `exact` | `correctlyRounded` | `ulps 1` |
| `specialOnly` | `none` | `none` | `none` |

`ValidLibmDouble p impl` ("exports a valid libm at profile `p`") is the
conjunction of `e.valid (level p e.name) (impl e)` over the catalogue
(`validLibmDouble_iff`, `validLibm_cons`), and `ValidLibmDouble.mono` weakens it
along `correctlyRounded → glibcMost → glibcAll → specialOnly` and
`correctlyRounded → faithful → specialOnly`. Problems that a particular binary
exports a valid libm belong downstream, where the binary and its ABI are fixed.

## A fixed implementation: musl (`Musl`)

`Musl.sin` and `Musl.cos` transcribe musl's `sin`/`cos` (fdlibm's algorithms:
the `__sin`/`__cos` kernels and `__rem_pio2`'s Cody–Waite reduction) on the
F64 model, operation by operation, for finite `|x| < 2^20 · π/2`. Payne–Hanek
reduction (`__rem_pio2_large`) and non-finite arguments are not transcribed
(the references return `none`). `Musl.Tests` compares them with the host's
`Float.sin`/`Float.cos` within one encoding step on 21 samples. The 1-ulp bound
is assumed (`Musl.Task.sin_faithful`), and `sin_errorOn_of_bitExactWhere`
derives the bound for any implementation bit-exact with musl on that range.
wasi-libc's `sin` is musl's; Rust's `libm` crate ports the same algorithms.

## WebAssembly modules (`Wasm`)

`Silmaril.Numeric.Libm.Wasm.Defs` states the nodes for a Wasm module. The module is instantiated
against no imports (`exportFunc?`, silmaril-lean's executable instantiation) and its export is
called with `$invoke` under the Core 3.0 small-step semantics at a profile `P`, with no host
functions; a `double` is an `f64` with the same bits, a C `int` an `i32`.

| Definition | Meaning |
| --- | --- |
| `FuncImplements P s a N` | every input returns one `double` on some run; every run that stops has returned one `double`; every resolution `impl` of the runs (a value some run returns, per input) satisfies `N (Outcome.pure impl)` |
| `Exports P m name N` | the export `name` of module `m` implements `N` |
| `ExportsSpecialValues`, `ExportsErrorOn`, `ExportsErrorGlobal`, `ExportsCorrectlyRounded`, `ExportsCRWithin`, `ExportsExact`, `ExportsBitExact`, `ExportsBitExactWhere` | the lattice nodes (a)–(e) for an export |
| `ExportsValid P m S a` | "`m` exports a valid `f`": `Spec.ValidValues` at accuracy `a` (Wasm has no flags or `errno`) |
| `ExportsValidLibm P m p` | "`m` exports a valid libm at profile `p`": one `ExportsValid` per entry of `wasmCatalogue` |
| `BuildExports b name N`, `BuildValidLibm b p` | the same for the bytes `b` of a binary (decoded by silmaril-lean's decoder), at every deterministic profile |

`wasmCatalogue` is `Double.catalogue` without `frexp` and `modf` (they return through a pointer
into linear memory); `ldexp` and `scalbn` take a C `int` and are specified on `F64 × BitVec 32`
(`Spec.comap`).

Proved (`Wasm.Thms`, proofs in `Silmaril.Proofs.Numeric.Libm.Wasm`), at every deterministic
profile (`Profile.deterministic o`, canonical NaNs):

- `Exports.mono`, `BuildExports.mono`: every lattice edge transfers to exports.
- `funcImplements_unop`: a function `local.get 0; f64.op` is `BitExact` with `floatUnOp64 op`
  (`F64.abs`, `F64.floor`, `F64.ceil`, `F64.trunc`, `F64.nearest`, `F64.sqrt`), hence, with
  `Exact.Thms`, `Exact` for `floor`/`ceil`/`trunc`/`rint`/`nearbyint` and `CorrectlyRounded`
  for `sqrt`.
- `funcImplements_call_binop`: a function forwarding to `local.get 0; local.get 1; f64.op`
  (Rust's `#[no_mangle]` wrapper shape) is `BitExact` with `floatBinOp64 op` (`copysign`).
- `buildExports_unop`, `buildExports_call_binop`: the same for a binary, from the executable
  recognisers `checkUnopBytes` and `checkCallBinopBytes` run in the kernel (`kernel_rfl`; a
  547-byte module checks in seconds; decoding a 45 KB module in the kernel hit the default
  heartbeat limit after about 200 s, and without a limit had not finished after 25 minutes).

The runs are built with the existential calculus (`WasmSpec.Computes`, `FuncSpec.of_body`,
`wp_call`) and every other run is ruled out by uniqueness of normal forms at the deterministic
profile (`Silmaril.Wasm.Binaryen.steps_det_nf`). Not covered: `Profile.spec`, where NaN results
are nondeterministic, and every function compiled to more than one instruction.
The problems for concrete binaries (Rust's `libm` crate compiled to Wasm) are in erebor-lean.

## Building

```
lake build Silmaril.Numeric.Libm.Catalogue.Thms Silmaril.Numeric.Libm.Exact.Tests \
  Silmaril.Numeric.Libm.Musl.Thms Silmaril.Numeric.Libm.Musl.Tests \
  Silmaril.Numeric.Libm.Wasm.Thms
```

## References

- ISO/IEC 9899:2018, §7.12 and Annex F (IEC 60559 floating-point arithmetic).
- POSIX.1-2024, `<math.h>` and the function pages (`math_errhandling`).
- IEEE Std 754-2019, §§4.3, 5.3–5.5, 7.4–7.6, 9.2, 9.6.
- J.-M. Muller, *Elementary Functions: Algorithms and Implementation*, 3rd ed.,
  Birkhäuser, 2016, §2.1 (ulp).
- glibc 2.40, `sysdeps/*/libm-test-ulps` and `math/libm-test-support.c`.
- musl commit `7813e9119eb5fe681b6750b8a033a0490bca0941`, `src/math`.
