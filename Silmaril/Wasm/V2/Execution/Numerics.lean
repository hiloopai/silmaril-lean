module

public import Silmaril.Wasm.V2.Instructions
public import Silmaril.Wasm.Numerics.VectorProfile
public import Silmaril.Wasm.Numerics.Conversion
public import Silmaril.Wasm.Execution.Memory

/-!
# WebAssembly 2.0 numerics: the bridge to `Silmaril.Wasm.Numerics`

Transcribed from the official SpecTec source
`specification/wasm-2.0/3-numerics.spectec` at WebAssembly/spec revision
`608711107b7f1edb13efd57b7d79b49477462d36` (see `specs/wasm/core-2.0.json`).
Line references of the form `3-numerics:NN` point into that file; `8-reduction:NN`
points into `specification/wasm-2.0/8-reduction.spectec`.

**No arithmetic is implemented here.** Every definition in this file is a thin
dispatcher that names a 2.0 operator family and delegates to the existing,
shared, already-verified numerics of `Silmaril/Wasm/Numerics/**`
(`Integer.lean`, `Float.lean`, `Conversion.lean`, `VectorLanes.lean`,
`Vector.lean`, `Relaxed.lean`, `Profile.lean`, `VectorProfile.lean`) and to the
byte layer `Silmaril/Wasm/Execution/Memory.lean`. The 2.0-specific operator
types of `Silmaril.Wasm.V2.Ops` reach the shared numerics through their
`toShared` injections.

## Shape of the interface

SpecTec gives the scalar and vector operator families two different signatures:

* `$unop_`, `$binop_`, `$cvtop__`, `$vunop_`, `$vbinop_`, `$vcvtop__` return a
  *sequence* `num_(nt)*` of results. A singleton is a deterministic result, a
  longer sequence is NaN non-determinism, and the empty sequence `eps` is a
  trap (`Step_pure/binop-trap`, `Step_pure/cvtop-trap`, `8-reduction:187-207`).
  These become `Prop`-valued *relations* `…Result` (membership in the result
  set), paired with a `…Traps` predicate for "the set is defined and empty".
  Where NaN non-determinism is possible the relation takes a
  `Silmaril.Wasm.Numerics.Profile`, which is the repo's packaging of the spec's
  implementation-defined choices.
* `$testop_`, `$relop_`, `$vrelop_`, `$vshiftop_`, `$vvunop_`, `$vvbinop_`,
  `$vvternop_` return a single value. These become plain functions.

A result relation being `False` for every result means *stuck*, not trapped:
that is how the combinations for which SpecTec gives no equation at all (see
"`$cvtop__` has no equation" below) are modelled.

## Mapping `3-numerics` to Lean

| SpecTec (`3-numerics`) | Lean |
| --- | --- |
| `$s33_to_u32` (`:7`) | *(unmapped: a binary-format helper, see `A-binary`; nothing in `8-reduction` uses it)* |
| `$bool` (`:9`) | `Silmaril.Wasm.Numerics.bool32` |
| `$truncz` (`:13`) | `Int.tdiv` / the truncating rounding inside `Silmaril.Numeric.Integer.fromFloat?` |
| `$signed_` (`:20`) | `BitVec.toInt` (and `Numerics.VecLane.toIntSx .signed`) |
| `$inv_signed_` (`:24`) | `BitVec.ofInt` |
| `$sat_u_` (`:31`) | `Numerics.VecLane.satU` |
| `$sat_s_` (`:36`) | `Numerics.VecLane.satS` |
| `$unop_` (`:44`) | `IntUnOpResult`, `FloatUnOpResult` |
| `$binop_` (`:46`) | `IntBinOpResult` / `IntBinOpTraps`, `FloatBinOpResult` |
| `$testop_` (`:48`) | `testOp` |
| `$relop_` (`:50`) | `intRelOp`, `floatRelOp` |
| `$cvtop__` (`:52`) | `CvtOpResult` / `CvtOpTraps` |
| `$wrap__` (`:55`) | `BitVec.setWidth` |
| `$extend__` (`:56`) | `Numerics.VecLane.extend` |
| `$trunc__` (`:57`) | `Numerics.truncFloat` |
| `$trunc_sat__` (`:58`) | `Numerics.truncSatFloat` |
| `$demote__` (`:59`) | `Numerics.convertRel .demote` (a set: NaN non-determinism) |
| `$promote__` (`:60`) | `Numerics.convertRel .promote` |
| `$convert__` (`:61`) | `Numerics.convertInt` |
| `$narrow__` (`:62`) | `Numerics.VecLane.narrow` |
| `$reinterpret__` (`:63`) | `Numerics.convert (.reinterpretInt _ / .reinterpretFloat _)` |
| `$ibits_`, `$fbits_`, `$inv_ibits_`, `$inv_fbits_` (`:76,77,83,84`) | *(unmapped as standalone: bit sequences are `BitVec` here; their only use in `8-reduction` is `vbitmask`, folded into `Numerics.vbitmask` — see `VecBitmask`)* |
| `$ibytes_`, `$inv_ibytes_` (`:78,85`) | `ibytes`, `invIbytes` |
| `$fbytes_`, `$inv_fbytes_` (`:79,86`) | `fbytes`, `invFbytes` |
| `$nbytes_`, `$inv_nbytes_` (`:80,87`) | `nbytes`, `invNbytes` |
| `$vbytes_`, `$inv_vbytes_` (`:81,88`) | `vbytes`, `invVbytes` |
| `$iadd_`, `$isub_`, `$imul_` (`:105-107`) | `BitVec` `+`, `-`, `*` (via `Numerics.intBinOp`, `Numerics.ivbinop`) |
| `$idiv_`, `$irem_` (`:108,109`) | `Numerics.intBinOp (.div sx) / (.rem sx)` |
| `$inot_`, `$iand_`, `$ior_`, `$ixor_` (`:110,112,114,115`) | `Numerics.vvunop`, `Numerics.vvbinop` / `Numerics.intBinOp` |
| `$iandnot_` (`:113`) | `Numerics.VecLane.iandnot` |
| `$irev_` (`:111`) | *(only used by `vbitmask`; folded into `Numerics.vbitmask`)* |
| `$ishl_`, `$ishr_` (`:116,117`) | `Numerics.VecLane.ishl`, `Numerics.VecLane.ishr` (scalar: `Numerics.intBinOp`) |
| `$irotl_`, `$irotr_` (`:118,119`) | `Numerics.intBinOp .rotl / .rotr` |
| `$iclz_`, `$ictz_`, `$ipopcnt_` (`:120-122`) | `Numerics.intUnOp`, `Numerics.VecLane.ipopcnt` |
| `$ieqz_`, `$inez_` (`:123,124`) | `Numerics.intTestOp`, `Numerics.vvtestop` |
| `$ieq_` … `$ige_` (`:125-130`) | `Numerics.intRelOp`, `Numerics.VecLane.irelop` |
| `$ibitselect_` (`:131`) | `Numerics.VecLane.ibitselect` |
| `$iabs_`, `$ineg_` (`:132,133`) | `Numerics.VecLane.iabs`, `Numerics.VecLane.ineg` |
| `$imin_`, `$imax_` (`:134,135`) | `Numerics.VecLane.imin`, `Numerics.VecLane.imax` |
| `$iadd_sat_`, `$isub_sat_` (`:136,137`) | `Numerics.VecLane.iaddSat`, `Numerics.VecLane.isubSat` |
| `$iavgr_` (`:138`) | `Numerics.VecLane.iavgrU` |
| `$iq15mulr_sat_` (`:139`) | `Numerics.VecLane.iq15mulrSatS` |
| `$fadd_` … `$fcopysign_` (`:215-223`) | `Numerics.floatBinOpRel` / `Numerics.floatBinOp` |
| `$fpmin_`, `$fpmax_` (`:221,222`) | `Numerics.fpmin`, `Numerics.fpmax` |
| `$fabs_` … `$fnearest_` (`:224-230`) | `Numerics.floatUnOpRel` / `Numerics.floatUnOp` |
| `$feq_` … `$fge_` (`:231-236`) | `Numerics.floatRelOp`, `Numerics.floatRelBool` |
| `$packnum_` (`:323`) | `BitVec.setWidth` (inside `VecSplat`, `VecReplaceLane`) |
| `$unpacknum_` (`:328`) | `Numerics.VecLane.extend` (inside `VecExtractLane`) |
| `$lanes_`, `$inv_lanes_` (`:336,339`) | `Numerics.lanes` / `Numerics.invLanes`, `Shape.lanesOf` / `Shape.invLanes` |
| `$zeroop`, `$halfop` (`:343,350`) | *(unmapped as standalone: the half/zero discipline is built into the shape-indexed cases of `Numerics.vcvtop`; see `VecCvtOpResult`)* |
| `$half` (`:357`) | `Numerics.VecLane.half` |
| `$vvunop_`, `$vvbinop_`, `$vvternop_` (`:362-366`) | `VVUnOp`, `VVBinOp`, `VVTernOp` |
| `$vunop_` (`:377`) | `VecIntUnOpResult`, `VecFloatUnOpResult` |
| `$vbinop_` (`:379`) | `VecIntBinOpResult`, `VecFloatBinOpResult` |
| `$vrelop_` (`:381`) | `VecIntRelOp`, `VecFloatRelOp` |
| `$vcvtop__` (`:383`) | `VecCvtOpResult` |
| `$vextunop__` (`:583`) | `VecExtUnOpResult` |
| `$vextbinop__` (`:585`) | `VecExtBinOpResult` |
| `$vshiftop_` (`:608`) | `VecShiftOp` |

### `3-numerics` definitions we could not map

* `$s33_to_u32` (`3-numerics:7`). It is the signed-to-unsigned reading of the
  `s33` type-index immediate of the binary format (`A-binary`); no typing or
  reduction rule mentions it. It belongs to `Silmaril/Wasm/V2/Binary/**`.
* `$ibits_`, `$fbits_`, `$inv_ibits_`, `$inv_fbits_` (`3-numerics:76,77,83,84`).
  These produce SpecTec `bit*` sequences. We represent words as `BitVec`, in
  which the bit sequence is the value itself, so there is nothing to define.
  The only place `8-reduction` uses them is `Step_pure/vbitmask`
  (`8-reduction:293`); see `VecBitmask` below for why `Numerics.vbitmask`
  implements it.
* `$zeroop`, `$halfop` (`3-numerics:343,350`). These classify a `vcvtop` into
  the three `Step_pure/vcvtop-{full,half,zero}` rules. The shared
  `Numerics.vcvtop` is indexed by the operator *and both shapes* and already
  performs the slice (`half`) and the zero padding (`zero`) in the single case
  that applies, so no separate classifier is needed. `VecCvtOpResult` therefore
  covers all three rules at once.

### Lean definitions here with no `3-numerics` source

Wasm 2.0 inlines several vector instructions directly into `8-reduction`
instead of giving them a `$…` function (Core 3.0 later factored them out as
`$vtestop_`, `$ivbitmaskop_`, `$vswizzlop_`, `$vshufflop_`, `$vsplatop_`,
`$vextractop_`, `$vreplaceop_`, `$vnarrowop__`). Their Lean names here come from
the reduction rules:

| Lean | `8-reduction` rule |
| --- | --- |
| `VVTestOp` | `Step_pure/vvtestop` (`8-reduction:243`), `$ine_(128, c, 0)` |
| `VecAllTrue` | `Step_pure/vtestop-true` / `-false` (`8-reduction:267,272`) |
| `VecBitmask` | `Step_pure/vbitmask` (`8-reduction:293`) |
| `VecSwizzle` | `Step_pure/vswizzle` (`8-reduction:299`) |
| `VecShuffle` | `Step_pure/vshuffle` (`8-reduction:307`) |
| `VecSplat` | `Step_pure/vsplat` (`8-reduction:314`) |
| `VecExtractLane` | `Step_pure/vextract_lane-num` / `-pack` (`8-reduction:319,324`) |
| `VecReplaceLane` | `Step_pure/vreplace_lane` (`8-reduction:329`) |
| `VecNarrow` | `Step_pure/vnarrow` (`8-reduction:344`) |

## Notes on two readings

**`$ibits_` is most-significant-bit first.** `Step_pure/vbitmask`
(`8-reduction:293`) reads `$ibits_(32, ci) = $ilt_(.., S, ci_1, 0)* (0)^(32-N)`
and returns `$irev_(32, ci)`. `3-numerics` declares `$ibits_` `builtin`, but the
commented-out definitions of `$iclz_`/`$ictz_` in the 3.0 source
(`3.1-numerics.scalar.spectec:153,156`, identical wording) fix the order:
`$iclz_(N, i) = k -- if $ibits_(N, i) = (0)^k 1 d*`, so the sequence starts at
the most significant bit. Hence lane `i`'s sign bit sits at bit `31 - i` before
`$irev_` and at bit `i` after it, which is exactly
`Numerics.vbitmask` (little-endian `bitsNat` over the lane signs). The reference
interpreter agrees (`interpreter/exec/eval_simd.ml`, `Bitmask`).

**`$cvtop__` has no equation for some well-typed instructions.**
`Instr_ok/cvtop-convert` (`6-typing:285`) is unconstrained, so e.g.
`CVTOP I32 I64 (EXTEND S)` (target `i32`, source `i64`) type-checks, while
`3-numerics:310` would need `$extend__(64, 32, S, ·)`, which the `$extend__`
builtin does not define. We follow the decision already recorded in
`Silmaril/Wasm/V2/Ops.lean` (`CvtOp.toShared` is `Option`-valued): such a
configuration is *stuck*, not trapped, so `CvtOpResult` is `False` and
`CvtOpTraps` is `False` for it. This is not a new deviation; it is the same one
`Ops.lean` documents.

## Relaxed SIMD

`Silmaril.Wasm.Numerics` covers Core 3.0, which has relaxed-SIMD operators;
Wasm 2.0 does not. The `toShared` injections of `Silmaril.Wasm.V2.Ops` therefore
never hit a relaxed constructor, which is proved here
(`VecIntBinOp.toShared_ne_relaxed`, `VecFloatBinOp.toShared_ne_relaxedMin`,
`VecFloatBinOp.toShared_ne_relaxedMax`, `VecExtBinOp.toShared_ne_relaxedDotS`,
`VecCvtOp.toShared_ne_relaxedTrunc`). The consequence — that `Profile.nd` and
`Profile.relaxed` are irrelevant to the 2.0 semantics — is recorded as
`VecIntBinOpResult_nd_irrelevant`, `VecFloatBinOpResult_nd_irrelevant`,
`VecExtBinOpResult_nd_irrelevant` and `VecCvtOpResult_nd_irrelevant`. Only
`Profile.nan` (the NaN policy) matters, and 2.0 has no relaxed ternary, swizzle
or lane-select instruction at all, so `Numerics.VecFloatTernOpRel`,
`Numerics.VecIntTernOpRel`, `Numerics.vecRelaxedSwizzle` and
`Numerics.VecExtTernOpRel` are simply unused by this layer.
-/

@[expose] public section

namespace Silmaril.Wasm.V2.Execution

open Silmaril.Wasm.Numerics (V128 Profile)
open Silmaril.Wasm.Execution.Memory (Bytes decodeLE encodeLE readBytes writeBytes)

/-! ## Scalar integer operators

`$unop_(Inn, …)` (`3-numerics:275-278`), `$binop_(Inn, …)` (`3-numerics:263-274`),
`$testop_(Inn, …)` (`3-numerics:279`), `$relop_(Inn, …)` (`3-numerics:280-285`). -/

/-- `$unop_(Inn, unop, c)` (`3-numerics:275-278`): `CLZ`, `CTZ`, `POPCNT` and
`EXTEND N'`. Every equation is single-valued, so the SpecTec result sequence is
always a singleton and this relation is the graph of `Numerics.intUnOp`. -/
def IntUnOpResult (t : IntType) (op : IntUnOp) (x z : BitVec t.width) : Prop :=
  z = Numerics.intUnOp t op x

/-- `$binop_(Inn, binop, c_1, c_2)` (`3-numerics:263-274`). The sequence is empty
exactly for `DIV`/`REM` by zero and for signed `DIV` overflow
(`3-numerics:145-155`), which `Numerics.intBinOp` reports as `.error`. -/
def IntBinOpResult (t : IntType) (op : IntBinOp) (x y z : BitVec t.width) : Prop :=
  Numerics.intBinOp t op x y = .ok z

/-- `$binop_(Inn, binop, c_1, c_2) = eps`, the premise of `Step_pure/binop-trap`
(`8-reduction:187-189`). -/
def IntBinOpTraps (t : IntType) (op : IntBinOp) (x y : BitVec t.width) : Prop :=
  ∃ e, Numerics.intBinOp t op x y = .error e

/-- `$testop_(Inn, EQZ, c)` (`3-numerics:279`), i.e. `$ieqz_`. Deterministic. -/
def testOp (t : IntType) (op : IntTestOp) (x : BitVec t.width) : BitVec 32 :=
  Numerics.intTestOp t op x

/-- `$relop_(Inn, relop, c_1, c_2)` (`3-numerics:280-285`). Deterministic. -/
def intRelOp (t : IntType) (op : IntRelOp) (x y : BitVec t.width) : BitVec 32 :=
  Numerics.intRelOp t op x y

/-! ## Scalar floating-point operators

`$unop_(Fnn, …)` (`3-numerics:295-301`), `$binop_(Fnn, …)` (`3-numerics:287-293`),
`$relop_(Fnn, …)` (`3-numerics:303-308`). The float functions return *sets*
(`fN*`, `3-numerics:215-230`) because of NaN payload non-determinism; the set is
never empty, so the float `unop`/`binop` trap rules never fire
(`FloatUnOpResult_nonempty`, `FloatBinOpResult_nonempty`). -/

/-- `$unop_(Fnn, unop, c)` (`3-numerics:295-301`). -/
def FloatUnOpResult (P : Profile) (t : FloatType) (op : FloatUnOp)
    (x z : BitVec t.width) : Prop :=
  Numerics.floatUnOpP P t op x z

/-- `$binop_(Fnn, binop, c_1, c_2)` (`3-numerics:287-293`). -/
def FloatBinOpResult (P : Profile) (t : FloatType) (op : FloatBinOp)
    (x y z : BitVec t.width) : Prop :=
  Numerics.floatBinOpP P t op x y z

/-- `$relop_(Fnn, relop, c_1, c_2)` (`3-numerics:303-308`). Deterministic. -/
def floatRelOp (t : FloatType) (op : FloatRelOp) (x y : BitVec t.width) : BitVec 32 :=
  Numerics.floatRelOp t op x y

/-! ## Scalar conversions

`$cvtop__(nt_1, nt_2, cvtop, c_1)` (`3-numerics:310-318`), where `nt_1` is the
*source* and `nt_2` the *target*; the instruction is `CVTOP nt_2 nt_1 cvtop`
(`8-reduction:201`), so `V2.Instr.cvtOp` and the definitions here take
`target` before `source`, as `CvtOp.toShared` does. -/

/-- `c <- $cvtop__(source, target, op, x)` (`3-numerics:310-318`), the premise of
`Step_pure/cvtop-val` (`8-reduction:201`).

The combinations listed are exactly those for which `3-numerics` gives an
equation whose builtin is defined; they coincide with the `some` cases of
`V2.CvtOp.toShared` (`cvtOpResult_iff_toShared`). Matching on the two number
types rather than quantifying over the shared `ConvertOp` keeps the operand and
result widths definitionally correct, with no casts. -/
def CvtOpResult (P : Profile) :
    (target source : NumType) → CvtOp → BitVec source.width → BitVec target.width → Prop
  | .int .i64, .int .i32, .extend sg, x, z => Numerics.convertP P (.extend sg) x (.ok z)
  | .int .i32, .int .i64, .wrap, x, z => Numerics.convertP P .wrap x (.ok z)
  | .float t, .int s, .convert sg, x, z => Numerics.convertP P (.convert s t sg) x (.ok z)
  | .int t, .float s, .trunc sg, x, z => Numerics.convertP P (.trunc s t sg) x (.ok z)
  | .int t, .float s, .truncSat sg, x, z => Numerics.convertP P (.truncSat s t sg) x (.ok z)
  | .float .f64, .float .f32, .promote, x, z => Numerics.convertP P .promote x (.ok z)
  | .float .f32, .float .f64, .demote, x, z => Numerics.convertP P .demote x (.ok z)
  | .int .i32, .float .f32, .reinterpret, x, z =>
      Numerics.convertP P (.reinterpretInt .f32) x (.ok z)
  | .int .i64, .float .f64, .reinterpret, x, z =>
      Numerics.convertP P (.reinterpretInt .f64) x (.ok z)
  | .float .f32, .int .i32, .reinterpret, x, z =>
      Numerics.convertP P (.reinterpretFloat .i32) x (.ok z)
  | .float .f64, .int .i64, .reinterpret, x, z =>
      Numerics.convertP P (.reinterpretFloat .i64) x (.ok z)
  | _, _, _, _, _ => False

/-- `$cvtop__(source, target, op, x) = eps`, the premise of
`Step_pure/cvtop-trap` (`8-reduction:205-207`). Only `TRUNC sx` can produce an empty
sequence (`3-numerics:312`, `$trunc__ : iN(N')?`): `TRUNC_SAT` saturates,
`DEMOTE`/`PROMOTE` return non-empty NaN sets, and the remaining conversions are
total. A combination with no `3-numerics` equation is *not* a trap — it is
`False` here as well, leaving the machine stuck; see the module docstring. -/
def CvtOpTraps (P : Profile) :
    (target source : NumType) → CvtOp → BitVec source.width → Prop
  | .int t, .float s, .trunc sg, x => ∃ e, Numerics.convertP P (.trunc s t sg) x (.error e)
  | _, _, _, _ => False

/-! ## Bitwise vector operators

`$vvunop_`, `$vvbinop_`, `$vvternop_` (`3-numerics:362-374`) and
`Step_pure/vvtestop` (`8-reduction:243`). All four are deterministic. -/

/-- `$vvunop_(V128, NOT, v)` (`3-numerics:369`) = `$inot_(128, v)`. -/
def VVUnOp (op : VecUnOp) (v : V128) : V128 := Numerics.vvunop op v

/-- `$vvbinop_(V128, {AND, ANDNOT, OR, XOR}, v_1, v_2)` (`3-numerics:370-373`). -/
def VVBinOp (op : VecBinOp) (v w : V128) : V128 := Numerics.vvbinop op v w

/-- `$vvternop_(V128, BITSELECT, v_1, v_2, v_3)` (`3-numerics:374`). -/
def VVTernOp (op : VecTernOp) (v w m : V128) : V128 := Numerics.vvternop op v w m

/-- `Step_pure/vvtestop` (`8-reduction:243`): `ANY_TRUE` is `$ine_(128, v, 0)`.
2.0 has no `$vvtestop_` function; the rule inlines `$ine_`. -/
def VVTestOp (op : VecTestOp) (v : V128) : BitVec 32 := Numerics.vvtestop op v

/-! ## Lane-wise vector operators -/

/-- `$vunop_(Jnn X M, {ABS, NEG, POPCNT}, v)` (`3-numerics:386-394`). Each
equation is single-valued. -/
def VecIntUnOpResult (sh : IntShape) (op : VecIntUnOp) (v r : V128) : Prop :=
  r = Numerics.vecIntUnOp sh op v

/-- `$vunop_(Fnn X M, vunop, v)` (`3-numerics:464-491`): the `$setproduct_` of
the lane-wise float result sets, mapped through `$inv_lanes_`. -/
def VecFloatUnOpResult (P : Profile) (sh : FloatShape) (op : FloatUnOp)
    (v r : V128) : Prop :=
  Numerics.VecFloatUnOpRel P sh op v r

/-- `$vbinop_(Jnn X M, vbinop, v_1, v_2)` (`3-numerics:396-431`). Single-valued;
the `Profile` is carried only because the shared dispatcher also covers
`relaxed_q15mulr_s`, which `V2.VecIntBinOp.toShared` never produces
(`VecIntBinOpResult_nd_irrelevant`). -/
def VecIntBinOpResult (P : Profile) (sh : IntShape) (op : VecIntBinOp)
    (a b r : V128) : Prop :=
  r = Numerics.vecIntBinOp P sh op.toShared a b

/-- `$vbinop_(Fnn X M, vbinop, v_1, v_2)` (`3-numerics:493-532`). -/
def VecFloatBinOpResult (P : Profile) (sh : FloatShape) (op : VecFloatBinOp)
    (a b r : V128) : Prop :=
  Numerics.VecFloatBinOpRel P sh op.toShared a b r

/-- `Step_pure/vtestop-true` / `-false` (`8-reduction:268,273`): `ALL_TRUE` is
`1` iff every lane is non-zero. 2.0 has no `$vtestop_` function. -/
def VecAllTrue (sh : IntShape) (v : V128) : BitVec 32 := Numerics.vecAllTrue sh v

/-- `$vrelop_(Jnn X M, vrelop, v_1, v_2)` (`3-numerics:433-462`): the lane-wise
comparison sign-extended from one bit to the lane width. -/
def VecIntRelOp (sh : IntShape) (op : IntRelOp) (a b : V128) : V128 :=
  Numerics.vecIntRelOp sh op a b

/-- `$vrelop_(Fnn X M, vrelop, v_1, v_2)` (`3-numerics:534-569`). The result
lanes are integer lanes of the same width (`$isize(Inn) = $size(Fnn)`). -/
def VecFloatRelOp (sh : FloatShape) (op : FloatRelOp) (a b : V128) : V128 :=
  Numerics.vecFloatRelOp sh op a b

/-- `$vshiftop_(Jnn X M, vshiftop, lane, n)` (`3-numerics:608-612`), fused with
the lane mapping that `Step_pure/vshiftop` (`8-reduction:287`) performs: SpecTec's
function acts on one lane, this one on the whole vector. The shift count is
reduced modulo the lane width by `$ishl_`/`$ishr_`. -/
def VecShiftOp (sh : IntShape) (op : Wasm.VecShiftOp) (v : V128) (n : BitVec 32) : V128 :=
  Numerics.vecShiftOp sh op v n

/-- `Step_pure/vbitmask` (`8-reduction:293`): bit `i` of the result is the sign
bit of lane `i`. See the module docstring for why `$irev_` of the MSB-first
`$ibits_` is the little-endian packing `Numerics.vbitmask` performs. -/
def VecBitmask (sh : IntShape) (v : V128) : BitVec 32 := Numerics.vecBitmask sh v

/-- `Step_pure/vswizzle` (`8-reduction:299`): `table` is `c_1`, `indices` is
`c_2`. SpecTec pads the table with `0^(256-M)` so that an out-of-range index
selects `0`; `Numerics.iswizzleLane` uses `List.getD … 0`, which agrees. -/
def VecSwizzle (table indices : V128) : V128 := Numerics.vecSwizzle table indices

/-- `Step_pure/vshuffle` (`8-reduction:307`): index into `lanes(a) ++ lanes(b)`.
The bound on each index is the typing premise `-- (if $(i < 2*$dim(sh)))*`
(`Instr_ok/vshuffle`, `6-typing:340-342`); since this constructor fixes
`sh = I8 X 16` and `$dim(Lnn X N) = N` (`2-syntax-aux:39`), it reads `i < 32`.
The function is therefore total here and returns `0` out of range. -/
def VecShuffle (idx : List LaneIdx) (a b : V128) : V128 := Numerics.vecShuffle idx a b

/-- `Step_pure/vsplat` (`8-reduction:314`): `$inv_lanes_(Lnn X N, $packnum_(Lnn, c)^N)`. -/
def VecSplat (sh : Shape) (x : BitVec sh.unpacked.width) : V128 := Numerics.vecSplat sh x

/-- `Step_pure/vextract_lane-num` / `-pack` (`8-reduction:320,325`). For a packed
lane type the lane is `$extend__($psize(pt), 32, sx, ·)`; `sx` is `none` exactly
for unpacked lanes, which `Instr.immediatesValid` enforces. -/
def VecExtractLane (sh : Shape) (sx : Option Signedness) (i : Nat) (v : V128) :
    BitVec sh.unpacked.width :=
  Numerics.vecExtractLane sh sx i v

/-- `Step_pure/vreplace_lane` (`8-reduction:329`). -/
def VecReplaceLane (sh : Shape) (i : Nat) (v : V128) (x : BitVec sh.unpacked.width) : V128 :=
  Numerics.vecReplaceLane sh i v x

/-- `$vextunop__(ishape_1, ishape_2, vextunop, v)` (`3-numerics:583,588`), with
`ishape_1` the *result* shape and `ishape_2` the operand shape; the instruction
is `VEXTUNOP sh_1 sh_2 vextunop` (`8-reduction:334`), so `target` comes first
here, matching `V2.Instr.vecExtUnOp`. Single-valued. -/
def VecExtUnOpResult (target source : IntShape) (op : VecExtUnOp) (a r : V128) : Prop :=
  Numerics.VecExtUnOpRel source target op a r

/-- `$vextbinop__(ishape_1, ishape_2, vextbinop, v_1, v_2)`
(`3-numerics:585,595,600`): `EXTMUL half sx` and `DOT S`. `target` is SpecTec's
`ishape_1`. Single-valued; the `Profile` is carried only because the shared
dispatcher also covers `relaxed_dot`. -/
def VecExtBinOpResult (P : Profile) (target source : IntShape) (op : VecExtBinOp)
    (a b r : V128) : Prop :=
  Numerics.VecExtBinOpRel P source target op.toShared a b r

/-- `Step_pure/vnarrow` (`8-reduction:344`): the instruction is
`VNARROW (Jnn_2 X N_2) (Jnn_1 X N_1) sx`, result shape first. Both halves are
`$narrow__`, which saturates the *signed* interpretation of the source lane into
the `sx` range. 2.0 has no `$vnarrowop__` function. -/
def VecNarrow (target source : IntShape) (sx : Signedness) (a b : V128) : V128 :=
  Numerics.vnarrow source target sx a b

/-- `$vcvtop__(shape_1, shape_2, vcvtop, lane)` (`3-numerics:383,571-580`)
together with the three rules `Step_pure/vcvtop-{full,half,zero}`
(`8-reduction:353,360,367`): the lane slicing of `$halfop` and the zero padding
of `$zeroop` are already part of `Numerics.vcvtop`'s shape-indexed cases.
`target` is SpecTec's `shape_2`, matching `V2.Instr.vecCvtOp`. -/
def VecCvtOpResult (P : Profile) (target source : Shape) (op : VecCvtOp)
    (a r : V128) : Prop :=
  Numerics.VecConvertRel P source target op.toShared a r

/-! ## Byte serialization

`$ibytes_`, `$fbytes_`, `$nbytes_`, `$vbytes_` and their inverses
(`3-numerics:76-102`), all declared `builtin`. They are little-endian, `N/8`
bytes wide, and are the only interface between numbers and linear memory
(`8-reduction:489-593`). The repo has no function of these names; the byte layer
is `Silmaril.Wasm.Execution.Memory`, whose `encodeLE`/`decodeLE` are exactly the
little-endian coder, and whose `load`/`store` are `readBytes`/`writeBytes`
composed with it (`load_eq_invIbytes`, `store_eq_ibytes`). -/

/-- `$ibytes_(N, i)` (`3-numerics:78`): the little-endian `N/8`-byte encoding. -/
def ibytes (N : Nat) (x : BitVec N) : Bytes := encodeLE (N / 8) x.toNat

/-- `$inv_ibytes_(N, b*)` (`3-numerics:85`). -/
def invIbytes (N : Nat) (bs : Bytes) : BitVec N := BitVec.ofNat N (decodeLE bs)

/-- `$fbytes_(N, z)` (`3-numerics:79`). Floats are stored as their raw bit
pattern, so this is `$ibytes_` at the same width. -/
def fbytes (t : FloatType) (x : BitVec t.width) : Bytes := ibytes t.width x

/-- `$inv_fbytes_(N, b*)` (`3-numerics:86`). -/
def invFbytes (t : FloatType) (bs : Bytes) : BitVec t.width := invIbytes t.width bs

/-- `$nbytes_(numtype, c)` (`3-numerics:80`). -/
def nbytes (t : NumType) (x : BitVec t.width) : Bytes := ibytes t.width x

/-- `$inv_nbytes_(numtype, b*)` (`3-numerics:87`). -/
def invNbytes (t : NumType) (bs : Bytes) : BitVec t.width := invIbytes t.width bs

/-- `$vbytes_(V128, c)` (`3-numerics:81`). `vectype` has the single alternative
`V128` (`1-syntax:129-130`), so the type argument carries no information and is
dropped. -/
def vbytes (x : V128) : Bytes := ibytes 128 x

/-- `$inv_vbytes_(V128, b*)` (`3-numerics:88`). -/
def invVbytes (bs : Bytes) : V128 := invIbytes 128 bs

/-! ### Properties of the byte functions -/

@[simp] theorem ibytes_size (N : Nat) (x : BitVec N) : (ibytes N x).size = N / 8 :=
  Silmaril.Wasm.Execution.Memory.encodeLE_size _ _

@[simp] theorem nbytes_size (t : NumType) (x : BitVec t.width) :
    (nbytes t x).size = t.width / 8 := ibytes_size _ _

@[simp] theorem fbytes_size (t : FloatType) (x : BitVec t.width) :
    (fbytes t x).size = t.width / 8 := ibytes_size _ _

@[simp] theorem vbytes_size (x : V128) : (vbytes x).size = 16 := ibytes_size _ _

/-- `$inv_ibytes_` is a left inverse of `$ibytes_` at every byte-aligned width. -/
theorem invIbytes_ibytes {N : Nat} (h : 8 ∣ N) (x : BitVec N) : invIbytes N (ibytes N x) = x := by
  obtain ⟨k, rfl⟩ := h
  have hk : 8 * k / 8 = k := Nat.mul_div_cancel_left k (by decide)
  have hp : (256 : Nat) ^ k = 2 ^ (8 * k) := by rw [Nat.pow_mul]
  apply BitVec.eq_of_toNat_eq
  rw [invIbytes, ibytes, hk, Silmaril.Wasm.Execution.Memory.decodeLE_encodeLE, hp,
    Nat.mod_eq_of_lt x.isLt]
  simp

@[simp] theorem invNbytes_nbytes (t : NumType) (x : BitVec t.width) :
    invNbytes t (nbytes t x) = x :=
  invIbytes_ibytes (by cases t <;> rename_i t <;> cases t <;> decide) x

@[simp] theorem invFbytes_fbytes (t : FloatType) (x : BitVec t.width) :
    invFbytes t (fbytes t x) = x :=
  invIbytes_ibytes (by cases t <;> decide) x

@[simp] theorem invVbytes_vbytes (x : V128) : invVbytes (vbytes x) = x :=
  invIbytes_ibytes (by decide) x

/-- `decodeLE` peels off the least significant byte (it is little-endian). -/
theorem decodeLE_cons (b : UInt8) (l : List UInt8) :
    decodeLE ⟨⟨b :: l⟩⟩ = b.toNat + 256 * decodeLE ⟨⟨l⟩⟩ := by
  simp [decodeLE]

/-- A byte string of length `n` decodes below `256 ^ n`. -/
theorem decodeLE_lt (bs : Bytes) : decodeLE bs < 256 ^ bs.size := by
  obtain ⟨⟨l⟩⟩ := bs
  induction l with
  | nil => decide
  | cons b l ih =>
    have hb : b.toNat < 256 := b.toNat_lt
    have ihl : decodeLE (⟨⟨l⟩⟩ : Bytes) < 256 ^ l.length := ih
    have hs : (⟨⟨b :: l⟩⟩ : Bytes).size = l.length + 1 := rfl
    rw [hs, decodeLE_cons, Nat.pow_succ]
    omega

/-- `encodeLE` is a left inverse of `decodeLE` on byte arrays of their own
length; the missing half of `Silmaril.Wasm.Execution.Memory.decodeLE_encodeLE`. -/
theorem encodeLE_decodeLE (bs : Bytes) : encodeLE bs.size (decodeLE bs) = bs := by
  obtain ⟨⟨l⟩⟩ := bs
  induction l with
  | nil => rfl
  | cons b l ih =>
    have hb : b.toNat < 256 := b.toNat_lt
    have h1 : UInt8.ofNat (b.toNat + 256 * decodeLE (⟨⟨l⟩⟩ : Bytes)) = b :=
      UInt8.toNat_inj.mp (by
        rw [UInt8.toNat_ofNat']
        change (b.toNat + 256 * decodeLE (⟨⟨l⟩⟩ : Bytes)) % 256 = b.toNat
        rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb])
    have h2 : (b.toNat + 256 * decodeLE (⟨⟨l⟩⟩ : Bytes)) / 256
        = decodeLE (⟨⟨l⟩⟩ : Bytes) := by
      rw [Nat.add_mul_div_left _ _ (by decide : 0 < 256), Nat.div_eq_of_lt hb, Nat.zero_add]
    have ihl : encodeLE l.length (decodeLE (⟨⟨l⟩⟩ : Bytes)) = (⟨⟨l⟩⟩ : Bytes) := ih
    have hs : (⟨⟨b :: l⟩⟩ : Bytes).size = l.length + 1 := rfl
    rw [hs, decodeLE_cons, encodeLE, h1, h2, ihl]
    apply ByteArray.ext
    simp [ByteArray.data_append]

/-- `$ibytes_` is onto the byte strings of length `N/8`: together with
`invIbytes_ibytes` this says `$ibytes_(N, ·)` is a bijection
`iN(N) ≃ {b* | |b*| = N/8}`, which is what `hint(inverse $inv_ibytes_)`
(`3-numerics:78`) asserts. -/
theorem ibytes_invIbytes {N : Nat} (h : 8 ∣ N) {bs : Bytes} (hb : bs.size = N / 8) :
    ibytes N (invIbytes N bs) = bs := by
  obtain ⟨k, rfl⟩ := h
  have hk : 8 * k / 8 = k := Nat.mul_div_cancel_left k (by decide)
  rw [hk] at hb
  have hp : (256 : Nat) ^ k = 2 ^ (8 * k) := by rw [Nat.pow_mul]
  have hlt : decodeLE bs < 2 ^ (8 * k) := by
    have hd := decodeLE_lt bs
    rwa [hb, hp] at hd
  rw [ibytes, invIbytes, hk, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt, ← hb]
  exact encodeLE_decodeLE bs

theorem ibytes_injective {N : Nat} (h : 8 ∣ N) : Function.Injective (ibytes N) := by
  intro x y hxy
  rw [← invIbytes_ibytes h x, ← invIbytes_ibytes h y, hxy]

/-- The bijection statement in full. -/
theorem ibytes_bijective {N : Nat} (h : 8 ∣ N) {bs : Bytes} (hb : bs.size = N / 8) :
    ∃! x : BitVec N, ibytes N x = bs :=
  ⟨invIbytes N bs, ibytes_invIbytes h hb, fun _ hy => ibytes_injective h (hy.trans
    (ibytes_invIbytes h hb).symm)⟩

theorem nbytes_injective (t : NumType) : Function.Injective (nbytes t) :=
  ibytes_injective (by cases t <;> rename_i t <;> cases t <;> decide)

theorem fbytes_injective (t : FloatType) : Function.Injective (fbytes t) :=
  ibytes_injective (by cases t <;> decide)

theorem vbytes_injective : Function.Injective vbytes := ibytes_injective (by decide)

/-! ### Agreement with the memory layer

`8-reduction` phrases every load as `$nbytes_(nt, c) = …BYTES[i : N/8]` and every
store as `$with_mem(z, 0, i, N/8, $nbytes_(nt, c))`. These two lemmas say that is
exactly `Silmaril.Wasm.Execution.Memory.load` / `.store`. -/

theorem load_eq_invIbytes (mem : Bytes) (i count : Nat) :
    Silmaril.Wasm.Execution.Memory.load mem i count
      = (readBytes mem i count).map (invIbytes (8 * count)) := rfl

theorem store_eq_ibytes (mem : Bytes) (i count : Nat) (x : BitVec (8 * count)) :
    Silmaril.Wasm.Execution.Memory.store mem i x = writeBytes mem i (ibytes (8 * count) x) := by
  rw [ibytes, Nat.mul_div_cancel_left count (by decide : 0 < 8)]
  rfl

/-! ## Agreement theorems

Every dispatcher above is *defined* by delegation, so the "agreement" statements
below are mostly definitional unfoldings; they are stated anyway because they are
the contract the reduction rules are written against, and because the proofs of
the interesting ones (profile irrelevance, non-emptiness, absence of relaxed
operators) are not definitional. -/

/-! ### Scalar -/

theorem intUnOpResult_iff (t : IntType) (op : IntUnOp) (x z : BitVec t.width) :
    IntUnOpResult t op x z ↔ z = Numerics.intUnOp t op x := Iff.rfl

theorem intBinOpResult_iff (t : IntType) (op : IntBinOp) (x y z : BitVec t.width) :
    IntBinOpResult t op x y z ↔ Numerics.intBinOp t op x y = .ok z := Iff.rfl

theorem testOp_eq (t : IntType) (op : IntTestOp) (x : BitVec t.width) :
    testOp t op x = Numerics.intTestOp t op x := rfl

theorem intRelOp_eq (t : IntType) (op : IntRelOp) (x y : BitVec t.width) :
    intRelOp t op x y = Numerics.intRelOp t op x y := rfl

theorem floatUnOpResult_iff (P : Profile) (t : FloatType) (op : FloatUnOp)
    (x z : BitVec t.width) : FloatUnOpResult P t op x z ↔ Numerics.floatUnOpP P t op x z :=
  Iff.rfl

theorem floatBinOpResult_iff (P : Profile) (t : FloatType) (op : FloatBinOp)
    (x y z : BitVec t.width) :
    FloatBinOpResult P t op x y z ↔ Numerics.floatBinOpP P t op x y z := Iff.rfl

theorem floatRelOp_eq (t : FloatType) (op : FloatRelOp) (x y : BitVec t.width) :
    floatRelOp t op x y = Numerics.floatRelOp t op x y := rfl

/-- `$unop_(Inn, …)` is a singleton: the integer `unop` rule always applies. -/
theorem IntUnOpResult_nonempty (t : IntType) (op : IntUnOp) (x : BitVec t.width) :
    ∃ z, IntUnOpResult t op x z := ⟨_, rfl⟩

theorem IntUnOpResult_unique {t : IntType} {op : IntUnOp} {x z z' : BitVec t.width}
    (h : IntUnOpResult t op x z) (h' : IntUnOpResult t op x z') : z = z' := h.trans h'.symm

/-- `$binop_(Inn, …)` is either a singleton or empty, never both: exactly one of
`Step_pure/binop-val` and `Step_pure/binop-trap` applies. -/
theorem IntBinOpResult_or_traps (t : IntType) (op : IntBinOp) (x y : BitVec t.width) :
    (∃ z, IntBinOpResult t op x y z) ∨ IntBinOpTraps t op x y := by
  rcases h : Numerics.intBinOp t op x y with e | z
  · exact Or.inr ⟨e, h⟩
  · exact Or.inl ⟨z, h⟩

theorem IntBinOpTraps_iff (t : IntType) (op : IntBinOp) (x y : BitVec t.width) :
    IntBinOpTraps t op x y ↔ ∀ z, ¬ IntBinOpResult t op x y z := by
  constructor
  · rintro ⟨e, he⟩ z hz
    rw [IntBinOpResult, he] at hz
    simp at hz
  · intro h
    rcases hb : Numerics.intBinOp t op x y with e | z
    · exact ⟨e, hb⟩
    · exact absurd hb (h z)

theorem IntBinOpResult_unique {t : IntType} {op : IntBinOp} {x y z z' : BitVec t.width}
    (h : IntBinOpResult t op x y z) (h' : IntBinOpResult t op x y z') : z = z' :=
  Except.ok.inj (h.symm.trans h')

/-- The float result sets are never empty, so the float `unop-trap` rule never
fires (`Numerics.floatUnOpP_nonempty`). -/
theorem FloatUnOpResult_nonempty (P : Profile) (t : FloatType) (op : FloatUnOp)
    (x : BitVec t.width) : ∃ z, FloatUnOpResult P t op x z :=
  Numerics.floatUnOpP_nonempty P t op x

theorem FloatBinOpResult_nonempty (P : Profile) (t : FloatType) (op : FloatBinOp)
    (x y : BitVec t.width) : ∃ z, FloatBinOpResult P t op x y z :=
  Numerics.floatBinOpP_nonempty P t op x y

/-! ### Scalar conversions -/

/-- `V2.CvtOp.toShared` preserves the source type. -/
theorem cvtOp_toShared_source {target source : NumType} {op : CvtOp} {co : ConvertOp}
    (h : op.toShared target source = some co) : co.source = source := by
  cases op <;> rcases target with t | t <;> rcases source with s | s <;>
    cases t <;> cases s <;>
    simp_all [CvtOp.toShared, IntType.width, FloatType.width] <;>
    (try subst_vars) <;> rfl

/-- `V2.CvtOp.toShared` preserves the target type. -/
theorem cvtOp_toShared_target {target source : NumType} {op : CvtOp} {co : ConvertOp}
    (h : op.toShared target source = some co) : co.target = target := by
  cases op <;> rcases target with t | t <;> rcases source with s | s <;>
    cases t <;> cases s <;>
    simp_all [CvtOp.toShared, IntType.width, FloatType.width] <;>
    (try subst_vars) <;> rfl

/-- `$cvtop__` agrees with the shared `Numerics.convertP` on the whole image of
`V2.CvtOp.toShared`. Together with `cvtOp_toShared_source` and
`cvtOp_toShared_target` — which say that a successful `toShared` forces
`source = co.source` and `target = co.target` — this covers every conversion the
2.0 semantics defines, and needs no width casts. -/
theorem cvtOpResult_iff_toShared (P : Profile) (op : CvtOp) (co : ConvertOp)
    (hco : op.toShared co.target co.source = some co) (x : BitVec co.source.width)
    (z : BitVec co.target.width) :
    CvtOpResult P co.target co.source op x z ↔ Numerics.convertP P co x (.ok z) := by
  cases op <;>
    rcases co with _ | sg' | ⟨s', t', sg'⟩ | ⟨s', t', sg'⟩ | ⟨s', t', sg'⟩ | _ | _ | ft | it <;>
    (try cases ft) <;> (try cases it) <;> (try cases s') <;> (try cases t') <;>
    simp_all [CvtOp.toShared, CvtOpResult, ConvertOp.source, ConvertOp.target,
      IntType.width, FloatType.width]

/-- A conversion outside the image of `toShared` has no result: the machine is
stuck, not trapped. -/
theorem cvtOpResult_eq_false (P : Profile) (target source : NumType) (op : CvtOp)
    (h : op.toShared target source = none) (x : BitVec source.width)
    (z : BitVec target.width) : ¬ CvtOpResult P target source op x z := by
  cases op <;> rcases target with t | t <;> rcases source with s | s <;>
    cases t <;> cases s <;>
    simp_all [CvtOp.toShared, CvtOpResult, IntType.width, FloatType.width]

/-- Nor does it trap. -/
theorem cvtOpTraps_eq_false (P : Profile) (target source : NumType) (op : CvtOp)
    (h : op.toShared target source = none) (x : BitVec source.width) :
    ¬ CvtOpTraps P target source op x := by
  cases op <;> rcases target with t | t <;> rcases source with s | s <;>
    cases t <;> cases s <;>
    simp_all [CvtOp.toShared, CvtOpTraps, IntType.width, FloatType.width]

/-- An `.error` result of `Numerics.convertP` is an `.error` result of the
deterministic `Numerics.convert`, for every profile. -/
theorem convertP_error {P : Profile} {op : ConvertOp} {x : Numerics.NumValue op.source}
    {e : Numerics.FloatTrap} (h : Numerics.convertP P op x (.error e)) :
    Numerics.convert op x = .error e := by
  rcases hn : P.nan with _ | _ <;> simp only [Numerics.convertP, hn] at h
  · cases op <;> exact h.symm
  · exact h.symm

/-- Only `TRUNC` can fail: every other scalar conversion is total. -/
theorem convert_error_trunc {op : ConvertOp} {x : Numerics.NumValue op.source}
    {e : Numerics.FloatTrap} (h : Numerics.convert op x = .error e) :
    ∃ s t sg, op = .trunc s t sg := by
  cases op <;> (try (rename_i a; cases a)) <;> first
    | exact ⟨_, _, _, rfl⟩
    | simp_all [Numerics.convert]

/-- On the image of `toShared`, at least one of `Step_pure/cvtop-val` and
`Step_pure/cvtop-trap` applies, so conversion never gets stuck when it is
defined. -/
theorem cvtOpResult_or_traps (P : Profile) (op : CvtOp) (co : ConvertOp)
    (hco : op.toShared co.target co.source = some co) (x : BitVec co.source.width) :
    (∃ z, CvtOpResult P co.target co.source op x z) ∨
      CvtOpTraps P co.target co.source op x := by
  obtain ⟨r, hr⟩ := Numerics.convertP_nonempty P co x
  rcases r with e | z
  · refine Or.inr ?_
    obtain ⟨s, t, sg, rfl⟩ := convert_error_trunc (convertP_error hr)
    cases op <;> simp only [CvtOp.toShared, ConvertOp.source, ConvertOp.target] at hco <;>
      simp_all
    exact ⟨e, hr⟩
  · exact Or.inl ⟨z, (cvtOpResult_iff_toShared P op co hco x z).mpr hr⟩

/-- `TRUNC_SAT` agrees with `TRUNC` wherever `TRUNC` succeeds
(`Numerics.truncSatFloat_agrees`); this is the 2.0 statement of
`Silmaril.Wasm.Numerics.convertRel_truncSat_of_trunc`. -/
theorem cvtOpResult_truncSat_of_trunc (P : Profile) (t : IntType) (s : FloatType)
    (sg : Signedness) (x : BitVec (NumType.float s).width)
    (z : BitVec (NumType.int t).width)
    (h : CvtOpResult P (.int t) (.float s) (.trunc sg) x z) :
    CvtOpResult P (.int t) (.float s) (.truncSat sg) x z := by
  simp only [CvtOpResult, Numerics.convertP] at h ⊢
  rcases hn : P.nan with _ | _ <;> simp only [hn] at h ⊢
  · exact Numerics.convertRel_truncSat_of_trunc s t sg x z h
  · exact (Numerics.convert_truncSat_of_trunc s t sg x z h.symm).symm

/-! ### Vector: the 2.0 operators never reach a relaxed-SIMD operator

These are the theorems that make the `Profile`'s relaxed choices irrelevant to
Wasm 2.0. They are proved by `cases`, not assumed. -/

theorem VecIntBinOp_toShared_ne_relaxed (op : VecIntBinOp) :
    op.toShared ≠ .relaxedQ15mulrS := by
  cases op <;> simp [VecIntBinOp.toShared]

theorem VecFloatBinOp_toShared_ne_relaxedMin (op : VecFloatBinOp) :
    op.toShared ≠ .relaxedMin := by
  cases op <;> simp [VecFloatBinOp.toShared]

theorem VecFloatBinOp_toShared_ne_relaxedMax (op : VecFloatBinOp) :
    op.toShared ≠ .relaxedMax := by
  cases op <;> simp [VecFloatBinOp.toShared]

theorem VecExtBinOp_toShared_ne_relaxedDotS (op : VecExtBinOp) :
    op.toShared ≠ .relaxedDotS := by
  cases op <;> simp [VecExtBinOp.toShared]

theorem VecCvtOp_toShared_ne_relaxedTrunc (op : VecCvtOp) (sx : Signedness) (z : Bool) :
    op.toShared ≠ .relaxedTrunc sx z := by
  cases op <;> simp [VecCvtOp.toShared]

/-! ### Vector: agreement and profile irrelevance -/

theorem vvUnOp_eq (op : VecUnOp) (v : V128) : VVUnOp op v = Numerics.vvunop op v := rfl

theorem vvBinOp_eq (op : VecBinOp) (v w : V128) :
    VVBinOp op v w = Numerics.vvbinop op v w := rfl

theorem vvTernOp_eq (op : VecTernOp) (v w m : V128) :
    VVTernOp op v w m = Numerics.vvternop op v w m := rfl

theorem vvTestOp_eq (op : VecTestOp) (v : V128) :
    VVTestOp op v = Numerics.vvtestop op v := rfl

theorem vecIntUnOpResult_iff (sh : IntShape) (op : VecIntUnOp) (v r : V128) :
    VecIntUnOpResult sh op v r ↔ r = Numerics.vecIntUnOp sh op v := Iff.rfl

theorem VecIntUnOpResult_nonempty (sh : IntShape) (op : VecIntUnOp) (v : V128) :
    ∃ r, VecIntUnOpResult sh op v r := ⟨_, rfl⟩

theorem vecFloatUnOpResult_iff (P : Profile) (sh : FloatShape) (op : FloatUnOp) (v r : V128) :
    VecFloatUnOpResult P sh op v r ↔ Numerics.VecFloatUnOpRel P sh op v r := Iff.rfl

theorem VecFloatUnOpResult_nonempty (P : Profile) (sh : FloatShape) (op : FloatUnOp)
    (v : V128) : ∃ r, VecFloatUnOpResult P sh op v r :=
  Numerics.VecFloatUnOpRel_nonempty P sh op v

/-- `$vbinop_(Jnn X M, …)` is the deterministic shared `vbinopInt`: on the 2.0
operator image the relaxed branch of `Numerics.vecIntBinOp` is unreachable. -/
theorem vecIntBinOpResult_iff (P : Profile) (sh : IntShape) (op : VecIntBinOp)
    (a b r : V128) :
    VecIntBinOpResult P sh op a b r ↔ Numerics.vbinopInt sh op.toShared a b = some r := by
  cases op <;>
    simp [VecIntBinOpResult, VecIntBinOp.toShared, Numerics.vecIntBinOp,
      Numerics.vbinopIntRelaxed, Numerics.vbinopInt, eq_comm]

/-- The `Profile`'s `$ND` and `$R_*` builtins do not affect any 2.0 integer
vector binary operator. -/
theorem VecIntBinOpResult_nd_irrelevant (P Q : Profile) (sh : IntShape) (op : VecIntBinOp)
    (a b r : V128) : VecIntBinOpResult P sh op a b r ↔ VecIntBinOpResult Q sh op a b r := by
  rw [vecIntBinOpResult_iff, vecIntBinOpResult_iff]

theorem VecIntBinOpResult_nonempty (P : Profile) (sh : IntShape) (op : VecIntBinOp)
    (a b : V128) : ∃ r, VecIntBinOpResult P sh op a b r := ⟨_, rfl⟩

/-- With the spec NaN policy, `$vbinop_(Fnn X M, …)` is the shared float set
product `Numerics.vbinopFloatRel`. -/
theorem vecFloatBinOpResult_spec (P : Profile) (hP : P.nan = .spec) (sh : FloatShape)
    (op : VecFloatBinOp) (a b r : V128) :
    VecFloatBinOpResult P sh op a b r ↔ Numerics.vbinopFloatRel sh op.toShared a b r := by
  simp only [VecFloatBinOpResult, Numerics.VecFloatBinOpRel, hP]
  cases op <;> exact Iff.rfl

/-- With the canonical NaN policy it is the deterministic `Numerics.vbinopFloat`. -/
theorem vecFloatBinOpResult_canonical (P : Profile) (hP : P.nan = .canonical)
    (sh : FloatShape) (op : VecFloatBinOp) (a b r : V128) :
    VecFloatBinOpResult P sh op a b r ↔ Numerics.vbinopFloat sh op.toShared a b = some r := by
  simp only [VecFloatBinOpResult, Numerics.VecFloatBinOpRel, hP]
  cases op <;> exact Iff.rfl

/-- `Numerics.vbinopFloat` is defined on the whole 2.0 operator image. -/
theorem vbinopFloat_toShared_isSome (sh : FloatShape) (op : VecFloatBinOp) (a b : V128) :
    ∃ r, Numerics.vbinopFloat sh op.toShared a b = some r := by
  cases op <;> exact ⟨_, rfl⟩

/-- Only `Profile.nan` matters: `$ND` and `$R_*` are irrelevant to 2.0 float
vector binary operators. -/
theorem VecFloatBinOpResult_nd_irrelevant (P Q : Profile) (hPQ : P.nan = Q.nan)
    (sh : FloatShape) (op : VecFloatBinOp) (a b r : V128) :
    VecFloatBinOpResult P sh op a b r ↔ VecFloatBinOpResult Q sh op a b r := by
  rcases hn : Q.nan with _ | _
  · rw [vecFloatBinOpResult_spec P (hPQ.trans hn), vecFloatBinOpResult_spec Q hn]
  · rw [vecFloatBinOpResult_canonical P (hPQ.trans hn), vecFloatBinOpResult_canonical Q hn]

theorem VecFloatBinOpResult_nonempty (P : Profile) (sh : FloatShape) (op : VecFloatBinOp)
    (a b : V128) : ∃ r, VecFloatBinOpResult P sh op a b r := by
  obtain ⟨r, hr⟩ := vbinopFloat_toShared_isSome sh op a b
  refine ⟨r, ?_⟩
  show Numerics.VecFloatBinOpRel P sh op.toShared a b r
  unfold Numerics.VecFloatBinOpRel
  cases P.nan
  · cases op <;> exact Numerics.vbinopFloatRel_self _ _ _ _ _ hr
  · cases op <;> exact hr

theorem vecAllTrue_eq (sh : IntShape) (v : V128) :
    VecAllTrue sh v = Numerics.vecAllTrue sh v := rfl

theorem vecIntRelOp_eq (sh : IntShape) (op : IntRelOp) (a b : V128) :
    VecIntRelOp sh op a b = Numerics.vecIntRelOp sh op a b := rfl

theorem vecFloatRelOp_eq (sh : FloatShape) (op : FloatRelOp) (a b : V128) :
    VecFloatRelOp sh op a b = Numerics.vecFloatRelOp sh op a b := rfl

theorem vecShiftOp_eq (sh : IntShape) (op : Wasm.VecShiftOp) (v : V128) (n : BitVec 32) :
    VecShiftOp sh op v n = Numerics.vecShiftOp sh op v n := rfl

theorem vecBitmask_eq (sh : IntShape) (v : V128) :
    VecBitmask sh v = Numerics.vecBitmask sh v := rfl

theorem vecSwizzle_eq (a b : V128) : VecSwizzle a b = Numerics.vecSwizzle a b := rfl

theorem vecShuffle_eq (idx : List LaneIdx) (a b : V128) :
    VecShuffle idx a b = Numerics.vecShuffle idx a b := rfl

theorem vecSplat_eq (sh : Shape) (x : BitVec sh.unpacked.width) :
    VecSplat sh x = Numerics.vecSplat sh x := rfl

theorem vecExtractLane_eq (sh : Shape) (sx : Option Signedness) (i : Nat) (v : V128) :
    VecExtractLane sh sx i v = Numerics.vecExtractLane sh sx i v := rfl

theorem vecReplaceLane_eq (sh : Shape) (i : Nat) (v : V128) (x : BitVec sh.unpacked.width) :
    VecReplaceLane sh i v x = Numerics.vecReplaceLane sh i v x := rfl

theorem vecNarrow_eq (target source : IntShape) (sx : Signedness) (a b : V128) :
    VecNarrow target source sx a b = Numerics.vnarrow source target sx a b := rfl

/-- Extracting a lane of a splat returns the (wrapped) scalar: a sanity check
that `VecSplat`/`VecExtractLane` agree on lane layout. -/
theorem vecExtractLane_vecSplat (sh : Shape) (i : Nat) (hi : i < sh.lanes)
    (x : BitVec sh.unpacked.width) :
    Numerics.vextractLane sh i (VecSplat sh x) = x.setWidth sh.laneWidth :=
  Numerics.vextractLane_vsplat sh i hi x

theorem vecExtUnOpResult_iff (target source : IntShape) (op : VecExtUnOp) (a r : V128) :
    VecExtUnOpResult target source op a r ↔ r = Numerics.vextunop source target op a :=
  Iff.rfl

theorem VecExtUnOpResult_nonempty (target source : IntShape) (op : VecExtUnOp) (a : V128) :
    ∃ r, VecExtUnOpResult target source op a r := ⟨_, rfl⟩

/-- `$vextbinop__` is the deterministic shared `vextbinop`: the relaxed branch is
unreachable on the 2.0 operator image. -/
theorem vecExtBinOpResult_iff (P : Profile) (target source : IntShape) (op : VecExtBinOp)
    (a b r : V128) :
    VecExtBinOpResult P target source op a b r ↔
      Numerics.vextbinop source target op.toShared a b = some r := by
  cases op <;> exact Iff.rfl

theorem VecExtBinOpResult_nd_irrelevant (P Q : Profile) (target source : IntShape)
    (op : VecExtBinOp) (a b r : V128) :
    VecExtBinOpResult P target source op a b r ↔ VecExtBinOpResult Q target source op a b r := by
  rw [vecExtBinOpResult_iff, vecExtBinOpResult_iff]

theorem VecExtBinOpResult_nonempty (P : Profile) (target source : IntShape)
    (op : VecExtBinOp) (a b : V128) : ∃ r, VecExtBinOpResult P target source op a b r := by
  cases op <;> exact ⟨_, rfl⟩

/-- With the spec NaN policy, `$vcvtop__` is the shared `Numerics.vcvtopRel`. -/
theorem vecCvtOpResult_spec (P : Profile) (hP : P.nan = .spec) (target source : Shape)
    (op : VecCvtOp) (a r : V128) :
    VecCvtOpResult P target source op a r ↔
      Numerics.vcvtopRel op.toShared source target a r := by
  simp only [VecCvtOpResult, Numerics.VecConvertRel]
  cases op <;> simp only [VecCvtOp.toShared, hP]

/-- With the canonical NaN policy it is the deterministic `Numerics.vcvtop`. -/
theorem vecCvtOpResult_canonical (P : Profile) (hP : P.nan = .canonical)
    (target source : Shape) (op : VecCvtOp) (a r : V128) :
    VecCvtOpResult P target source op a r ↔
      Numerics.vcvtop op.toShared source target a = some r := by
  simp only [VecCvtOpResult, Numerics.VecConvertRel]
  cases op <;> simp only [VecCvtOp.toShared, hP]

theorem VecCvtOpResult_nd_irrelevant (P Q : Profile) (hPQ : P.nan = Q.nan)
    (target source : Shape) (op : VecCvtOp) (a r : V128) :
    VecCvtOpResult P target source op a r ↔ VecCvtOpResult Q target source op a r := by
  rcases hn : Q.nan with _ | _
  · rw [vecCvtOpResult_spec P (hPQ.trans hn), vecCvtOpResult_spec Q hn]
  · rw [vecCvtOpResult_canonical P (hPQ.trans hn), vecCvtOpResult_canonical Q hn]

/-- Every shape combination admitted by `Instr.immediatesValid` has a result, so
`Step_pure/vcvtop-*` never gets stuck on a validated instruction. -/
theorem VecCvtOpResult_nonempty (P : Profile) (target source : Shape) (op : VecCvtOp)
    (h : op.valid target source = true) (a : V128) :
    ∃ r, VecCvtOpResult P target source op a r :=
  Numerics.VecConvertRel_nonempty P h a

end Silmaril.Wasm.V2.Execution
