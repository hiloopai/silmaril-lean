module

public import Silmaril.Wasm.V2.Types
public import Silmaril.Wasm.Ops

/-!
# WebAssembly 2.0 operators

Transcribed from `specification/wasm-2.0/1-syntax.spectec` (`Operators`,
`1-syntax:200-393`) at WebAssembly/spec revision
`608711107b7f1edb13efd57b7d79b49477462d36`.

SpecTec indexes the operator families by their type (`unop_(numtype)`,
`vbinop_(shape)`, …). We flatten each family into a plain inductive and keep
the indexing as an explicit argument of the instruction, as the Core 3.0 and
1.0 layers do.

Where a 2.0 family coincides exactly with the shared one in
`Silmaril.Wasm.Ops` we reuse the shared type: `IntUnOp`, `IntBinOp`,
`IntTestOp`, `IntRelOp`, `FloatUnOp`, `FloatBinOp`, `FloatRelOp`, `Signedness`,
`PackSize`, `Half`, `VecUnOp`, `VecBinOp`, `VecTernOp`, `VecTestOp`,
`VecIntUnOp`, `VecShiftOp`, `VecExtUnOp`. The families that differ do so only
because the shared type also carries relaxed-SIMD operators, which Wasm 2.0
does not have; those get a 2.0-specific type together with an injection into
the shared one, so the existing numerics apply unchanged.
-/

@[expose] public section

namespace Silmaril.Wasm.V2

/-! ## Scalar conversions

`cvtop ::= EXTEND sx | WRAP | CONVERT sx | TRUNC sx | TRUNC_SAT sx | PROMOTE |
DEMOTE | REINTERPRET` (`1-syntax:305-313`).

SpecTec keeps the source and target types in the *instruction*
(`CVTOP numtype_1 numtype_2 cvtop`, with `numtype_1` the target and
`numtype_2` the source, per `Instr_ok/cvtop-convert`). We keep that shape. -/

/-- `cvtop` (`1-syntax:305-313`). -/
inductive CvtOp where
  | extend (sign : Signedness)
  | wrap
  | convert (sign : Signedness)
  | trunc (sign : Signedness)
  | truncSat (sign : Signedness)
  | promote
  | demote
  | reinterpret
  deriving DecidableEq, Repr

/-- The shared `ConvertOp` this 2.0 conversion denotes at the given target and
source types, if the combination is one the 2.0 semantics defines
(`3-numerics:310-318`). `none` means the combination has no `$cvtop__` equation,
which the typing rules of `6-typing` nevertheless admit for `cvtop-convert`;
see `Silmaril.Wasm.V2.Validation`. -/
def CvtOp.toShared : NumType → NumType → CvtOp → Option ConvertOp
  | .int .i64, .int .i32, .extend s => some (.extend s)
  | .int .i32, .int .i64, .wrap => some .wrap
  | .float t, .int s, .convert sg => some (.convert s t sg)
  | .int t, .float s, .trunc sg => some (.trunc s t sg)
  | .int t, .float s, .truncSat sg => some (.truncSat s t sg)
  | .float .f64, .float .f32, .promote => some .promote
  | .float .f32, .float .f64, .demote => some .demote
  | .int t, .float s, .reinterpret =>
      if s.width = t.width then some (.reinterpretInt s) else none
  | .float t, .int s, .reinterpret =>
      if s.width = t.width then some (.reinterpretFloat s) else none
  | _, _, _ => none

/-- The four reinterpretations `3-numerics` defines are exactly the pairs of
distinct number types of equal width, so `Instr_ok/cvtop-reinterpret`'s premises
already imply definedness. -/
theorem CvtOp.toShared_reinterpret_isSome {t₁ t₂ : NumType} (hne : t₁ ≠ t₂)
    (hsize : t₁.width = t₂.width) : (CvtOp.toShared t₁ t₂ .reinterpret).isSome := by
  match t₁, t₂ with
  | .int .i32, .int .i32 | .int .i64, .int .i64
  | .float .f32, .float .f32 | .float .f64, .float .f64 => exact absurd rfl hne
  | .int .i32, .int .i64 | .int .i64, .int .i32
  | .float .f32, .float .f64 | .float .f64, .float .f32
  | .int .i32, .float .f64 | .int .i64, .float .f32
  | .float .f32, .int .i64 | .float .f64, .int .i32 => exact absurd hsize (by decide)
  | .int .i32, .float .f32 | .int .i64, .float .f64
  | .float .f32, .int .i32 | .float .f64, .int .i64 => rfl

/-! ## Vector operators -/

/-- `vbinop_(Jnn X M)` (`1-syntax:340-349`). The shared `Wasm.VecIntBinOp` is this
type plus `relaxedQ15mulrS`, which 2.0 does not have. -/
inductive VecIntBinOp where
  | add | sub | mul
  | addSat (sign : Signedness)
  | subSat (sign : Signedness)
  | avgrU
  | q15mulrSatS
  | min (sign : Signedness)
  | max (sign : Signedness)
  deriving DecidableEq, Repr

/-- The injection into the shared operator type. -/
def VecIntBinOp.toShared : VecIntBinOp → Wasm.VecIntBinOp
  | .add => .add | .sub => .sub | .mul => .mul
  | .addSat s => .addSat s | .subSat s => .subSat s
  | .avgrU => .avgrU | .q15mulrSatS => .q15mulrSatS
  | .min s => .min s | .max s => .max s

/-- The side conditions of `1-syntax:341-349`, read off the shape. -/
def VecIntBinOp.valid (s : IntShape) : VecIntBinOp → Bool
  | .add | .sub => true
  | .mul => 16 ≤ s.laneWidth
  | .addSat _ | .subSat _ | .avgrU => s.laneWidth ≤ 16
  | .q15mulrSatS => s.laneWidth == 16
  | .min _ | .max _ => s.laneWidth ≤ 32

/-- `vbinop_(Fnn X M) = ADD | SUB | MUL | DIV | MIN | MAX | PMIN | PMAX`
(`1-syntax:350`). The shared type adds `relaxedMin`/`relaxedMax`. -/
inductive VecFloatBinOp where
  | add | sub | mul | div | min | max | pmin | pmax
  deriving DecidableEq, Repr

def VecFloatBinOp.toShared : VecFloatBinOp → Wasm.VecFloatBinOp
  | .add => .add | .sub => .sub | .mul => .mul | .div => .div
  | .min => .min | .max => .max | .pmin => .pmin | .pmax => .pmax

/-- `vextbinop_(Jnn X M) = EXTMUL half sx | DOT S` (`1-syntax:376-378`). The
shared type adds `relaxedDotS`. -/
inductive VecExtBinOp where
  | extmul (half : Half) (sign : Signedness)
  | dotS
  deriving DecidableEq, Repr

def VecExtBinOp.toShared : VecExtBinOp → Wasm.VecExtBinOp
  | .extmul h s => .extmul h s
  | .dotS => .dotS

/-- The side conditions of `vextbinop_(Jnn X M)` (`1-syntax:377-378`) together
with the lane-doubling condition of the `VEXTBINOP` production
(`1-syntax:465-467`): `EXTMUL` doubles the lane width, `DOT S` needs a 32-bit
result lane. `target` is `ishape_1` of SpecTec (the result shape) and `source`
is `ishape_2` (the operand shape). -/
def VecExtBinOp.valid (target source : IntShape) : VecExtBinOp → Bool
  | .extmul _ _ => target.laneWidth == 2 * source.laneWidth
  | .dotS => target.laneWidth == 32 && source.laneWidth == 16

/-- The side condition of `vextunop_(Jnn X M)` (`1-syntax:373-374`):
`EXTADD_PAIRWISE sx` needs `16 ≤ |Jnn_1| ≤ 32`, with `Jnn_1` the result lane
type, together with the lane-doubling condition of the `VEXTUNOP` production
(`1-syntax:462-464`). -/
def VecExtUnOp.valid2 (target source : IntShape) (_op : Wasm.VecExtUnOp) : Bool :=
  target.laneWidth == 2 * source.laneWidth && 16 ≤ target.laneWidth && target.laneWidth ≤ 32

/-- `vcvtop ::= EXTEND half sx | TRUNC_SAT sx zero? | CONVERT half? sx |
DEMOTE zero | PROMOTE LOW` (`1-syntax:367`). The shared type adds
`relaxedTrunc`. -/
inductive VecCvtOp where
  | extend (half : Half) (sign : Signedness)
  | truncSat (sign : Signedness) (zero : Bool)
  | convert (half : Option Half) (sign : Signedness)
  | demoteZero
  | promoteLow
  deriving DecidableEq, Repr

def VecCvtOp.toShared : VecCvtOp → Wasm.VecConvertOp
  | .extend h s => .extend h s
  | .truncSat s z => .truncSat s z
  | .convert h s => .convert h s
  | .demoteZero => .demoteZero
  | .promoteLow => .promoteLow

/-- The combinations the 2.0 reduction rules `Step_pure/vcvtop-*` define. -/
def VecCvtOp.valid (target source : Shape) (op : VecCvtOp) : Bool :=
  op.toShared.valid source target

/-- `vloadop ::= SHAPE n X n _ sx | SPLAT n | ZERO n` (`1-syntax:390-393`). -/
inductive VecLoadOp where
  | shape8x8 (sign : Signedness)
  | shape16x4 (sign : Signedness)
  | shape32x2 (sign : Signedness)
  | splat (size : PackSize)
  | zero32
  | zero64
  deriving DecidableEq, Repr

/-- The shared load shape; `none` of `VLOAD vectype vloadop? memarg` is
`VecLoadOp.full`. -/
def VecLoadOp.toShared : VecLoadOp → Wasm.VecLoadOp
  | .shape8x8 s => .extend8x8 s
  | .shape16x4 s => .extend16x4 s
  | .shape32x2 s => .extend32x2 s
  | .splat sz => .splat sz
  | .zero32 => .zero32
  | .zero64 => .zero64

/-- The number of bits a vector load touches, for the alignment conditions of
`Instr_ok/vload-*` (`6-typing:497-519`). -/
def VecLoadOp.accessWidth : Option VecLoadOp → Nat
  | none => 128
  | some (.shape8x8 _) => 64
  | some (.shape16x4 _) => 64
  | some (.shape32x2 _) => 64
  | some (.splat sz) => sz.width
  | some .zero32 => 32
  | some .zero64 => 64

/-! ## Memory arguments -/

/-- `memarg ::= {ALIGN u32, OFFSET u32}` (`1-syntax:383`). Both fields are `u32`;
2.0 has no 64-bit offsets and no explicit memory index. -/
structure MemArg where
  align : Fin (2 ^ 32)
  offset : Fin (2 ^ 32)
  deriving DecidableEq, Repr

end Silmaril.Wasm.V2
