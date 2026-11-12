module

public import Silmaril.Wasm.SpecTec.Sim.FloatSimd.Defs
public import Silmaril.Wasm.SpecTec.Sim.IntNumeric.Defs

/-!
# SpecTec ↔ Core 3.0, float track: the float and conversion primitives

The pinned script declares the scalar float operators (`$fabs_` … `$fcopysign_`, `$feq_` …
`$fge_`) and the conversions (`$wrap__`, `$extend__`, `$trunc__`, `$trunc_sat__`, `$convert__`,
`$promote__`, `$demote__`, `$reinterpret__`) `hint(builtin)` with no clause
(`3.1-numerics.scalar.spectec:242-333`). `floatCall P` interprets them by Core's numerics under
the profile `P` (`Silmaril.Wasm.Numerics.Profile`):

* a set-valued operator (`fN(N)*`) returns the list of **every** bit pattern the profile allows
  (`floatUnOpP`, `floatBinOpP`, `convertP` for `$promote__`/`$demote__`), encoded by `floatV`;
  at `Profile.spec nd r` that is every NaN payload Core's NaN policy permits;
* a comparison returns Core's `floatRelOp` as a `u32`;
* an optional conversion (`iN(N')?`: `$trunc__`, `$trunc_sat__`) returns `?(c)` when the profile
  gives a result and `?()` when it traps;
* a single-valued conversion returns the profile's (unique) result;
* `$wrap__`/`$extend__` are the bit operations at every width (they also serve the reference and
  lane rules, at widths 31 and the packed lane widths).

The argument decoders are the inverses of the encodings (`floatV`, `numV`, `numTypeV`), defined by
choice and computed on encodings by injectivity. `FloatB P B` says that `B` extends `floatCall P`;
`floatIntB P` is a concrete `B` extending both the integer primitives (`IntNumeric.intCall`) and
`floatCall P`.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Floats

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv (bvV)
open Silmaril.SpecTec.Equiv.ExecBuiltins (asBits?)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution.Core (NumVal)

/-! ## Finite enumerations and decoders -/

/-- Every bit pattern of width `n`. -/
def allBits (n : Nat) : List (BitVec n) := (List.range (2 ^ n)).map (BitVec.ofNat n)

/-- The bit patterns of width `n` satisfying `R` (a classical filter of `allBits`). -/
noncomputable def bitsWhere (n : Nat) (R : BitVec n → Prop) : List (BitVec n) :=
  open Classical in (allBits n).filter (fun z => decide (R z))

/-- The numeral of type `t` that `v` encodes, if any (`numV` is injective at each type). -/
noncomputable def decNum (t : NumType) (v : Value) : Option (BitVec t.width) :=
  open Classical in
  if h : ∃ b : BitVec t.width, numV ⟨t, b⟩ = v then some (Classical.choose h) else none

/-- The number type that `v` encodes, if any. -/
noncomputable def decNumType (v : Value) : Option NumType :=
  open Classical in
  if h : ∃ t : NumType, Vec.numTypeV t = v then some (Classical.choose h) else none

/-- The float type of a width. -/
def floatOfWidth : Nat → Option FloatType
  | 32 => some .f32
  | 64 => some .f64
  | _ => none

/-- The integer type of a width. -/
def intOfWidth : Nat → Option IntType
  | 32 => some .i32
  | 64 => some .i64
  | _ => none

/-- The reinterpretation between two number types of the same width. -/
def reinterpOp? : NumType → NumType → Option ConvertOp
  | .float .f32, .int .i32 => some (.reinterpretInt .f32)
  | .float .f64, .int .i64 => some (.reinterpretInt .f64)
  | .int .i32, .float .f32 => some (.reinterpretFloat .i32)
  | .int .i64, .float .f64 => some (.reinterpretFloat .i64)
  | _, _ => none

/-! ## The primitives -/

/-- `$f…_(N, f)`: every result of the unary operator the profile allows. -/
noncomputable def fUn (P : Profile) (op : FloatUnOp) (N : Nat) (a : Value) : Option Value := do
  let t ← floatOfWidth N
  let x ← decNum (.float t) a
  pure (.list ((bitsWhere t.width (floatUnOpP P t op x)).map (floatV t)))

/-- `$f…_(N, f_1, f_2)`: every result of the binary operator the profile allows. -/
noncomputable def fBin (P : Profile) (op : FloatBinOp) (N : Nat) (a b : Value) :
    Option Value := do
  let t ← floatOfWidth N
  let x ← decNum (.float t) a
  let y ← decNum (.float t) b
  pure (.list ((bitsWhere t.width (floatBinOpP P t op x y)).map (floatV t)))

/-- `$f…_(N, f_1, f_2) : u32`: Core's comparison. -/
noncomputable def fRel (op : FloatRelOp) (N : Nat) (a b : Value) : Option Value := do
  let t ← floatOfWidth N
  let x ← decNum (.float t) a
  let y ← decNum (.float t) b
  pure (Vec.i32NV (floatRelOp t op x y))

/-- The profile's successful result of a conversion, if any. -/
noncomputable def convRes (P : Profile) (op : ConvertOp) (x : BitVec op.source.width) :
    Option (BitVec op.target.width) :=
  open Classical in
  if h : ∃ z, convertP P op x (.ok z) then some (Classical.choose h) else none

/-- A single-valued conversion (`$convert__`, `$reinterpret__`). -/
noncomputable def convOne (P : Profile) (op : ConvertOp) (a : Value) : Option Value := do
  let x ← decNum op.source a
  let z ← convRes P op x
  pure (numV ⟨op.target, z⟩)

/-- An optional conversion (`$trunc__`, `$trunc_sat__`): `?()` when the conversion traps. -/
noncomputable def convOpt (P : Profile) (op : ConvertOp) (a : Value) : Option Value := do
  let x ← decNum op.source a
  pure (.opt ((convRes P op x).map fun z => numV ⟨op.target, z⟩))

/-- A set-valued conversion (`$promote__`, `$demote__`): every result the profile allows. -/
noncomputable def convList (P : Profile) (op : ConvertOp) (a : Value) : Option Value := do
  let x ← decNum op.source a
  pure (.list ((bitsWhere op.target.width (fun z => convertP P op x (.ok z))).map
    fun z => numV ⟨op.target, z⟩))

/-- `$wrap__(N, N', i)`: the low `N'` bits. -/
def wrapBits (N N' : Nat) (a : Value) : Option Value := do
  let x ← asBits? N a
  pure (bvV (x.setWidth N'))

/-- `$extend__(N, N', sx, i)`: sign or zero extension to `N'` bits. -/
def extendBits (N N' : Nat) (s a : Value) : Option Value := do
  let sx ← IntNumeric.asSx? s
  let x ← asBits? N a
  pure (bvV (match sx with | .signed => x.signExtend N' | .unsigned => x.setWidth N'))

/-- The names `floatCall` answers. -/
def floatNames : List IL.Id :=
  ["fabs_", "fneg_", "fsqrt_", "fceil_", "ffloor_", "ftrunc_", "fnearest_",
   "fadd_", "fsub_", "fmul_", "fdiv_", "fmin_", "fmax_", "fcopysign_",
   "feq_", "fne_", "flt_", "fgt_", "fle_", "fge_",
   "wrap__", "extend__", "trunc__", "trunc_sat__", "convert__", "promote__", "demote__",
   "reinterpret__"]

/-- The float and conversion primitives at the argument shapes their declarations give them,
before the name filter. -/
noncomputable def floatCall' (P : Profile) : IL.Id → List ArgV → Option Value
  | "fabs_", [.val (.num (.natN N)), .val a] => fUn P .abs N a
  | "fneg_", [.val (.num (.natN N)), .val a] => fUn P .neg N a
  | "fsqrt_", [.val (.num (.natN N)), .val a] => fUn P .sqrt N a
  | "fceil_", [.val (.num (.natN N)), .val a] => fUn P .ceil N a
  | "ffloor_", [.val (.num (.natN N)), .val a] => fUn P .floor N a
  | "ftrunc_", [.val (.num (.natN N)), .val a] => fUn P .trunc N a
  | "fnearest_", [.val (.num (.natN N)), .val a] => fUn P .nearest N a
  | "fadd_", [.val (.num (.natN N)), .val a, .val b] => fBin P .add N a b
  | "fsub_", [.val (.num (.natN N)), .val a, .val b] => fBin P .sub N a b
  | "fmul_", [.val (.num (.natN N)), .val a, .val b] => fBin P .mul N a b
  | "fdiv_", [.val (.num (.natN N)), .val a, .val b] => fBin P .div N a b
  | "fmin_", [.val (.num (.natN N)), .val a, .val b] => fBin P .min N a b
  | "fmax_", [.val (.num (.natN N)), .val a, .val b] => fBin P .max N a b
  | "fcopysign_", [.val (.num (.natN N)), .val a, .val b] => fBin P .copysign N a b
  | "feq_", [.val (.num (.natN N)), .val a, .val b] => fRel .eq N a b
  | "fne_", [.val (.num (.natN N)), .val a, .val b] => fRel .ne N a b
  | "flt_", [.val (.num (.natN N)), .val a, .val b] => fRel .lt N a b
  | "fgt_", [.val (.num (.natN N)), .val a, .val b] => fRel .gt N a b
  | "fle_", [.val (.num (.natN N)), .val a, .val b] => fRel .le N a b
  | "fge_", [.val (.num (.natN N)), .val a, .val b] => fRel .ge N a b
  | "wrap__", [.val (.num (.natN N)), .val (.num (.natN N')), .val a] => wrapBits N N' a
  | "extend__", [.val (.num (.natN N)), .val (.num (.natN N')), .val s, .val a] =>
      extendBits N N' s a
  | "trunc__", [.val (.num (.natN N)), .val (.num (.natN N')), .val s, .val a] => do
      let t ← floatOfWidth N
      let i ← intOfWidth N'
      let sx ← IntNumeric.asSx? s
      convOpt P (.trunc t i sx) a
  | "trunc_sat__", [.val (.num (.natN N)), .val (.num (.natN N')), .val s, .val a] => do
      let t ← floatOfWidth N
      let i ← intOfWidth N'
      let sx ← IntNumeric.asSx? s
      convOpt P (.truncSat t i sx) a
  | "convert__", [.val (.num (.natN N)), .val (.num (.natN N')), .val s, .val a] => do
      let i ← intOfWidth N
      let t ← floatOfWidth N'
      let sx ← IntNumeric.asSx? s
      convOne P (.convert i t sx) a
  | "promote__", [.val (.num (.natN 32)), .val (.num (.natN 64)), .val a] => convList P .promote a
  | "demote__", [.val (.num (.natN 64)), .val (.num (.natN 32)), .val a] => convList P .demote a
  | "reinterpret__", [.val n₁, .val n₂, .val a] => do
      let t₁ ← decNumType n₁
      let t₂ ← decNumType n₂
      let op ← reinterpOp? t₁ t₂
      convOne P op a
  | _, _ => none

open Classical in
/-- **The float and conversion primitives** under the profile `P`: `floatCall'` on the names of
`floatNames`, nothing elsewhere. -/
noncomputable def floatCall (P : Profile) (x : IL.Id) (ws : List ArgV) : Option Value :=
  if x ∈ floatNames then floatCall' P x ws else none

/-- `B` extends the float primitives of the profile `P`. -/
def FloatB (P : Profile) (B : Builtins) : Prop :=
  ∀ x ws v, floatCall P x ws = some v → B.call x ws = some v

open Classical in
/-- **A concrete interpretation of the primitives** for the profile `P`: the float primitives on
`floatNames`, the integer primitives elsewhere. -/
noncomputable def floatIntB (P : Profile) : Builtins :=
  ⟨fun x ws => if x ∈ floatNames then floatCall' P x ws else IntNumeric.intCall x ws⟩

end Silmaril.Wasm.SpecTec.Sim.Floats
