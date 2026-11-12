module

public import Silmaril.Wasm.SpecTec.Sim.FloatSimd.Defs
public import Silmaril.Wasm.Numerics.VectorProfile

/-!
# SpecTec ↔ Core 3.0, round 5, track simd: `$lanes_` and `$inv_lanes_` as primitives

`3.2-numerics.vector.spectec` declares `$lanes_(shape, vec_(V128)) : lane_($lanetype(shape))*` and
its inverse `$inv_lanes_` with `hint(builtin)` and no clause, so `callDef` always falls back to `B`
for them. Until round 5 `Prims.builtins` answered neither, so every vector operator other than the
bitwise ones, and the rules `vtestop`, `vsplat`, `vextract_lane` and `vreplace_lane`, denoted
nothing, and family V's `VecAgree` was false (`Round5.Simd.not_vecAgree_of_lanes`).

This header gives both primitives Core's meaning (`Silmaril.Wasm.Shape.lanesOf`,
`Shape.invLanes`) on images:

* a lane of an integer shape is the numeral `%(n)` of its bits (`iN`, also for the packed lanes
  `I8`, `I16`); a lane of a float shape is SpecTec's `fN` encoding `floatV` of its bits;
* `lanesCall sh v`: at the image of a shape and of a 128-bit pattern, the images of its lanes;
* `invLanesCall sh ls`: at the image of a shape and of the lane images of some pattern, that
  pattern (unique, `Round5.Simd.lanesV_injective`).

`Prims.call` consults them after every other primitive (`Prims.builtins` stays the concrete `B`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Simd

open Silmaril.SpecTec
open Silmaril.SpecTec.Sem
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.SpecTec.Equiv.Execution (pctV)

/-- A lane of the shape `sh`, as SpecTec's `lane_($lanetype(sh))`: `%(n)` for integer lanes,
`fN` for float lanes. -/
def laneV : (sh : Shape) → BitVec sh.laneWidth → Value
  | .int _, x => pctV x.toNat
  | .float .f32x4, x => floatV .f32 x
  | .float .f64x2, x => floatV .f64 x

/-- The lanes of a 128-bit pattern at the shape `sh`, as SpecTec values. -/
def lanesV (sh : Shape) (a : V128) : List Value := (sh.lanesOf a).map (laneV sh)

/-- `$lanes_(sh, v)`: at the image of a shape and a pattern, the images of its lanes. -/
noncomputable def lanesCall (sv v : Value) : Option Value :=
  open Classical in
  if h : ∃ p : Shape × V128, sv = Vec.shapeV p.1 ∧ v = Vec.vecV p.2 then
    some (.list (lanesV h.choose.1 h.choose.2))
  else none

/-- `$inv_lanes_(sh, c*)`: at the image of a shape and the lane images of a pattern, that
pattern. -/
noncomputable def invLanesCall (sv lv : Value) : Option Value :=
  open Classical in
  if h : ∃ p : Shape × V128, sv = Vec.shapeV p.1 ∧ lv = .list (lanesV p.1 p.2) then
    some (Vec.vecV h.choose.2)
  else none

/-! ## Pass 3: the lane-wise operators as primitives (fallbacks)

The SpecTec clauses of the lane-wise vector operators (`$vunop_`, `$vbinop_`, …, `$vnarrowop__`,
`$vcvtop__`) bind the lanes of their operands in an `if` premise (`c_1* = $lanes_(…)`, directly or
in the helper they call, `$ivunop_`, `$fvbinop_`, …). The IL evaluator's `if` only tests, so every
clause definitely fails and `callDef` falls back to `B` (as for `$irem_`). `vecOpCall P x ws`
answers those calls, at the images of their arguments, by Core's vector numerics under the profile
`P`: the deterministic operators by their value, the NaN-nondeterministic float operators (which
SpecTec lists with `$setproduct_`) by the list of all allowed results (`vecsOf`), and the partial
ones only where Core defines them. `$vcvtop__` is a function in SpecTec but a relation in Core
under the spec NaN profile; it answers one allowed result (`someVec`).
-/

/-- Decoding an argument list through an encoding, by choice. -/
noncomputable def decodeArgs {α : Type} (enc : α → List ArgV) (ws : List ArgV) : Option α :=
  open Classical in if h : ∃ p, enc p = ws then some h.choose else none

/-- Every 128-bit pattern satisfying `R`, as SpecTec values. -/
noncomputable def vecsOf (R : V128 → Prop) : List Value :=
  open Classical in
  ((List.range (2 ^ 128)).filter fun n => decide (R (BitVec.ofNat 128 n))).map
    fun n => Vec.vecV (BitVec.ofNat 128 n)

/-- Some 128-bit pattern satisfying `R`, if there is one. -/
noncomputable def someVec (R : V128 → Prop) : Option Value :=
  open Classical in if h : ∃ r, R r then some (Vec.vecV h.choose) else none

/-- `$vunop_` on integer shapes, arguments. -/
def encIntUnOp (p : IntShape × VecIntUnOp × V128) : List ArgV :=
  [.val (Vec.ishV p.1), .val (Vec.vIntUnOpV p.2.1), .val (Vec.vecV p.2.2)]
/-- `$vunop_` on float shapes, arguments. -/
def encFloatUnOp (p : FloatShape × FloatUnOp × V128) : List ArgV :=
  [.val (Vec.fshV p.1), .val (Vec.vFloatUnOpV p.2.1), .val (Vec.vecV p.2.2)]
/-- `$vbinop_` on integer shapes, arguments. -/
def encIntBinOp (p : IntShape × VecIntBinOp × V128 × V128) : List ArgV :=
  [.val (Vec.ishV p.1), .val (Vec.vIntBinOpV p.2.1), .val (Vec.vecV p.2.2.1),
    .val (Vec.vecV p.2.2.2)]
/-- `$vbinop_` on float shapes, arguments. -/
def encFloatBinOp (p : FloatShape × VecFloatBinOp × V128 × V128) : List ArgV :=
  [.val (Vec.fshV p.1), .val (Vec.vFloatBinOpV p.2.1), .val (Vec.vecV p.2.2.1),
    .val (Vec.vecV p.2.2.2)]
/-- `$vternop_` on integer shapes, arguments. -/
def encIntTernOp (p : IntShape × VecIntTernOp × V128 × V128 × V128) : List ArgV :=
  [.val (Vec.ishV p.1), .val (Vec.vIntTernOpV p.2.1), .val (Vec.vecV p.2.2.1),
    .val (Vec.vecV p.2.2.2.1), .val (Vec.vecV p.2.2.2.2)]
/-- `$vternop_` on float shapes, arguments. -/
def encFloatTernOp (p : FloatShape × VecFloatTernOp × V128 × V128 × V128) : List ArgV :=
  [.val (Vec.fshV p.1), .val (Vec.vFloatTernOpV p.2.1), .val (Vec.vecV p.2.2.1),
    .val (Vec.vecV p.2.2.2.1), .val (Vec.vecV p.2.2.2.2)]
/-- `$vrelop_` on integer shapes, arguments. -/
def encIntRelOp (p : IntShape × IntRelOp × V128 × V128) : List ArgV :=
  [.val (Vec.ishV p.1), .val (Vec.vIntRelOpV p.2.1), .val (Vec.vecV p.2.2.1),
    .val (Vec.vecV p.2.2.2)]
/-- `$vrelop_` on float shapes, arguments. -/
def encFloatRelOp (p : FloatShape × FloatRelOp × V128 × V128) : List ArgV :=
  [.val (Vec.fshV p.1), .val (Vec.vFloatRelOpV p.2.1), .val (Vec.vecV p.2.2.1),
    .val (Vec.vecV p.2.2.2)]
/-- `$vshiftop_`, arguments. -/
def encShiftOp (p : IntShape × VecShiftOp × V128 × BitVec 32) : List ArgV :=
  [.val (Vec.ishapeV p.1), .val (Vec.vShiftOpV p.2.1), .val (Vec.vecV p.2.2.1),
    .val (Vec.i32NV p.2.2.2)]
/-- `$vbitmaskop_`, arguments. -/
def encBitmask (p : IntShape × V128) : List ArgV := [.val (Vec.ishapeV p.1), .val (Vec.vecV p.2)]
/-- `$vswizzlop_`, arguments. -/
def encSwizzle (p : VecSwizzleOp × V128 × V128) : List ArgV :=
  [.val Vec.bshapeV, .val (Vec.vSwizzleOpV p.1), .val (Vec.vecV p.2.1), .val (Vec.vecV p.2.2)]
/-- `$vshufflop_`, arguments. -/
def encShuffle (p : List LaneIdx × V128 × V128) : List ArgV :=
  [.val Vec.bshapeV, .val (.list (p.1.map Vec.laneIdxV)), .val (Vec.vecV p.2.1),
    .val (Vec.vecV p.2.2)]
/-- `$vextunop__`, arguments. -/
def encExtUnOp (p : IntShape × IntShape × VecExtUnOp × V128) : List ArgV :=
  [.val (Vec.ishapeV p.1), .val (Vec.ishapeV p.2.1), .val (Vec.vExtUnOpV p.2.2.1),
    .val (Vec.vecV p.2.2.2)]
/-- `$vextbinop__`, arguments. -/
def encExtBinOp (p : IntShape × IntShape × VecExtBinOp × V128 × V128) : List ArgV :=
  [.val (Vec.ishapeV p.1), .val (Vec.ishapeV p.2.1), .val (Vec.vExtBinOpV p.2.2.1),
    .val (Vec.vecV p.2.2.2.1), .val (Vec.vecV p.2.2.2.2)]
/-- `$vextternop__`, arguments. -/
def encExtTernOp (p : IntShape × IntShape × VecExtTernOp × V128 × V128 × V128) : List ArgV :=
  [.val (Vec.ishapeV p.1), .val (Vec.ishapeV p.2.1), .val (Vec.vExtTernOpV p.2.2.1),
    .val (Vec.vecV p.2.2.2.1), .val (Vec.vecV p.2.2.2.2.1), .val (Vec.vecV p.2.2.2.2.2)]
/-- `$vnarrowop__`, arguments. -/
def encNarrow (p : IntShape × IntShape × Signedness × V128 × V128) : List ArgV :=
  [.val (Vec.ishV p.1), .val (Vec.ishV p.2.1), .val (Vec.sxV p.2.2.1), .val (Vec.vecV p.2.2.2.1),
    .val (Vec.vecV p.2.2.2.2)]
/-- `$vcvtop__`, arguments. -/
def encConvert (p : Shape × Shape × VecConvertOp × V128) : List ArgV :=
  [.val (Vec.shapeV p.1), .val (Vec.shapeV p.2.1), .val (Vec.vConvertOpV p.2.2.1),
    .val (Vec.vecV p.2.2.2)]

/-- `$vswizzlop_`'s result. -/
def swizzleOp (P : Profile) : VecSwizzleOp → V128 → V128 → V128
  | .swizzle, a, b => vecSwizzle a b
  | .relaxedSwizzle, a, b => vecRelaxedSwizzle P a b

/-- **The lane-wise vector operators**, at the images of their arguments (see above). -/
noncomputable def vecOpCall (P : Profile) (x : IL.Id) (ws : List ArgV) : Option Value :=
  match x with
  | "vunop_" =>
    ((decodeArgs encIntUnOp ws).map fun p => .list [Vec.vecV (vecIntUnOp p.1 p.2.1 p.2.2)]) <|>
    ((decodeArgs encFloatUnOp ws).map fun p =>
      .list (vecsOf (VecFloatUnOpRel P p.1 p.2.1 p.2.2)))
  | "vbinop_" =>
    ((decodeArgs encIntBinOp ws).map fun p =>
      .list [Vec.vecV (vecIntBinOp P p.1 p.2.1 p.2.2.1 p.2.2.2)]) <|>
    ((decodeArgs encFloatBinOp ws).map fun p =>
      .list (vecsOf (VecFloatBinOpRel P p.1 p.2.1 p.2.2.1 p.2.2.2)))
  | "vternop_" =>
    ((decodeArgs encIntTernOp ws).map fun p =>
      .list [Vec.vecV (vecIntTernOp P p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)]) <|>
    ((decodeArgs encFloatTernOp ws).map fun p =>
      .list (vecsOf (VecFloatTernOpRel P p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)))
  | "vrelop_" =>
    ((decodeArgs encIntRelOp ws).map fun p =>
      Vec.vecV (vecIntRelOp p.1 p.2.1 p.2.2.1 p.2.2.2)) <|>
    ((decodeArgs encFloatRelOp ws).map fun p =>
      Vec.vecV (vecFloatRelOp p.1 p.2.1 p.2.2.1 p.2.2.2))
  | "vshiftop_" =>
    (decodeArgs encShiftOp ws).map fun p => Vec.vecV (vecShiftOp p.1 p.2.1 p.2.2.1 p.2.2.2)
  | "vbitmaskop_" => (decodeArgs encBitmask ws).map fun p => Vec.i32NV (vecBitmask p.1 p.2)
  | "vswizzlop_" =>
    (decodeArgs encSwizzle ws).map fun p => Vec.vecV (swizzleOp P p.1 p.2.1 p.2.2)
  | "vshufflop_" =>
    open Classical in
    (decodeArgs encShuffle ws).bind fun p =>
      if ∀ j ∈ p.1, j.val < 32 then some (Vec.vecV (vecShuffle p.1 p.2.1 p.2.2)) else none
  | "vextunop__" =>
    (decodeArgs encExtUnOp ws).bind fun p => someVec (VecExtUnOpRel p.1 p.2.1 p.2.2.1 p.2.2.2)
  | "vextbinop__" =>
    (decodeArgs encExtBinOp ws).bind fun p =>
      someVec (VecExtBinOpRel P p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
  | "vextternop__" =>
    (decodeArgs encExtTernOp ws).bind fun p =>
      someVec (VecExtTernOpRel P p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2)
  | "vnarrowop__" =>
    (decodeArgs encNarrow ws).bind fun p =>
      someVec (VecNarrowRel p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
  | "vcvtop__" =>
    (decodeArgs encConvert ws).bind fun p => someVec (VecConvertRel P p.1 p.2.1 p.2.2.1 p.2.2.2)
  | _ => none

end Silmaril.Wasm.SpecTec.Sim.Round5.Simd
