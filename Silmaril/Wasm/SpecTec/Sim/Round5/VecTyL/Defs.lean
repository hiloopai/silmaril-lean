module

public import Silmaril.Wasm.SpecTec.Sim.FloatSimd.Defs

/-!
# SpecTec ↔ Core 3.0, round 5, track simdty: family V's vector typing, restated

Family V's `Vec.VecTyping` is false in every `simEnv B` (`Round5.SimdTy.not_vecTyping`): its
field `lanes` asks **every** list of values, `[true]` included, to be a list of lanes. Its one
use (`Vec.fwd_vecAllTrue`) needs this only of the list `$lanes_` returns.

`VecTypingL` is `Vec.VecTyping` with `lanes` restricted to the lists `$lanes_(Jnn X M, v)`
returns; every other field is verbatim. `ofVecTyping` shows it asks no more than `VecTyping`.
Family V's forward lemmas take `VecTypingL` (they used no other field of `lanes`), so the
forward vector steps follow from `VecTypingL` and `VecAgree`. This header imports only family V's
definitions so that family V's proofs can use it.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.SimdTy

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Vec

/-- **Family V's `VecTyping`, with `lanes` restricted to what `$lanes_` returns.** -/
structure VecTypingL (env : Env) : Prop where
  /-- Every 128-bit pattern is a `vec_(V128)`. -/
  vec : ∀ a : V128, TypedV env vecT (vecV a)
  /-- Every 32-bit pattern is a `num_(I32)`. -/
  i32 : ∀ a : BitVec 32, TypedV env i32T (i32NV a)
  /-- The encoded `vvunop`s. -/
  vvunop : ∀ op, TypedV env (.varT "vvunop" []) (vvunopV op)
  /-- The encoded `vvbinop`s. -/
  vvbinop : ∀ op, TypedV env (.varT "vvbinop" []) (vvbinopV op)
  /-- The encoded `vvternop`s. -/
  vvternop : ∀ op, TypedV env (.varT "vvternop" []) (vvternopV op)
  /-- Both signednesses are `sx`s. -/
  sx : ∀ s : Signedness, TypedV env (.varT "sx" []) (sxV s)
  /-- Every encoded shape is a `shape`. -/
  shape : ∀ s : Shape, TypedV env shapeT (shapeV s)
  /-- Every encoded integer shape is an `ishape`. -/
  ishape : ∀ s : IntShape, TypedV env ishapeT (ishapeV s)
  /-- `I8 X 16` is a `bshape`. -/
  bshape : TypedV env bshapeT bshapeV
  /-- A typed `VUNOP` has an operator of type `vunop_(sh)` (integer shapes). -/
  intUnOp : ∀ s op, InstrTyped env (.vecIntUnOp s op) →
    TypedDep env "sh" (ishV s) (opT "vunop_" "sh") (vIntUnOpV op)
  /-- The same, float shapes. -/
  floatUnOp : ∀ s op, InstrTyped env (.vecFloatUnOp s op) →
    TypedDep env "sh" (fshV s) (opT "vunop_" "sh") (vFloatUnOpV op)
  /-- A typed `VBINOP` (integer shapes). -/
  intBinOp : ∀ s op, InstrTyped env (.vecIntBinOp s op) →
    TypedDep env "sh" (ishV s) (opT "vbinop_" "sh") (vIntBinOpV op)
  /-- A typed `VBINOP` (float shapes). -/
  floatBinOp : ∀ s op, InstrTyped env (.vecFloatBinOp s op) →
    TypedDep env "sh" (fshV s) (opT "vbinop_" "sh") (vFloatBinOpV op)
  /-- A typed `VTERNOP` (integer shapes). -/
  intTernOp : ∀ s op, InstrTyped env (.vecIntTernOp s op) →
    TypedDep env "sh" (ishV s) (opT "vternop_" "sh") (vIntTernOpV op)
  /-- A typed `VTERNOP` (float shapes). -/
  floatTernOp : ∀ s op, InstrTyped env (.vecFloatTernOp s op) →
    TypedDep env "sh" (fshV s) (opT "vternop_" "sh") (vFloatTernOpV op)
  /-- A typed `VRELOP` (integer shapes). -/
  intRelOp : ∀ s op, InstrTyped env (.vecIntRelOp s op) →
    TypedDep env "sh" (ishV s) (opT "vrelop_" "sh") (vIntRelOpV op)
  /-- A typed `VRELOP` (float shapes). -/
  floatRelOp : ∀ s op, InstrTyped env (.vecFloatRelOp s op) →
    TypedDep env "sh" (fshV s) (opT "vrelop_" "sh") (vFloatRelOpV op)
  /-- A typed `VSHIFTOP`. -/
  shiftOp : ∀ s op, InstrTyped env (.vecShiftOp s op) →
    TypedDep env "sh" (ishapeV s) (opT "vshiftop_" "sh") (vShiftOpV op)
  /-- A typed `VSWIZZLOP`. -/
  swizzle : ∀ op, InstrTyped env (.vecSwizzle op) →
    TypedDep env "sh" bshapeV (opT "vswizzlop_" "sh") (vSwizzleOpV op)
  /-- A typed `VSHUFFLE` has a `laneidx*` operand. -/
  shuffle : ∀ ls, InstrTyped env (.vecShuffle ls) →
    TypedV env laneidxsT (.list (ls.map laneIdxV))
  /-- A typed `VEXTUNOP`. -/
  extUnOp : ∀ s t op, InstrTyped env (.vecExtUnOp s t op) →
    TypedDep2 env "sh_1" (ishapeV s) "sh_2" (ishapeV t) (opT2 "vextunop__") (vExtUnOpV op)
  /-- A typed `VEXTBINOP`. -/
  extBinOp : ∀ s t op, InstrTyped env (.vecExtBinOp s t op) →
    TypedDep2 env "sh_1" (ishapeV s) "sh_2" (ishapeV t) (opT2 "vextbinop__") (vExtBinOpV op)
  /-- A typed `VEXTTERNOP`. -/
  extTernOp : ∀ s t op, InstrTyped env (.vecExtTernOp s t op) →
    TypedDep2 env "sh_1" (ishapeV s) "sh_2" (ishapeV t) (opT2 "vextternop__") (vExtTernOpV op)
  /-- Every lane count of a shape is an `M` (`dim`). -/
  dim : ∀ s : Shape, TypedV env (.varT "M" []) (pctV s.lanes)
  /-- Every lane index is a `laneidx`. -/
  laneidx : ∀ i : LaneIdx, TypedV env (.varT "laneidx" []) (laneIdxV i)
  /-- `I8` and `I16` are `packtype`s. -/
  packtype : ∀ s : IntShape, s.laneWidth < 32 → TypedV env (.varT "packtype" []) (intLaneV s)
  /-- Every lane type is an `Lnn`. -/
  lnn : ∀ s : Shape, TypedV env (.varT "Lnn" []) (laneTypeV s)
  /-- A numeral of a shape's unpacked type is a `num_($lunpack(Lnn))`. -/
  numLunpack : ∀ (s : Shape) (x : BitVec s.unpacked.width), TypedDep env "Lnn" (laneTypeV s)
    (.varT "num_" [.expA (.callE "lunpack" [.expA (.varE "Lnn")])])
    (numV ⟨s.unpacked, x⟩)
  /-- Every integer lane type is a `Jnn`. -/
  jnn : ∀ s : IntShape, TypedV env (.varT "Jnn" []) (intLaneV s)
  /-- **The lanes `$lanes_` gives** for an integer shape have the type `vtestop` quantifies them
  at, `lane_($lanetype(Jnn X M))*` (family V's `VecTyping.lanes` asks this of every list). -/
  lanes : ∀ (s : IntShape) (a : V128) (ls : List Value),
    Applies env "lanes_" [.val (ishV s), .val (vecV a)] (.list ls) →
    TypedDep2 env "Jnn" (intLaneV s) "M" (pctV s.lanes)
      (.iterT (.varT "lane_" [.expA (.callE "lanetype" [.expA (.caseE "%X%" (.tupE
        [.subE (.varE "Jnn") (.varT "Jnn" []) (.varT "lanetype" []), .varE "M"]))])]) .list)
      (.list ls)
  /-- A typed `VEXTRACT_LANE` has a signedness exactly when its lanes are packed (the IL's
  `sx? = eps <=> lanetype ∈ {I32, I64, F32, F64}`). -/
  extractSx : ∀ sh sx i, InstrTyped env (.vecExtractLane sh sx i) → (sx = none ↔ 32 ≤ sh.laneWidth)
  /-- A typed `VCVTOP`. -/
  convert : ∀ s t op, InstrTyped env (.vecConvert s t op) →
    TypedDep2 env "sh_1" (shapeV s) "sh_2" (shapeV t) (opT2 "vcvtop__") (vConvertOpV op)

/-- `VecTypingL` asks no more than family V's `VecTyping`. -/
theorem ofVecTyping {env : Env} (Ty : Vec.VecTyping env) : VecTypingL env where
  vec := Ty.vec
  i32 := Ty.i32
  vvunop := Ty.vvunop
  vvbinop := Ty.vvbinop
  vvternop := Ty.vvternop
  sx := Ty.sx
  shape := Ty.shape
  ishape := Ty.ishape
  bshape := Ty.bshape
  intUnOp := Ty.intUnOp
  floatUnOp := Ty.floatUnOp
  intBinOp := Ty.intBinOp
  floatBinOp := Ty.floatBinOp
  intTernOp := Ty.intTernOp
  floatTernOp := Ty.floatTernOp
  intRelOp := Ty.intRelOp
  floatRelOp := Ty.floatRelOp
  shiftOp := Ty.shiftOp
  swizzle := Ty.swizzle
  shuffle := Ty.shuffle
  extUnOp := Ty.extUnOp
  extBinOp := Ty.extBinOp
  extTernOp := Ty.extTernOp
  dim := Ty.dim
  laneidx := Ty.laneidx
  packtype := Ty.packtype
  lnn := Ty.lnn
  numLunpack := Ty.numLunpack
  jnn := Ty.jnn
  lanes s _ ls _ := Ty.lanes s ls
  extractSx := Ty.extractSx
  convert := Ty.convert

end Silmaril.Wasm.SpecTec.Sim.Round5.SimdTy
