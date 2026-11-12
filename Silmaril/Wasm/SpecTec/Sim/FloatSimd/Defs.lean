module

public import Silmaril.Wasm.SpecTec.Sim.Defs

/-!
# SpecTec ↔ Core 3.0, family V (vector/relaxed): typing and agreement interfaces

The per-rule constructions (`Silmaril/Proofs/Wasm/SpecTec/Sim/FloatSimd/Rules.lean`) build the vector
rules 54–78 of `Step_pure` for arbitrary IL values; the Core-level lemmas
(`…/FloatSimd/Forward.lean`) instantiate them at the images of Core's `VectorStep`. Two things are
assumed there, each as a structure over the environment, so that what is proved and what is
assumed stay separate:

* `VecTyping env`: the values a vector rule quantifies over have their IL types. The closed facts
  (`vec_(V128)` holds every 128-bit pattern, the encoded shapes are `shape`s) are unconditional;
  the operator facts (`vunop : vunop_(sh)`) are conditioned on the instruction being typed, as in
  the base's `TypingFacts`. Family E is expected to discharge these.
* `VecAgree env P`: SpecTec's vector operators, as `Applies` (clauses, or the builtin fallback),
  denote what Core's `VectorStep` computes under the profile `P`. Every field is stated so that it
  serves both directions: a deterministic operator gives one value (`Applies` is functional,
  `Equiv.ExecNumeric.applies_unique`); a relational one is an `↔` over the possible results.
  Nothing in this family proves these: relating `3.2-numerics.vector.spectec` to
  `Silmaril/Wasm/Numerics/Vector*.lean` is the open agreement layer.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Vec

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics

/-! ## Types and scopes -/

/-- `w` has type `t` in every term-only scope that binds `x` to `v`: the typing of a quantifier
whose type mentions an earlier quantifier (`vunop : vunop_(sh)`). -/
def TypedDep (env : Env) (x : IL.Id) (v : Value) (t : Typ) (w : Value) : Prop :=
  ∀ ρ : VarEnv, ValsOnly ρ → ρ.findVal? x = some v → HasTyp env ρ t w

/-- The same, for a type that mentions two earlier quantifiers (`vextunop__(sh_1, sh_2)`). -/
def TypedDep2 (env : Env) (x : IL.Id) (v : Value) (y : IL.Id) (u : Value) (t : Typ)
    (w : Value) : Prop :=
  ∀ ρ : VarEnv, ValsOnly ρ → ρ.findVal? x = some v → ρ.findVal? y = some u → HasTyp env ρ t w

/-- The IL type `vec_(V128)`. -/
abbrev vecT : Typ := .varT "vec_" [.expA (.caseE "V128" (.tupE []))]
/-- The IL type `num_(I32)`. -/
abbrev i32T : Typ := .varT "num_" [.expA (.caseE "I32" (.tupE []))]
/-- The IL type `shape`. -/
abbrev shapeT : Typ := .varT "shape" []
/-- The IL type `ishape`. -/
abbrev ishapeT : Typ := .varT "ishape" []
/-- The IL type `bshape`. -/
abbrev bshapeT : Typ := .varT "bshape" []
/-- The IL type `laneidx*`. -/
abbrev laneidxsT : Typ := .iterT (.varT "laneidx" []) .list

/-- A 128-bit pattern as a value of `vec_(V128)`. -/
abbrev vecV (a : V128) : Value := pctV a.toNat

/-- A 32-bit pattern as a value of `num_(I32)`. -/
abbrev i32NV (a : BitVec 32) : Value := pctV a.toNat

/-- A dependent operator type `x_(sh)` over the quantifier `sh`. -/
abbrev opT (x : IL.Id) (sh : IL.Id) : Typ := .varT x [.expA (.varE sh)]

/-- A dependent operator type `x__(sh_1, sh_2)`. -/
abbrev opT2 (x : IL.Id) : Typ := .varT x [.expA (.varE "sh_1"), .expA (.varE "sh_2")]

/-- A single instruction is typed as an `instr*`. -/
abbrev InstrTyped (env : Env) (i : Silmaril.Wasm.Instr) : Prop :=
  TypedV env instrsT (.list [instrToV i])

/-! ## Typing -/

/-- What the vector rules need about the IL typing of the encoded values. -/
structure VecTyping (env : Env) : Prop where
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
  /-- The lanes `$lanes_` gives for an integer shape have the type `vtestop` quantifies them at,
  `lane_($lanetype(Jnn X M))*`. -/
  lanes : ∀ (s : IntShape) (ls : List Value), TypedDep2 env "Jnn" (intLaneV s) "M" (pctV s.lanes)
    (.iterT (.varT "lane_" [.expA (.callE "lanetype" [.expA (.caseE "%X%" (.tupE
      [.subE (.varE "Jnn") (.varT "Jnn" []) (.varT "lanetype" []), .varE "M"]))])]) .list)
    (.list ls)
  /-- A typed `VEXTRACT_LANE` has a signedness exactly when its lanes are packed (the IL's
  `sx? = eps <=> lanetype ∈ {I32, I64, F32, F64}`). -/
  extractSx : ∀ sh sx i, InstrTyped env (.vecExtractLane sh sx i) → (sx = none ↔ 32 ≤ sh.laneWidth)
  /-- A typed `VCVTOP`. -/
  convert : ∀ s t op, InstrTyped env (.vecConvert s t op) →
    TypedDep2 env "sh_1" (shapeV s) "sh_2" (shapeV t) (opT2 "vcvtop__") (vConvertOpV op)

/-! ## Agreement of the operators -/

/-- What SpecTec's vector operators denote, in terms of Core's (`Silmaril.Wasm.Numerics`) under the
profile `P`. Deterministic operators are stated as a single `Applies` (functional); relational ones
as an `↔` over results, so that one field serves the forward and the backward direction, and the
`-trap` rules (empty result list) are covered by the same `↔`. -/
structure VecAgree (env : Env) (P : Profile) : Prop where
  /-- `$vvunop_(V128, op, c)`. -/
  vvunop : ∀ op a, Applies env "vvunop_" [.val vecTypeV, .val (vvunopV op), .val (vecV a)]
    (.list [vecV (vvunop op a)])
  /-- `$vvbinop_(V128, op, c_1, c_2)`. -/
  vvbinop : ∀ op a b, Applies env "vvbinop_"
    [.val vecTypeV, .val (vvbinopV op), .val (vecV a), .val (vecV b)]
    (.list [vecV (vvbinop op a b)])
  /-- `$vvternop_(V128, op, c_1, c_2, c_3)`. -/
  vvternop : ∀ op a b c, Applies env "vvternop_"
    [.val vecTypeV, .val (vvternopV op), .val (vecV a), .val (vecV b), .val (vecV c)]
    (.list [vecV (vvternop op a b c)])
  /-- `$vsize(V128)` and `$inez_`, the premise of `vvtestop`. -/
  vvtestop : ∀ op a, ∃ n, Applies env "vsize" [.val vecTypeV] n ∧
    Applies env "inez_" [.val n, .val (vecV a)] (i32NV (vvtestop op a))
  /-- `$vunop_` on integer shapes. -/
  intUnOp : ∀ s op a, Applies env "vunop_" [.val (ishV s), .val (vIntUnOpV op), .val (vecV a)]
    (.list [vecV (vecIntUnOp s op a)])
  /-- `$vunop_` on float shapes: the result list is the set `VecFloatUnOpRel` allows. -/
  floatUnOp : ∀ s op a, ∃ L, Applies env "vunop_"
    [.val (fshV s), .val (vFloatUnOpV op), .val (vecV a)] (.list L) ∧
    ∀ c, c ∈ L ↔ ∃ r, VecFloatUnOpRel P s op a r ∧ c = vecV r
  /-- `$vbinop_` on integer shapes. -/
  intBinOp : ∀ s op a b, Applies env "vbinop_"
    [.val (ishV s), .val (vIntBinOpV op), .val (vecV a), .val (vecV b)]
    (.list [vecV (vecIntBinOp P s op a b)])
  /-- `$vbinop_` on float shapes. -/
  floatBinOp : ∀ s op a b, ∃ L, Applies env "vbinop_"
    [.val (fshV s), .val (vFloatBinOpV op), .val (vecV a), .val (vecV b)] (.list L) ∧
    ∀ c, c ∈ L ↔ ∃ r, VecFloatBinOpRel P s op a b r ∧ c = vecV r
  /-- `$vternop_` on integer shapes. -/
  intTernOp : ∀ s op a b c, Applies env "vternop_"
    [.val (ishV s), .val (vIntTernOpV op), .val (vecV a), .val (vecV b), .val (vecV c)]
    (.list [vecV (vecIntTernOp P s op a b c)])
  /-- `$vternop_` on float shapes. -/
  floatTernOp : ∀ s op a b c, ∃ L, Applies env "vternop_"
    [.val (fshV s), .val (vFloatTernOpV op), .val (vecV a), .val (vecV b), .val (vecV c)]
    (.list L) ∧ ∀ d, d ∈ L ↔ ∃ r, VecFloatTernOpRel P s op a b c r ∧ d = vecV r
  /-- `$vrelop_` on integer shapes. -/
  intRelOp : ∀ s op a b, Applies env "vrelop_"
    [.val (ishV s), .val (vIntRelOpV op), .val (vecV a), .val (vecV b)]
    (vecV (vecIntRelOp s op a b))
  /-- `$vrelop_` on float shapes. -/
  floatRelOp : ∀ s op a b, Applies env "vrelop_"
    [.val (fshV s), .val (vFloatRelOpV op), .val (vecV a), .val (vecV b)]
    (vecV (vecFloatRelOp s op a b))
  /-- `$vshiftop_`. -/
  shiftOp : ∀ s op a n, Applies env "vshiftop_"
    [.val (ishapeV s), .val (vShiftOpV op), .val (vecV a), .val (i32NV n)]
    (vecV (vecShiftOp s op a n))
  /-- `$vbitmaskop_`. -/
  bitmask : ∀ s a, Applies env "vbitmaskop_" [.val (ishapeV s), .val (vecV a)]
    (i32NV (vecBitmask s a))
  /-- `$vswizzlop_`, `SWIZZLE`. -/
  swizzle : ∀ a b, Applies env "vswizzlop_"
    [.val bshapeV, .val (vSwizzleOpV .swizzle), .val (vecV a), .val (vecV b)]
    (vecV (vecSwizzle a b))
  /-- `$vswizzlop_`, `RELAXED_SWIZZLE`. -/
  relaxedSwizzle : ∀ a b, Applies env "vswizzlop_"
    [.val bshapeV, .val (vSwizzleOpV .relaxedSwizzle), .val (vecV a), .val (vecV b)]
    (vecV (vecRelaxedSwizzle P a b))
  /-- `$vshufflop_`: defined exactly on in-range lane indices. -/
  shuffle : ∀ idx a b c, Applies env "vshufflop_"
    [.val bshapeV, .val (.list (idx.map laneIdxV)), .val (vecV a), .val (vecV b)] c ↔
    (∀ j ∈ idx, j.val < 32) ∧ c = vecV (vecShuffle idx a b)
  /-- `$vextunop__`. -/
  extUnOp : ∀ s t op a c, Applies env "vextunop__"
    [.val (ishapeV s), .val (ishapeV t), .val (vExtUnOpV op), .val (vecV a)] c ↔
    ∃ r, VecExtUnOpRel s t op a r ∧ c = vecV r
  /-- `$vextbinop__`. -/
  extBinOp : ∀ s t op a b c, Applies env "vextbinop__"
    [.val (ishapeV s), .val (ishapeV t), .val (vExtBinOpV op), .val (vecV a), .val (vecV b)] c ↔
    ∃ r, VecExtBinOpRel P s t op a b r ∧ c = vecV r
  /-- `$vextternop__`. -/
  extTernOp : ∀ s t op a b d c, Applies env "vextternop__"
    [.val (ishapeV s), .val (ishapeV t), .val (vExtTernOpV op), .val (vecV a), .val (vecV b),
      .val (vecV d)] c ↔
    ∃ r, VecExtTernOpRel P s t op a b d r ∧ c = vecV r
  /-- `$vnarrowop__`. -/
  narrow : ∀ s t sx a b c, Applies env "vnarrowop__"
    [.val (ishV s), .val (ishV t), .val (sxV sx), .val (vecV a), .val (vecV b)] c ↔
    ∃ r, VecNarrowRel s t sx a b r ∧ c = vecV r
  /-- `$lanes_` at an unpacked lane: the `k`-th lane is Core's extracted lane, as a numeral of the
  unpacked type (for float shapes an `fN` value). -/
  extractNum : ∀ (sh : Shape) (a : V128) (k : Nat), k < sh.lanes → 32 ≤ sh.laneWidth →
    ∃ ls, Applies env "lanes_" [.val (shapeV sh), .val (vecV a)] (.list ls) ∧
      ls[k]? = some (numV ⟨sh.unpacked, vecExtractLane sh none k a⟩)
  /-- `$extend__($psize(pt), 32, sx, $lanes_(pt X M, c)[k])` at a packed lane. -/
  extractPack : ∀ (sh : IntShape) (sx : Signedness) (a : V128) (k : Nat), k < sh.lanes →
    sh.laneWidth < 32 → ∃ ls l n, Applies env "lanes_" [.val (ishV sh), .val (vecV a)] (.list ls) ∧
      ls[k]? = some l ∧ Applies env "psize" [.val (intLaneV sh)] n ∧
      Applies env "extend__" [.val n, .val (.num (.natN 32)), .val (sxV sx), .val l]
        (numV ⟨(Shape.int sh).unpacked, vecExtractLane (.int sh) (some sx) k a⟩)
  /-- `vreplace_lane`'s premise: `$lunpack`, `$lanes_`, `$lpacknum_`, the list update and
  `$inv_lanes_` compose to Core's `vecReplaceLane`. -/
  replaceLane : ∀ (sh : Shape) (a : V128) (k : Nat) (x : BitVec sh.unpacked.width), k < sh.lanes →
    ∃ ls l u, Applies env "lunpack" [.val (laneTypeV sh)] (numTypeV sh.unpacked) ∧
      Applies env "lanes_" [.val (shapeV sh), .val (vecV a)] (.list ls) ∧
      Applies env "lpacknum_" [.val (laneTypeV sh), .val (numV ⟨sh.unpacked, x⟩)] l ∧
      (Value.list ls).setIdx k l = some u ∧
      Applies env "inv_lanes_" [.val (shapeV sh), .val u] (vecV (vecReplaceLane sh k a x))
  /-- `vsplat`'s premise: `$lunpack`, `$lpacknum_` and `$inv_lanes_` of `M` copies compose to
  Core's `vecSplat`. -/
  splat : ∀ (sh : Shape) (x : BitVec sh.unpacked.width), ∃ l,
    Applies env "lunpack" [.val (laneTypeV sh)] (numTypeV sh.unpacked) ∧
    Applies env "lpacknum_" [.val (laneTypeV sh), .val (numV ⟨sh.unpacked, x⟩)] l ∧
    Applies env "inv_lanes_" [.val (shapeV sh), .val (.list (List.replicate sh.lanes l))]
      (vecV (vecSplat sh x))
  /-- `vtestop`'s premises: the lanes, `$jsizenn`, `$inez_` per lane and `$prod` compose to
  Core's `vecAllTrue`. -/
  allTrue : ∀ (sh : IntShape) (a : V128), ∃ ls jsz bs,
    Applies env "lanes_" [.val (ishV sh), .val (vecV a)] (.list ls) ∧
    Applies env "jsizenn" [.val (intLaneV sh)] jsz ∧
    List.Forall₂ (fun l b => Applies env "inez_" [.val jsz, .val l] (pctV b)) ls bs ∧
    Applies env "prod" [.val (.list (bs.map fun b => .num (.natN b)))]
      (.num (.natN (vecAllTrue sh a).toNat))
  /-- `$vcvtop__`. -/
  convert : ∀ s t op a c, Applies env "vcvtop__"
    [.val (shapeV s), .val (shapeV t), .val (vConvertOpV op), .val (vecV a)] c ↔
    ∃ r, VecConvertRel P s t op a r ∧ c = vecV r

/-! ## Scalar floats and conversions

The float half of `NumericStep` (`floatUnOp`, `floatBinOp`, `floatRelOp`) and the conversions
(`convert`, `convertTrap`), through the generic scalar rules 46, 48, 51, 52, 53 of `Step_pure`. -/

/-- A scalar float `unop_(Fnn)`. -/
def fUnOpV : FloatUnOp → Value
  | .abs => caseNilV "ABS"
  | .neg => caseNilV "NEG"
  | .sqrt => caseNilV "SQRT"
  | .ceil => caseNilV "CEIL"
  | .floor => caseNilV "FLOOR"
  | .trunc => caseNilV "TRUNC"
  | .nearest => caseNilV "NEAREST"

/-- A scalar float `binop_(Fnn)`. -/
def fBinOpV : FloatBinOp → Value
  | .add => caseNilV "ADD"
  | .sub => caseNilV "SUB"
  | .mul => caseNilV "MUL"
  | .div => caseNilV "DIV"
  | .min => caseNilV "MIN"
  | .max => caseNilV "MAX"
  | .copysign => caseNilV "COPYSIGN"

/-- The IL type `numtype`. -/
abbrev numtypeT : Typ := .varT "numtype" []

/-- The IL type `num_(x)` over the quantifier `x`. -/
abbrev numT (x : IL.Id) : Typ := .varT "num_" [.expA (.varE x)]

/-- The IL type `cvtop__(nt_1, nt_2)`. -/
abbrev cvtopT : Typ := .varT "cvtop__" [.expA (.varE "nt_1"), .expA (.varE "nt_2")]

/-- What the scalar float and conversion rules need about the IL typing of encoded values. -/
structure FloatTyping (env : Env) : Prop where
  /-- Every number type is a `numtype`. -/
  numtype : ∀ t : NumType, TypedV env numtypeT (numTypeV t)
  /-- A numeral of type `t` is a `num_(t)`, whichever quantifier names `t`. For floats this is
  the check that the `fN` encoding (`floatV`, including `NAN` payloads) inhabits `fN(N)`. -/
  num : ∀ (x : IL.Id) (n : Silmaril.Wasm.Execution.Core.NumVal),
    TypedDep env x (numTypeV n.type) (numT x) (numV n)
  /-- Every 32-bit pattern is a `num_(I32)`. -/
  i32 : ∀ a : BitVec 32, TypedV env i32T (i32NV a)
  /-- Every float `unop_(Fnn)`. -/
  unop : ∀ t op, TypedDep env "nt" (numTypeV (.float t)) (opT "unop_" "nt") (fUnOpV op)
  /-- Every float `binop_(Fnn)`. -/
  binop : ∀ t op, TypedDep env "nt" (numTypeV (.float t)) (opT "binop_" "nt") (fBinOpV op)
  /-- Every float `relop_(Fnn)`. -/
  relop : ∀ t op, TypedDep env "nt" (numTypeV (.float t)) (opT "relop_" "nt") (vFloatRelOpV op)
  /-- The operator of a typed `CVTOP` has type `cvtop__(nt_1, nt_2)`. -/
  cvtop : ∀ op, InstrTyped env (.convert op) →
    TypedDep2 env "nt_1" (numTypeV op.source) "nt_2" (numTypeV op.target) cvtopT (cvtOpV op)

/-- What SpecTec's scalar float operators and conversions denote, in terms of Core's
(`Silmaril.Wasm.Numerics`, profile-aware) under `P`. The result lists of `$unop_`, `$binop_` and
`$cvtop__` are exactly the sets the profile allows; `$relop_` is a function. -/
structure FloatAgree (env : Env) (P : Profile) : Prop where
  /-- `$unop_(Fnn, op, c)`. -/
  unop : ∀ (t : FloatType) op (x : BitVec t.width), ∃ L, Applies env "unop_"
    [.val (numTypeV (.float t)), .val (fUnOpV op), .val (floatV t x)] (.list L) ∧
    ∀ c, c ∈ L ↔ ∃ z, floatUnOpP P t op x z ∧ c = floatV t z
  /-- `$binop_(Fnn, op, c_1, c_2)`. -/
  binop : ∀ (t : FloatType) op (x y : BitVec t.width), ∃ L, Applies env "binop_"
    [.val (numTypeV (.float t)), .val (fBinOpV op), .val (floatV t x), .val (floatV t y)]
    (.list L) ∧ ∀ c, c ∈ L ↔ ∃ z, floatBinOpP P t op x y z ∧ c = floatV t z
  /-- `$relop_(Fnn, op, c_1, c_2)`. -/
  relop : ∀ (t : FloatType) op (x y : BitVec t.width), Applies env "relop_"
    [.val (numTypeV (.float t)), .val (vFloatRelOpV op), .val (floatV t x), .val (floatV t y)]
    (i32NV (floatRelOp t op x y))
  /-- `$cvtop__(nt_1, nt_2, op, c)`: the results are the profile's, and the list is empty
  exactly when the conversion traps. -/
  cvtop : ∀ (op : ConvertOp) (x : BitVec op.source.width), ∃ L, Applies env "cvtop__"
    [.val (numTypeV op.source), .val (numTypeV op.target), .val (cvtOpV op),
      .val (numV ⟨op.source, x⟩)] (.list L) ∧
    (∀ c, c ∈ L ↔ ∃ z, convertP P op x (.ok z) ∧ c = numV ⟨op.target, z⟩) ∧
    (L = [] ↔ ∃ e, convertP P op x (.error e))


end Silmaril.Wasm.SpecTec.Sim.Vec
