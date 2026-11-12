module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Int3.Defs

/-!
# SpecTec ↔ Core 3.0, round 5, track convert: definitions

Pass 3 left `Round5.Int3.Open4.vecOps` (`Simd.VecAgreeOps`) false under the spec NaN profile, at
its `convert` field: `$vcvtop__` is a function, while Core's `VecConvertRel` lets `promote_low` of a
canonical NaN lane give the canonical NaN of either sign (`Round5.Simd.not_convert_spec`). Track
simd split it into `Simd.VecAgreeLanes` (proved, `vecAgreeLanes_builtins`) and the restated
`Simd.VecConvertR` (sound and total). Track convert proves `VecConvertR` at the concrete builtins
(`Round5.Convert.vecConvertR_builtins`) and restates what depends on it:

* `VecAgreeNC env P`: family V's `Vec.VecAgree` without its `convert` field, field for field;
* `VectorFwdR hn P host`: `Round5.Int.VectorFwd` up to Core's choice. Every Core vector step from
  bounded code is matched by a SpecTec step to the image of *a* Core vector step from the same code;
  that step is the given one whenever Core's vector step from that code is unique. Only
  `vcvtop` needs the latitude;
* `Open5 hn P host`: `Round5.Int3.Open4` with `vecOps` replaced by `Simd.VecAgreeLanes` and
  `Simd.VecConvertR`. Both are proved at the concrete builtins, so only `simd` and `refOk` are
  left.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Convert

open Silmaril.SpecTec
open Silmaril.SpecTec.IL hiding Id Prod
open Silmaril.SpecTec.Sem
open Silmaril.SpecTec.Equiv.ExecNumeric (Applies)
open Silmaril.SpecTec.Equiv.Execution (pctV caseNilV)
open Silmaril.Wasm
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Execution.Core
open Vec
open Round4Int (BI)

variable {H : Type}

/-- **Family V's `Vec.VecAgree` without `convert`**, field for field (the fields and their
documentation are copied from `FloatSimd/Defs.lean`). -/
structure VecAgreeNC (env : Env) (P : Profile) : Prop where
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

/-- **`Round5.Int.VectorFwd` up to Core's choice of result.** From bounded code with a non-bitwise
SIMD instruction, a Core vector step to `is'` is matched by a SpecTec step to the image of a Core
vector step to some `is''`, and `is'' = is'` whenever every Core vector step from `is` goes to
`is'`. -/
def VectorFwdR (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop :=
  ∀ (s : Store H) (f : Frame) (is is' : List Admin), VectorStep P is is' →
    (∃ i, Admin.plain i ∈ is ∧ R4Fwd.VecArith i = true) → Round4.Bounded ⟨s, f, is⟩ →
    ∃ is'', VectorStep P is is'' ∧ ((∀ is₃, VectorStep P is is₃ → is₃ = is') → is'' = is') ∧
      FwdP (simEnv (BI P hn host)) hn ⟨s, f, is⟩ ⟨s, f, is''⟩

/-- **`Round5.Int.VectorFwd` on the vector steps Core takes deterministically.** -/
def VectorFwdDet (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop :=
  ∀ (s : Store H) (f : Frame) (is is' : List Admin), VectorStep P is is' →
    (∀ is₃, VectorStep P is is₃ → is₃ = is') →
    (∃ i, Admin.plain i ∈ is ∧ R4Fwd.VecArith i = true) → Round4.Bounded ⟨s, f, is⟩ →
    FwdP (simEnv (BI P hn host)) hn ⟨s, f, is⟩ ⟨s, f, is'⟩

/-- **`Round5.Int3.Open4` with `vecOps` restated**: `Simd.VecAgreeLanes` and `Simd.VecConvertR`
for `Simd.VecAgreeOps`. Both new fields hold at the concrete builtins
(`Round5.Simd.vecAgreeLanes_builtins`, `Round5.Convert.vecConvertR_builtins`). -/
structure Open5 (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- Typing of the SIMD instructions other than `v128.const`. False for every
  builtins: `Round5.SimdTy.not_simdTyping`. -/
  simd : Pos.SimdTyping (BI P hn host)
  /-- SpecTec's `Ref_ok` is Core's `RefOk` on typed stores and bounded types. -/
  refOk : Fwd.RefOkB (simEnv (BI P hn host))
  /-- The vector operators other than `$vcvtop__` agree with Core. -/
  vecLanes : Simd.VecAgreeLanes (simEnv (BI P hn host)) P
  /-- `$vcvtop__` is sound and total for Core's `VecConvertRel`. -/
  vecConvert : Simd.VecConvertR (simEnv (BI P hn host)) P

end Silmaril.Wasm.SpecTec.Sim.Round5.Convert
