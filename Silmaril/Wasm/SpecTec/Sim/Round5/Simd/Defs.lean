module

public import Silmaril.Wasm.SpecTec.Sim.Round5.Int.Defs

/-!
# SpecTec ↔ Core 3.0, round 5, track simd: definitions

Pass 1 left family V's `VecAgree` open at the concrete builtins, and it was false there:
`Prims.builtins` did not answer `$lanes_` (`Round5.Simd.not_vecAgree_of_lanes`), so pass 1's
`Round5.Int.Open` was unsatisfiable. Track simd extends `Prims.builtins` with `$lanes_` and
`$inv_lanes_` (`Round5/Lanes/Defs.lean`) and proves, at `BI P hn host`, the nine fields of
`VecAgree` that only read or write lanes or are bitwise (`vvunop`, `vvbinop`, `vvternop`,
`vvtestop`, `extractNum`, `extractPack`, `splat`, `replaceLane`, `allTrue`). This header names
what is left:

* `VecAgreeOps env P`: the other sixteen fields of `VecAgree`, verbatim: the lane-wise operators,
  whose SpecTec definitions (`3.2-numerics.vector.spectec`) now evaluate through `$lanes_` and
  the scalar operators;
* `PureOpenVtestop hn P host`: `Step_pure` 64 (`vtestop`) backward, the part of
  `BwdStep.PureOpenV` left after this track's proofs of 70–73;
* `OpenS hn P host`: `Round5.Int.Open` with `vecAgree` weakened to `VecAgreeOps` and `pureOpen`
  to `PureOpenVtestop` (`Round5.Simd.open_of_openS`).
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim.Round5.Simd

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

/-- **The fields of family V's `VecAgree` still open at the concrete builtins**, verbatim: the
lane-wise operators. -/
structure VecAgreeOps (env : Env) (P : Profile) : Prop where
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
  /-- `$vcvtop__`. -/
  convert : ∀ s t op a c, Applies env "vcvtop__"
    [.val (shapeV s), .val (shapeV t), .val (vConvertOpV op), .val (vecV a)] c ↔
    ∃ r, VecConvertRel P s t op a r ∧ c = vecV r

/-- **The part of `BwdStep.PureOpenV` still open**: `Step_pure` 64 (`vtestop`) backward. Track simd
proves 70–73 at the concrete builtins (`Round5.Simd.pureOpenV_of_vtestop`). -/
def PureOpenVtestop (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop :=
  ∀ (s : Store H) (f : Frame) (is : List Admin) (w : Value),
    Round4Read.ReadValid ⟨s, f, is⟩ → Typed (simEnv (BI P hn host)) hn ⟨s, f, is⟩ →
    Fires (simEnv (BI P hn host)) "Step_pure" 64 (.tuple [.list (adminsToV is), w]) →
    ∃ is' js, Bwd.CodeEq is' js ∧ w = .list (adminsToV js) ∧ Step P host ⟨s, f, is⟩ ⟨s, f, is'⟩

/-- **`Round5.Int.Open` with `vecAgree` weakened to `VecAgreeOps` and `pureOpen` to
`PureOpenVtestop`**: the parts of both this track proves at the concrete builtins are dropped. -/
structure OpenS (hn : H → String) (P : Profile) (host : HostSemantics H) : Prop where
  /-- Typing of the SIMD instructions other than `v128.const`. -/
  simd : Pos.SimdTyping (BI P hn host)
  /-- SpecTec's `Ref_ok` is Core's `RefOk` on typed stores and bounded types. -/
  refOk : Fwd.RefOkB (simEnv (BI P hn host))
  /-- The host respects the encoding (host `call_ref`, forward and backward). -/
  hostRespects : Prims.HostRespects hn host
  /-- The non-bitwise SIMD operators, forward. -/
  vector : Int.VectorFwd hn P host
  /-- `array.new_data` with `n > 0`, forward. -/
  newDataNum : Fwd.NewDataNumB (BI P hn host) hn
  /-- The lane-wise vector operators agree. -/
  vecOps : VecAgreeOps (simEnv (BI P hn host)) P
  /-- `Step_pure` 64 (`vtestop`), backward. -/
  vtestop : PureOpenVtestop hn P host
  /-- The remaining `Step_read` rules, backward. -/
  read : Int.ReadOpen hn P host

/-! ## Pass 3: the restated agreement

`VecAgreeOps.convert` is false under the spec NaN profile for every environment
(`Round5.Simd.not_convert_spec`): `$vcvtop__` is a function, Core's `VecConvertRel` a relation.
Pass 3 splits `VecAgreeOps` into the fields that do not mention `$vcvtop__`, `VecAgreeLanes`
(proved at the concrete builtins, `Round5.Simd.vecAgreeLanes_builtins`), and a restated
conversion field, `VecConvertR`: every value SpecTec's call denotes is one Core allows, and the call
denotes something wherever Core has a result. That is what the backward direction of the
`vcvtop` rule needs; the forward direction cannot hold for the relational conversions. -/

/-- **`VecAgreeOps` without `convert`**, field for field. -/
structure VecAgreeLanes (env : Env) (P : Profile) : Prop where
  intUnOp : ∀ s op a, Applies env "vunop_" [.val (ishV s), .val (vIntUnOpV op), .val (vecV a)]
    (.list [vecV (vecIntUnOp s op a)])
  floatUnOp : ∀ s op a, ∃ L, Applies env "vunop_"
    [.val (fshV s), .val (vFloatUnOpV op), .val (vecV a)] (.list L) ∧
    ∀ c, c ∈ L ↔ ∃ r, VecFloatUnOpRel P s op a r ∧ c = vecV r
  intBinOp : ∀ s op a b, Applies env "vbinop_"
    [.val (ishV s), .val (vIntBinOpV op), .val (vecV a), .val (vecV b)]
    (.list [vecV (vecIntBinOp P s op a b)])
  floatBinOp : ∀ s op a b, ∃ L, Applies env "vbinop_"
    [.val (fshV s), .val (vFloatBinOpV op), .val (vecV a), .val (vecV b)] (.list L) ∧
    ∀ c, c ∈ L ↔ ∃ r, VecFloatBinOpRel P s op a b r ∧ c = vecV r
  intTernOp : ∀ s op a b c, Applies env "vternop_"
    [.val (ishV s), .val (vIntTernOpV op), .val (vecV a), .val (vecV b), .val (vecV c)]
    (.list [vecV (vecIntTernOp P s op a b c)])
  floatTernOp : ∀ s op a b c, ∃ L, Applies env "vternop_"
    [.val (fshV s), .val (vFloatTernOpV op), .val (vecV a), .val (vecV b), .val (vecV c)]
    (.list L) ∧ ∀ d, d ∈ L ↔ ∃ r, VecFloatTernOpRel P s op a b c r ∧ d = vecV r
  intRelOp : ∀ s op a b, Applies env "vrelop_"
    [.val (ishV s), .val (vIntRelOpV op), .val (vecV a), .val (vecV b)]
    (vecV (vecIntRelOp s op a b))
  floatRelOp : ∀ s op a b, Applies env "vrelop_"
    [.val (fshV s), .val (vFloatRelOpV op), .val (vecV a), .val (vecV b)]
    (vecV (vecFloatRelOp s op a b))
  shiftOp : ∀ s op a n, Applies env "vshiftop_"
    [.val (ishapeV s), .val (vShiftOpV op), .val (vecV a), .val (i32NV n)]
    (vecV (vecShiftOp s op a n))
  bitmask : ∀ s a, Applies env "vbitmaskop_" [.val (ishapeV s), .val (vecV a)]
    (i32NV (vecBitmask s a))
  swizzle : ∀ a b, Applies env "vswizzlop_"
    [.val bshapeV, .val (vSwizzleOpV .swizzle), .val (vecV a), .val (vecV b)]
    (vecV (vecSwizzle a b))
  relaxedSwizzle : ∀ a b, Applies env "vswizzlop_"
    [.val bshapeV, .val (vSwizzleOpV .relaxedSwizzle), .val (vecV a), .val (vecV b)]
    (vecV (vecRelaxedSwizzle P a b))
  shuffle : ∀ idx a b c, Applies env "vshufflop_"
    [.val bshapeV, .val (.list (idx.map laneIdxV)), .val (vecV a), .val (vecV b)] c ↔
    (∀ j ∈ idx, j.val < 32) ∧ c = vecV (vecShuffle idx a b)
  extUnOp : ∀ s t op a c, Applies env "vextunop__"
    [.val (ishapeV s), .val (ishapeV t), .val (vExtUnOpV op), .val (vecV a)] c ↔
    ∃ r, VecExtUnOpRel s t op a r ∧ c = vecV r
  extBinOp : ∀ s t op a b c, Applies env "vextbinop__"
    [.val (ishapeV s), .val (ishapeV t), .val (vExtBinOpV op), .val (vecV a), .val (vecV b)] c ↔
    ∃ r, VecExtBinOpRel P s t op a b r ∧ c = vecV r
  extTernOp : ∀ s t op a b d c, Applies env "vextternop__"
    [.val (ishapeV s), .val (ishapeV t), .val (vExtTernOpV op), .val (vecV a), .val (vecV b),
      .val (vecV d)] c ↔
    ∃ r, VecExtTernOpRel P s t op a b d r ∧ c = vecV r
  narrow : ∀ s t sx a b c, Applies env "vnarrowop__"
    [.val (ishV s), .val (ishV t), .val (sxV sx), .val (vecV a), .val (vecV b)] c ↔
    ∃ r, VecNarrowRel s t sx a b r ∧ c = vecV r

/-- **`$vcvtop__`, restated**: sound (every value the call denotes is a result Core allows) and
total where Core has a result. -/
structure VecConvertR (env : Env) (P : Profile) : Prop where
  /-- Every value of the call is an allowed result. -/
  sound : ∀ s t op a c, Applies env "vcvtop__"
    [.val (shapeV s), .val (shapeV t), .val (vConvertOpV op), .val (vecV a)] c →
    ∃ r, VecConvertRel P s t op a r ∧ c = vecV r
  /-- The call denotes something wherever Core has a result. -/
  total : ∀ s t op a r, VecConvertRel P s t op a r → ∃ c, Applies env "vcvtop__"
    [.val (shapeV s), .val (shapeV t), .val (vConvertOpV op), .val (vecV a)] c

end Silmaril.Wasm.SpecTec.Sim.Round5.Simd
