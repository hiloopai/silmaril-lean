module

public import Silmaril.Proofs.Wasm.SpecTec.Sim20.VecNumLanes

/-!
# What `vecNB P` answers for `vbinop` and `vrelop`, lane by lane

An earlier step proved `VecNum.vecFloatUnOpResult_lanes`: the answers of `vecNB P` for the float
`$vunop_` are the set product of the lane-wise scalar results put back with `$inv_lanes_`, the
clause of `3-numerics.spectec` read with binding `if` premises. This module states the same for
the other five answers of `vecNB P`:

* **`vecFloatBinOpResult_lanes`**: a float `vbinop` result is `$inv_lanes_` of lanes drawn
  pointwise from the scalar results of the operand lanes: `Numerics.floatBinOpP P t op` (what
  round 3's `Floats.FloatB P` answers for `$fadd_` … `$fmax_`) for `ADD` … `MAX`, and V2's
  `fpmin`/`fpmax` for `PMIN`/`PMAX`. Both NaN policies of the profile.
* **`vecFloatRelOp_lanes`**: a float `vrelop` result is `$inv_lanes_` of the lane-wise comparisons,
  each widened to all ones or zero (`ibool`).
* **`vecIntUnOpResult_lanes`**, **`vecIntBinOpResult_lanes`**, **`vecIntRelOp_lanes`**: an
  integer result is `$inv_lanes_` of the lane-wise scalar function (`intUnLane`, `intBinLane`,
  `ibool ∘ irelop`). The profile plays no role: V2's integer `vbinop` never reaches the relaxed
  operator.

What these do not say: that the scalar integer functions (`iaddSat`, `iq15mulrSatS`, …) and
`fpmin`/`fpmax` are what the script's `$iadd_sat_`, `$iq15mulr_sat_`, `$fpmin_`, … compute. The
float scalar operators are covered 's `Floats.FloatB`; the others are not checked here.
-/

@[expose] public section

namespace Silmaril.Wasm.SpecTec.Sim20.VecTyp

open Silmaril.Wasm
open Silmaril.Wasm.V2.Execution
open Silmaril.Wasm.Numerics
open Silmaril.Wasm.Numerics.VecLane

/-! ## Integer shapes -/

/-- The lane function of a V2 integer `vunop`. -/
def intUnLane (s : IntShape) : VecIntUnOp → ILane s → ILane s
  | .abs => iabs
  | .neg => ineg
  | .popcnt => ipopcnt

/-- The lane function of a V2 integer `vbinop`. -/
def intBinLane (s : IntShape) : V2.VecIntBinOp → ILane s → ILane s → ILane s
  | .add => (· + ·)
  | .sub => (· - ·)
  | .mul => (· * ·)
  | .addSat sx => iaddSat sx
  | .subSat sx => isubSat sx
  | .avgrU => iavgrU
  | .q15mulrSatS => iq15mulrSatS
  | .min sx => imin sx
  | .max sx => imax sx

/-- **V2's integer `vunop` result is the lane-wise scalar function**, put back with
`$inv_lanes_`. -/
theorem vecIntUnOpResult_lanes (s : IntShape) (op : VecIntUnOp) (c r : BitVec 128) :
    VecIntUnOpResult s op c r ↔ r = s.invLanes ((s.lanesOf c).map (intUnLane s op)) := by
  cases op <;> rfl

/-- **V2's integer `vbinop` result is the lane-wise scalar function of the lane pairs**, at every
profile. -/
theorem vecIntBinOpResult_lanes (P : Profile) (s : IntShape) (op : V2.VecIntBinOp)
    (c₁ c₂ r : BitVec 128) :
    VecIntBinOpResult P s op c₁ c₂ r ↔
      r = s.invLanes (List.zipWith (intBinLane s op) (s.lanesOf c₁) (s.lanesOf c₂)) := by
  cases op <;> rfl

/-- **V2's integer `vrelop` result is the lane-wise comparison**, widened to all ones or zero. -/
theorem vecIntRelOp_lanes (s : IntShape) (op : IntRelOp) (c₁ c₂ : BitVec 128) :
    VecIntRelOp s op c₁ c₂ =
      s.invLanes (List.zipWith (fun x y => ibool (irelop op x y)) (s.lanesOf c₁) (s.lanesOf c₂)) :=
  rfl

/-! ## Float shapes -/

/-- **V2's float `vrelop` result is the lane-wise comparison**, widened to all ones or zero. -/
theorem vecFloatRelOp_lanes (s : FloatShape) (op : FloatRelOp) (c₁ c₂ : BitVec 128) :
    VecFloatRelOp s op c₁ c₂ = s.invLanes (List.zipWith
      (fun x y => ibool (floatRelBool s.floatType op x y)) (s.lanesOf c₁) (s.lanesOf c₂)) :=
  rfl

/-- The lane results of a V2 float `vbinop`: the profile's scalar results for `ADD` … `MAX`, and
V2's `fpmin`/`fpmax` for `PMIN`/`PMAX`. -/
def floatBinLaneP (P : Profile) (t : FloatType) :
    V2.VecFloatBinOp → FloatValue t → FloatValue t → FloatValue t → Prop
  | .add => floatBinOpP P t .add
  | .sub => floatBinOpP P t .sub
  | .mul => floatBinOpP P t .mul
  | .div => floatBinOpP P t .div
  | .min => floatBinOpP P t .min
  | .max => floatBinOpP P t .max
  | .pmin => fun x y z => z = fpmin t x y
  | .pmax => fun x y z => z = fpmax t x y

/-- At the specification NaN policy, the lane relation is the one `vbinopFloatRel` uses. -/
theorem floatVecBinRel_spec {P : Profile} (hP : P.nan = .spec) (t : FloatType)
    (op : V2.VecFloatBinOp) : floatVecBinRel t op.toShared = some (floatBinLaneP P t op) := by
  cases op <;> simp only [floatVecBinRel, V2.VecFloatBinOp.toShared, floatBinLaneP,
    Option.some.injEq] <;> funext x y z <;> simp [floatBinOpP, hP]

/-- At the canonical NaN policy, the lane relation is the graph of the lane function
`vbinopFloat` uses. -/
theorem floatVecBin_canonical {P : Profile} (hP : P.nan = .canonical) (t : FloatType)
    (op : V2.VecFloatBinOp) : ∃ f, floatVecBin t op.toShared = some f ∧
      floatBinLaneP P t op = fun x y z => z = f x y := by
  cases op <;> refine ⟨_, rfl, ?_⟩ <;> funext x y z <;>
    simp [floatBinLaneP, floatBinOpP, hP]

/-- The lane-wise form of `$inv_lanes_` of a lane function of the lane pairs. -/
theorem invLanes_zipWith_iff (s : FloatShape)
    (f : FloatValue s.floatType → FloatValue s.floatType → FloatValue s.floatType)
    (c₁ c₂ r : BitVec 128) :
    s.invLanes (List.zipWith f (s.lanesOf c₁) (s.lanesOf c₂)) = r ↔ ∃ zs, List.Forall₂
      (fun p z => z = f p.1 p.2) ((s.lanesOf c₁).zip (s.lanesOf c₂)) zs ∧ r = s.invLanes zs := by
  let g : FloatValue s.floatType × FloatValue s.floatType → FloatValue s.floatType :=
    fun p => f p.1 p.2
  have hz : List.zipWith f (s.lanesOf c₁) (s.lanesOf c₂) =
      ((s.lanesOf c₁).zip (s.lanesOf c₂)).map g :=
    (List.map_zip_eq_zipWith (f := g)).symm
  rw [hz]
  constructor
  · rintro rfl
    exact ⟨_, (VecNum.forall₂_eq_map_iff g _ _).2 rfl, rfl⟩
  · rintro ⟨zs, hz, rfl⟩
    rw [(VecNum.forall₂_eq_map_iff g _ _).1 hz]

/-- At the canonical NaN policy, V2's float `vbinop` result is the lane function's. -/
theorem vecFloatBinOpResult_canonical {P : Profile} (hP : P.nan = .canonical) (s : FloatShape)
    (op : V2.VecFloatBinOp) (c₁ c₂ r : BitVec 128) :
    VecFloatBinOpRel P s op.toShared c₁ c₂ r ↔ vbinopFloat s op.toShared c₁ c₂ = some r := by
  simp only [VecFloatBinOpRel, hP]
  cases op <;> cases P.nd <;> rfl

/-- At the specification NaN policy, V2's float `vbinop` results are `vbinopFloatRel`'s. -/
theorem vecFloatBinOpResult_spec {P : Profile} (hP : P.nan = .spec) (s : FloatShape)
    (op : V2.VecFloatBinOp) (c₁ c₂ r : BitVec 128) :
    VecFloatBinOpRel P s op.toShared c₁ c₂ r ↔ vbinopFloatRel s op.toShared c₁ c₂ r := by
  simp only [VecFloatBinOpRel, hP]
  cases op <;> rfl

/-- **V2's float `vbinop` results are the set product of the lane-wise results of the operand
lane pairs**, put back with `$inv_lanes_`, at both NaN policies. -/
theorem vecFloatBinOpResult_lanes (P : Profile) (s : FloatShape) (op : V2.VecFloatBinOp)
    (c₁ c₂ r : BitVec 128) :
    VecFloatBinOpResult P s op c₁ c₂ r ↔ ∃ zs, List.Forall₂
      (fun p z => floatBinLaneP P s.floatType op p.1 p.2 z)
      ((s.lanesOf c₁).zip (s.lanesOf c₂)) zs ∧ r = s.invLanes zs := by
  simp only [VecFloatBinOpResult]
  cases hP : P.nan with
  | spec =>
    rw [vecFloatBinOpResult_spec hP]
    simp only [vbinopFloatRel, floatVecBinRel_spec hP, invLanesSet, lanesRel2,
      FloatShape.invLanes]
  | canonical =>
    obtain ⟨f, hf, hR⟩ := floatVecBin_canonical hP s.floatType op
    rw [vecFloatBinOpResult_canonical hP, hR]
    simp only [vbinopFloat, hf, Option.map_some, Option.some.injEq]
    exact invLanes_zipWith_iff s f c₁ c₂ r

end Silmaril.Wasm.SpecTec.Sim20.VecTyp
