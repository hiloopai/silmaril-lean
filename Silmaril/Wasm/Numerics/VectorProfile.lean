module

public import Silmaril.Wasm.Numerics.Profile
public import Silmaril.Wasm.Numerics.Relaxed
public import Silmaril.Wasm.Instructions

@[expose] public section

/-! # Profile-aware vector numerics (the interface used by Core reduction)

The numerics library (`Numerics/VectorLanes.lean`, `Numerics/Vector.lean`,
`Numerics/Relaxed.lean`) gives every §3.2 vector operator: deterministic
integer/bitwise operators as functions, NaN-nondeterministic float operators as
result sets (`*Rel`) with a canonical function alongside (`*_self`), and relaxed
operators parameterised by `$ND` and the builtins `$R_*`.

This file packages them for a `Profile`:

* `P.nan = .spec`: the spec's result sets;
* `P.nan = .canonical`: the canonical-NaN functions (the deterministic profile);
* relaxed operators use `P.nd` and `P.relaxed`.

`VectorStep` (`Execution/Core/Step/Vector.lean`) and the vector memory rules use
only the names defined here.
-/

namespace Silmaril.Wasm.Numerics

/-- `$lanes_(w×n, v)` (little-endian). -/
def lanes (w n : Nat) (v : V128) : List (BitVec w) := lanesW w n v

/-- `$inv_lanes_(w×n, c*)`. -/
def invLanes (w : Nat) (cs : List (BitVec w)) : V128 := invLanesW w cs

theorem invLanes_lanes (w n : Nat) (hw : w * n = 128) (v : V128) :
    invLanes w (lanes w n v) = v :=
  invLanesW_lanesW hw v

theorem lanes_invLanes (w n : Nat) (hw : w * n = 128) (cs : List (BitVec w)) (hn : cs.length = n) :
    lanes w n (invLanes w cs) = cs :=
  lanesW_invLanesW (Nat.le_of_eq hw) cs hn

/-! ## Integer lanes -/

def vecIntUnOp (sh : IntShape) (op : VecIntUnOp) (v : V128) : V128 := vunopInt sh op v

/-- `$ivbinop_`, including `relaxed_q15mulr_s` (through `P.nd`, `$R_iq15mulr`). -/
def vecIntBinOp (P : Profile) (sh : IntShape) (op : VecIntBinOp) (a b : V128) : V128 :=
  vbinopIntRelaxed P.nd P.relaxed sh op a b

def vecIntRelOp (sh : IntShape) (op : IntRelOp) (a b : V128) : V128 := vrelopInt sh op a b

def vecShiftOp (sh : IntShape) (op : VecShiftOp) (v : V128) (count : BitVec 32) : V128 :=
  vshiftop sh op v count

/-- `all_true`. -/
def vecAllTrue (sh : IntShape) (v : V128) : BitVec 32 := vtestop sh v

def vecBitmask (sh : IntShape) (v : V128) : BitVec 32 := vbitmask sh v

/-- `relaxed_laneselect` (`$vternop_` on integer shapes). -/
def vecIntTernOp (P : Profile) (sh : IntShape) (_op : VecIntTernOp) (a b c : V128) : V128 :=
  vrelaxedLaneselect P.nd P.relaxed sh a b c

/-! ## Lane shuffling -/

def vecSwizzle (a s : V128) : V128 := (vswizzlop .swizzle a s).getD 0

def vecRelaxedSwizzle (P : Profile) (a s : V128) : V128 := vrelaxedSwizzle P.nd P.relaxed a s

def vecShuffle (idx : List LaneIdx) (a b : V128) : V128 := vshuffle (idx.map (·.val)) a b

/-- `vsplat`: replicate the (wrapped) scalar. -/
def vecSplat (sh : Shape) (x : BitVec sh.unpacked.width) : V128 := vsplat sh x

/-- `vextract_lane` (sign or zero extended for packed integer lanes). -/
def vecExtractLane (sh : Shape) (sx : Option Signedness) (i : Nat) (v : V128) :
    BitVec sh.unpacked.width :=
  let c := vextractLane sh i v
  match sx with
  | some .signed => c.signExtend _
  | _ => c.setWidth _

/-- `vreplace_lane`. -/
def vecReplaceLane (sh : Shape) (i : Nat) (v : V128) (x : BitVec sh.unpacked.width) : V128 :=
  vreplaceLane sh i x v

/-! ## Float lanes -/

/-- `$fvunop_`. -/
def VecFloatUnOpRel (P : Profile) (sh : FloatShape) (op : FloatUnOp) (a r : V128) : Prop :=
  match P.nan with
  | .spec => vunopFloatRel sh op a r
  | .canonical => r = vunopFloat sh op a

/-- `$fvbinop_`, including `relaxed_min`/`relaxed_max`. With `$ND = false` the
relaxed operators are `min`/`max` (`vbinopFloatRelaxedRel_false_min/max`). -/
def VecFloatBinOpRel (P : Profile) (sh : FloatShape) (op : VecFloatBinOp) (a b r : V128) : Prop :=
  match P.nan with
  | .spec => vbinopFloatRelaxedRel P.nd P.relaxed sh op a b r
  | .canonical =>
    match op, P.nd with
    | .relaxedMin, true | .relaxedMax, true => vbinopFloatRelaxedRel P.nd P.relaxed sh op a b r
    | .relaxedMin, false => vbinopFloat sh .min a b = some r
    | .relaxedMax, false => vbinopFloat sh .max a b = some r
    | op, _ => vbinopFloat sh op a b = some r

/-- `$fvrelop_`. -/
def vecFloatRelOp (sh : FloatShape) (op : FloatRelOp) (a b : V128) : V128 := vrelopFloat sh op a b

/-- The canonical unfused `relaxed_madd`/`relaxed_nmadd` lane result (`$ND = false`). -/
def fmaddCanon (t : FloatType) : VecFloatTernOp → FloatValue t → FloatValue t → FloatValue t →
    FloatValue t
  | .relaxedMadd, x, y, z => floatBinOp t .add (floatBinOp t .mul x y) z
  | .relaxedNmadd, x, y, z => floatBinOp t .add (floatBinOp t .mul (floatUnOp t .neg x) y) z

/-- `$fvternop_` (`relaxed_madd`, `relaxed_nmadd`). -/
def VecFloatTernOpRel (P : Profile) (sh : FloatShape) (op : VecFloatTernOp) (a b c r : V128) :
    Prop :=
  match P.nan, P.nd with
  | .canonical, false =>
    r = sh.invLanes (List.zipWith3 (fmaddCanon sh.floatType op)
      (sh.lanesOf a) (sh.lanesOf b) (sh.lanesOf c))
  | _, _ => vrelaxedMaddRel P.nd P.relaxed sh op a b c r

/-! ## Extending, narrowing and conversion -/

/-- `$vextunop__`. -/
def VecExtUnOpRel (sh₁ sh₂ : IntShape) (op : VecExtUnOp) (a r : V128) : Prop :=
  r = vextunop sh₁ sh₂ op a

/-- `$vextbinop__` (`extmul`, `dot`, `relaxed_dot`). -/
def VecExtBinOpRel (P : Profile) (sh₁ sh₂ : IntShape) (op : VecExtBinOp) (a b r : V128) : Prop :=
  match op with
  | .relaxedDotS => r = vrelaxedDot P.nd P.relaxed a b
  | op => vextbinop sh₁ sh₂ op a b = some r

/-- `$vextternop__` (`relaxed_dot_add`). -/
def VecExtTernOpRel (P : Profile) (_sh₁ _sh₂ : IntShape) (_op : VecExtTernOp) (a b c r : V128) :
    Prop :=
  r = vrelaxedDotAdd P.nd P.relaxed a b c

/-- `$vnarrowop__`. -/
def VecNarrowRel (sh₁ sh₂ : IntShape) (sx : Signedness) (a b r : V128) : Prop :=
  r = vnarrow sh₁ sh₂ sx a b

/-- `$vcvtop__`, including `relaxed_trunc`. -/
def VecConvertRel (P : Profile) (src tgt : Shape) (op : VecConvertOp) (a r : V128) : Prop :=
  match op with
  | .relaxedTrunc sx _ =>
    match src with
    | .float fs => tgt = .int .i32x4 ∧ vrelaxedTruncRel P.nd P.relaxed sx fs a r
    | .int _ => False
  | op =>
    match P.nan with
    | .spec => vcvtopRel op src tgt a r
    | .canonical => vcvtop op src tgt a = some r


/-! ## Non-emptiness of the result relations -/

theorem VecFloatUnOpRel_nonempty (P : Profile) (sh : FloatShape) (op : FloatUnOp) (a : V128) :
    ∃ r, VecFloatUnOpRel P sh op a r := by
  unfold VecFloatUnOpRel
  cases P.nan
  · exact ⟨_, vunopFloatRel_self sh op a⟩
  · exact ⟨_, rfl⟩

theorem VecExtUnOpRel_nonempty (sh₁ sh₂ : IntShape) (op : VecExtUnOp) (a : V128) :
    ∃ r, VecExtUnOpRel sh₁ sh₂ op a r := ⟨_, rfl⟩

theorem VecExtBinOpRel_nonempty (P : Profile) (sh₁ sh₂ : IntShape) (op : VecExtBinOp)
    (a b : V128) : ∃ r, VecExtBinOpRel P sh₁ sh₂ op a b r := by
  cases op <;> exact ⟨_, rfl⟩

theorem VecExtTernOpRel_nonempty (P : Profile) (sh₁ sh₂ : IntShape) (op : VecExtTernOp)
    (a b c : V128) : ∃ r, VecExtTernOpRel P sh₁ sh₂ op a b c r := ⟨_, rfl⟩

theorem VecNarrowRel_nonempty (sh₁ sh₂ : IntShape) (sx : Signedness) (a b : V128) :
    ∃ r, VecNarrowRel sh₁ sh₂ sx a b r := ⟨_, rfl⟩

theorem vcvtop_isSome_of_valid {op : VecConvertOp} {src tgt : Shape}
    (hop : ∀ sx z, op ≠ .relaxedTrunc sx z) (h : op.valid src tgt = true) (a : V128) :
    ∃ r, vcvtop op src tgt a = some r := by
  cases op with
  | relaxedTrunc sx z => exact absurd rfl (hop sx z)
  | extend hf sx =>
    rcases src with s | s <;> rcases tgt with t | t <;> simp [VecConvertOp.valid] at h
    simp [vcvtop, h]
  | convert hf sx =>
    rcases src with s | s <;> rcases tgt with t | t <;> cases s <;> cases t <;>
      simp [VecConvertOp.valid] at h <;> (try cases hf) <;> (try rename_i hf; cases hf) <;>
      simp_all [vcvtop]
  | truncSat sx z =>
    rcases src with s | s <;> rcases tgt with t | t <;> cases s <;> cases t <;> cases z <;>
      simp_all [VecConvertOp.valid, vcvtop]
  | demoteZero =>
    rcases src with s | s <;> rcases tgt with t | t <;> cases s <;> cases t <;>
      simp_all [VecConvertOp.valid, vcvtop]
  | promoteLow =>
    rcases src with s | s <;> rcases tgt with t | t <;> cases s <;> cases t <;>
      simp_all [VecConvertOp.valid, vcvtop]

theorem relaxedTrunc_nonempty (nd : Bool) (p : RelaxedParams) (t : FloatType) (sx : Signedness)
    (x : FloatValue t) : ∃ y, relaxedTrunc nd p t sx x y := by
  unfold relaxedTrunc
  cases sx
  · generalize truncFloat t .i32 .signed x = e
    rcases e with e | r
    · refine ⟨truncSatFloat t .i32 .signed x, ?_⟩
      rcases nd with _ | _ <;> simp only [relaxed2, Bool.false_eq_true, ↓reduceIte]
      (try split_ifs) <;> trivial
    · exact ⟨r, rfl⟩
  · generalize truncFloat t .i32 .unsigned x = e
    rcases e with e | r
    · refine ⟨truncSatFloat t .i32 .unsigned x, ?_⟩
      rcases nd with _ | _ <;> simp only [relaxed4, Bool.false_eq_true, ↓reduceIte]
      (try split_ifs) <;> trivial
    · exact ⟨r, rfl⟩

theorem forall₂_nonempty {α β : Type} {R : α → β → Prop} (h : ∀ x, ∃ y, R x y) :
    ∀ xs : List α, ∃ ys, List.Forall₂ R xs ys
  | [] => ⟨[], .nil⟩
  | x :: xs => by
    obtain ⟨y, hy⟩ := h x
    obtain ⟨ys, hys⟩ := forall₂_nonempty h xs
    exact ⟨y :: ys, .cons hy hys⟩

theorem VecConvertRel_nonempty (P : Profile) {src tgt : Shape} {op : VecConvertOp}
    (h : op.valid src tgt = true) (a : V128) : ∃ r, VecConvertRel P src tgt op a r := by
  by_cases hop : ∃ sx z, op = .relaxedTrunc sx z
  · obtain ⟨sx, z, rfl⟩ := hop
    rcases src with s | s <;> rcases tgt with t | t <;> cases s <;> cases t <;>
      simp [VecConvertOp.valid] at h
    · obtain ⟨c, hc⟩ := forall₂_nonempty (relaxedTrunc_nonempty P.nd P.relaxed .f32 sx)
        (FloatShape.f32x4.lanesOf a)
      exact ⟨_, rfl, c, hc, rfl⟩
    · obtain ⟨c, hc⟩ := forall₂_nonempty (relaxedTrunc_nonempty P.nd P.relaxed .f64 sx)
        (FloatShape.f64x2.lanesOf a)
      exact ⟨_, rfl, c, hc, rfl⟩
  · push Not at hop
    obtain ⟨r, hr⟩ := vcvtop_isSome_of_valid hop h a
    refine ⟨r, ?_⟩
    unfold VecConvertRel
    split
    · rename_i sx z; exact absurd rfl (hop sx z)
    · cases P.nan
      · exact vcvtopRel_self _ _ _ _ _ hr
      · exact hr

/-! ## Determinism of relaxed operators with `$ND = false` -/

theorem vecIntTernOp_det {P Q : Profile} (hP : P.nd = false) (hQ : Q.nd = false)
    (sh : IntShape) (op : VecIntTernOp) (a b c : V128) :
    vecIntTernOp P sh op a b c = vecIntTernOp Q sh op a b c := by
  simp only [vecIntTernOp, hP, hQ, vrelaxedLaneselect_false]

theorem vecRelaxedSwizzle_det {P Q : Profile} (hP : P.nd = false) (hQ : Q.nd = false)
    (a s : V128) : vecRelaxedSwizzle P a s = vecRelaxedSwizzle Q a s := by
  simp only [vecRelaxedSwizzle, hP, hQ, vrelaxedSwizzle_false]

theorem vecIntBinOp_det {P Q : Profile} (hP : P.nd = false) (hQ : Q.nd = false)
    (sh : IntShape) (op : VecIntBinOp) (a b : V128) :
    vecIntBinOp P sh op a b = vecIntBinOp Q sh op a b := by
  simp only [vecIntBinOp, hP, hQ, vbinopIntRelaxed_false]

end Silmaril.Wasm.Numerics
