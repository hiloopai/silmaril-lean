module

public import Silmaril.Wasm.Numerics.Vector
public import Silmaril.Wasm.Numerics.Conversion
public import Mathlib.Data.Set.Defs

@[expose] public section

/-!
# Relaxed numerics (spec 3.0-numerics.relaxed + relaxed parts of 3.1/3.2)

Merged from the integer and vector numerics branches: `$relaxed2`/`$relaxed4`,
the single `RelaxedChoice` record of builtins `$R_*`, the choice sets
`relaxed2Set`/`relaxed4Set`, and the relaxed SIMD operators.

The spec fixes a global implementation parameter `R_x` per relaxed family and
selects `relaxed(R)[A_0, …, A_n] = A_R` when the non-deterministic profile flag
`$ND` holds, and `A_0` otherwise (deterministic profile). We parameterise every
operator by `nd : Bool` and a `RelaxedParams` record. The parameters are global,
so a single `p` governs all lanes of a vector operation.

The scalar `builtin`s are transcribed from the prose (`exec/numerics.rst`,
"Relaxed Operations"). Choices made where the prose is informal:
* `NaN(n)` in `frelaxed_min/max` is read as the input NaN's payload with either
  sign (`nanPayload`).
* `𝐑` (the second alternative of `relaxed_trunc`) is read as "any value".
* The prose gives `R_trunc_u ∈ {0, 1}` but the SpecTec declares it `relaxed4`;
  we follow the SpecTec (alternatives 2 and 3 repeat "any value").
* `irelaxed_q15mulr` / `irelaxed_laneselect` are declared `iN(N)*` but are
  single-valued once `R` is fixed, so they are functions here.

Float results are sets (`· → Prop`) reusing the scalar NaN relations.
-/

namespace Silmaril.Wasm.Numerics

open VecLane

/-- `$relaxed2`. -/
def relaxed2 {α : Sort _} (nd : Bool) (i : Fin 2) (a b : α) : α :=
  if nd then (if i.val = 0 then a else b) else a

/-- `$relaxed4`. -/
def relaxed4 {α : Sort _} (nd : Bool) (i : Fin 4) (a b c d : α) : α :=
  if nd then (if i.val = 0 then a else if i.val = 1 then b else if i.val = 2 then c else d) else a

/-- The implementation-defined builtin choices `$R_*` of spec §3.0 (one record for
the whole development: scalar, vector and profile code all use it). `$R_trunc_u`
is `relaxed4` in the SpecTec source. -/
structure RelaxedChoice where
  fmadd : Fin 2 := 0
  fmin : Fin 4 := 0
  fmax : Fin 4 := 0
  idot : Fin 2 := 0
  iq15mulr : Fin 2 := 0
  truncU : Fin 4 := 0
  truncS : Fin 2 := 0
  swizzle : Fin 2 := 0
  laneselect : Fin 2 := 0
  deriving DecidableEq, Repr

instance : Inhabited RelaxedChoice := ⟨{}⟩

/-- Name used by the vector numerics. -/
abbrev RelaxedParams := RelaxedChoice
/-- Name used by the width-parametric integer numerics. -/
abbrev RelaxedChoices := RelaxedChoice

/-- The all-zero (deterministic-profile) parameters. -/
def RelaxedChoice.det : RelaxedChoice := {}

/-- Every result some implementation choice may produce. -/
def relaxed2Set {α : Type _} (nd : Bool) (x₁ x₂ : α) : Set α :=
  {x | ∃ i, relaxed2 nd i x₁ x₂ = x}

def relaxed4Set {α : Type _} (nd : Bool) (x₁ x₂ x₃ x₄ : α) : Set α :=
  {x | ∃ i, relaxed4 nd i x₁ x₂ x₃ x₄ = x}

/-- The deterministic profile admits exactly the first alternative. -/
theorem relaxed2Set_false {α : Type _} (x₁ x₂ : α) : relaxed2Set false x₁ x₂ = {x₁} := by
  ext x; exact ⟨fun ⟨_, h⟩ => h.symm, fun h => ⟨0, h.symm⟩⟩

theorem relaxed4Set_false {α : Type _} (x₁ x₂ x₃ x₄ : α) :
    relaxed4Set false x₁ x₂ x₃ x₄ = {x₁} := by
  ext x; exact ⟨fun ⟨_, h⟩ => h.symm, fun h => ⟨0, h.symm⟩⟩

@[simp] theorem relaxed2_false {α : Sort _} (i : Fin 2) (a b : α) : relaxed2 false i a b = a := rfl
@[simp] theorem relaxed4_false {α : Sort _} (i : Fin 4) (a b c d : α) :
    relaxed4 false i a b c d = a := rfl
@[simp] theorem relaxed2_zero {α : Sort _} (nd : Bool) (a b : α) : relaxed2 nd 0 a b = a := by
  cases nd <;> rfl
@[simp] theorem relaxed4_zero {α : Sort _} (nd : Bool) (a b c d : α) :
    relaxed4 nd 0 a b c d = a := by cases nd <;> rfl

/-- The deterministic profile is the index-0 choice. -/
theorem relaxed2_false_eq_true_zero {α : Sort _} (i : Fin 2) (a b : α) :
    relaxed2 false i a b = relaxed2 true 0 a b := rfl
theorem relaxed4_false_eq_true_zero {α : Sort _} (i : Fin 4) (a b c d : α) :
    relaxed4 false i a b c d = relaxed4 true 0 a b c d := rfl

/-! ## Scalar float helpers -/

def floatIsNaN : (t : FloatType) → FloatValue t → Prop
  | .f32, x => (asF32 x).IsNaN
  | .f64, x => (asF64 x).IsNaN

instance (t : FloatType) (x : FloatValue t) : Decidable (floatIsNaN t x) := by
  cases t <;> unfold floatIsNaN <;> infer_instance

/-- `±0` and `∓0`. -/
def oppositeZeros {n : Nat} (x y : BitVec n) : Prop :=
  (x = 0 ∧ y = BitVec.intMin n) ∨ (x = BitVec.intMin n ∧ y = 0)

instance {n : Nat} (x y : BitVec n) : Decidable (oppositeZeros x y) := by
  unfold oppositeZeros; infer_instance

/-- `NaN(n)`: the NaN with the payload of `x`, either sign. -/
def nanPayload (t : FloatType) (x z : FloatValue t) : Prop := z = x ∨ z = floatUnOp t .neg x

/-- The allowed results of IEEE fused multiply-add under the Wasm NaN policy. -/
def fmaRel : (t : FloatType) → FloatValue t → FloatValue t → FloatValue t → FloatValue t → Prop
  | .f32, x, y, z, r => Silmaril.Numeric.Ieee754.F32.fmaNaNRel (asF32 x) (asF32 y) (asF32 z) (asF32 r)
  | .f64, x, y, z, r => Silmaril.Numeric.Ieee754.F64.fmaNaNRel (asF64 x) (asF64 y) (asF64 z) (asF64 r)

/-! ## Scalar relaxed operators -/

/-- `$frelaxed_madd_`: `relaxed(R_fmadd)[fadd(fmul(z1,z2),z3), fma(z1,z2,z3)]`. -/
def frelaxedMadd (nd : Bool) (p : RelaxedParams) (t : FloatType) (z1 z2 z3 : FloatValue t) :
    FloatValue t → Prop :=
  relaxed2 nd p.fmadd
    (fun r => ∃ m, floatBinOpRel t .mul z1 z2 m ∧ floatBinOpRel t .add m z3 r)
    (fmaRel t z1 z2 z3)

/-- `$frelaxed_nmadd_ = frelaxed_madd(-z1, z2, z3)`. -/
def frelaxedNmadd (nd : Bool) (p : RelaxedParams) (t : FloatType) (z1 z2 z3 : FloatValue t) :
    FloatValue t → Prop :=
  frelaxedMadd nd p t (floatUnOp t .neg z1) z2 z3

/-- `$frelaxed_min_`. -/
def frelaxedMin (nd : Bool) (p : RelaxedParams) (t : FloatType) (z1 z2 : FloatValue t) :
    FloatValue t → Prop :=
  if floatIsNaN t z1 then
    relaxed4 nd p.fmin (floatBinOpRel t .min z1 z2) (nanPayload t z1) (· = z2) (· = z2)
  else if floatIsNaN t z2 then
    relaxed4 nd p.fmin (floatBinOpRel t .min z1 z2) (· = z1) (nanPayload t z2) (· = z1)
  else if oppositeZeros z1 z2 then
    relaxed4 nd p.fmin (floatBinOpRel t .min z1 z2) (· = z1) (· = z2) (· = BitVec.intMin _)
  else floatBinOpRel t .min z1 z2

/-- `$frelaxed_max_`. -/
def frelaxedMax (nd : Bool) (p : RelaxedParams) (t : FloatType) (z1 z2 : FloatValue t) :
    FloatValue t → Prop :=
  if floatIsNaN t z1 then
    relaxed4 nd p.fmax (floatBinOpRel t .max z1 z2) (nanPayload t z1) (· = z2) (· = z2)
  else if floatIsNaN t z2 then
    relaxed4 nd p.fmax (floatBinOpRel t .max z1 z2) (· = z1) (nanPayload t z2) (· = z1)
  else if oppositeZeros z1 z2 then
    relaxed4 nd p.fmax (floatBinOpRel t .max z1 z2) (· = z1) (· = z2) (· = 0)
  else floatBinOpRel t .max z1 z2

/-- `$irelaxed_q15mulr_s`. -/
def irelaxedQ15mulr {n : Nat} (nd : Bool) (p : RelaxedParams) (x y : BitVec n) : BitVec n :=
  if x = BitVec.intMin n ∧ y = BitVec.intMin n then
    relaxed2 nd p.iq15mulr (BitVec.intMax n) (BitVec.intMin n)
  else iq15mulrSatS x y

/-- `$irelaxed_laneselect_`: `ibitselect(i1, i2, relaxed[i3, extend_s(1,N)(ishr_u(i3, N-1))])`. -/
def irelaxedLaneselect {n : Nat} (nd : Bool) (p : RelaxedParams) (x y m : BitVec n) : BitVec n :=
  ibitselect x y (relaxed2 nd p.laneselect m (ibool m.msb))

/-- `$irelaxed_swizzle_lane_`. -/
def irelaxedSwizzleLane {n : Nat} (nd : Bool) (p : RelaxedParams) (c : List (BitVec n))
    (i : BitVec n) : BitVec n :=
  if i.toNat < c.length then c.getD i.toNat 0
  else if i.toInt < 0 then 0
  else relaxed2 nd p.swizzle 0 (c.getD (i.toNat % c.length) 0)

/-- `$relaxed_trunc__(M, 32, sx, z)`: exact when `trunc` is in range, else
`relaxed(R_trunc_sx)[trunc_sat(z), 𝐑]`. -/
def relaxedTrunc (nd : Bool) (p : RelaxedParams) (t : FloatType) (sx : Signedness)
    (x : FloatValue t) : IntValue .i32 → Prop :=
  match truncFloat t .i32 sx x with
  | .ok r => (· = r)
  | .error _ =>
    match sx with
    | .signed => relaxed2 nd p.truncS (· = truncSatFloat t .i32 sx x) (fun _ => True)
    | .unsigned => relaxed4 nd p.truncU (· = truncSatFloat t .i32 sx x) (fun _ => True)
        (fun _ => True) (fun _ => True)

/-! ## Vector relaxed operators -/

/-- `relaxed_madd` / `relaxed_nmadd` (`$fvternop_`). -/
def vrelaxedMaddRel (nd : Bool) (p : RelaxedParams) (s : FloatShape) (op : VecFloatTernOp)
    (v1 v2 v3 r : V128) : Prop :=
  invLanesSet _ (lanesRel3 (match op with
      | .relaxedMadd => frelaxedMadd nd p s.floatType
      | .relaxedNmadd => frelaxedNmadd nd p s.floatType)
    (s.lanesOf v1) (s.lanesOf v2) (s.lanesOf v3)) r

/-- `relaxed_min` / `relaxed_max` (`$fvbinop_`). Full float binary dispatcher,
delegating non-relaxed operators to `vbinopFloatRel`. -/
def vbinopFloatRelaxedRel (nd : Bool) (p : RelaxedParams) (s : FloatShape) (op : VecFloatBinOp)
    (v1 v2 r : V128) : Prop :=
  match op with
  | .relaxedMin => invLanesSet _ (lanesRel2 (frelaxedMin nd p s.floatType) (s.lanesOf v1) (s.lanesOf v2)) r
  | .relaxedMax => invLanesSet _ (lanesRel2 (frelaxedMax nd p s.floatType) (s.lanesOf v1) (s.lanesOf v2)) r
  | op => vbinopFloatRel s op v1 v2 r

/-- Full integer binary dispatcher including `relaxed_q15mulr_s`. -/
def vbinopIntRelaxed (nd : Bool) (p : RelaxedParams) (s : IntShape) (op : VecIntBinOp)
    (v1 v2 : V128) : V128 :=
  match op with
  | .relaxedQ15mulrS => ivbinop s (irelaxedQ15mulr nd p) v1 v2
  | op => (vbinopInt s op v1 v2).getD 0

/-- `relaxed_laneselect` (`$ivternopnd_`). -/
def vrelaxedLaneselect (nd : Bool) (p : RelaxedParams) (s : IntShape) (v1 v2 v3 : V128) : V128 :=
  s.invLanes (List.zipWith3 (irelaxedLaneselect nd p) (s.lanesOf v1) (s.lanesOf v2) (s.lanesOf v3))

/-- `relaxed_swizzle` (i8x16). -/
def vrelaxedSwizzle (nd : Bool) (p : RelaxedParams) (v1 v2 : V128) : V128 :=
  IntShape.i8x16.invLanes ((IntShape.i8x16.lanesOf v2).map
    (irelaxedSwizzleLane nd p (IntShape.i8x16.lanesOf v1)))

/-- `relaxed_trunc` (`$vcvtop__`): f32x4 → i32x4, or f64x2 → i32x4 with zero fill. -/
def vrelaxedTruncRel (nd : Bool) (p : RelaxedParams) (sx : Signedness) (src : FloatShape)
    (v r : V128) : Prop :=
  match src with
  | .f32x4 => invLanesSet 32 (List.Forall₂ (relaxedTrunc nd p .f32 sx) (FloatShape.f32x4.lanesOf v)) r
  | .f64x2 => ∃ c, List.Forall₂ (relaxedTrunc nd p .f64 sx) (FloatShape.f64x2.lanesOf v) c ∧
      r = IntShape.i32x4.invLanes (c ++ [0, 0])

/-- `relaxed_dot` i8x16 → i16x8: `$ivextbinop__` with `$ivdot_sat_`, the second
operand extended with `relaxed(R_idot)[S, U]`. -/
def vrelaxedDot (nd : Bool) (p : RelaxedParams) (v1 v2 : V128) : V128 :=
  ivextbinop .i8x16 .i16x8 dotSat .signed (relaxed2 nd p.idot .signed .unsigned) 0 16 v1 v2

/-- `relaxed_dot_add` i8x16 → i32x4: relaxed dot, then signed pairwise extending
add to i32x4, then lane-wise add of `v3`. -/
def vrelaxedDotAdd (nd : Bool) (p : RelaxedParams) (v1 v2 v3 : V128) : V128 :=
  ivbinop .i32x4 (· + ·) (vextunop .i16x8 .i32x4 (.extaddPairwise .signed) (vrelaxedDot nd p v1 v2)) v3

/-! ## Profile lemmas: ND = false is the index-0 choice, and lies in the ND = true family -/

section Profile
variable (p : RelaxedParams)

theorem frelaxedMadd_false (t : FloatType) (a b c : FloatValue t) :
    frelaxedMadd false p t a b c = frelaxedMadd true .det t a b c := rfl
theorem frelaxedNmadd_false (t : FloatType) (a b c : FloatValue t) :
    frelaxedNmadd false p t a b c = frelaxedNmadd true .det t a b c := rfl
theorem frelaxedMin_false (t : FloatType) (a b : FloatValue t) :
    frelaxedMin false p t a b = frelaxedMin true .det t a b := rfl
theorem frelaxedMax_false (t : FloatType) (a b : FloatValue t) :
    frelaxedMax false p t a b = frelaxedMax true .det t a b := rfl
theorem irelaxedQ15mulr_false {n : Nat} (a b : BitVec n) :
    irelaxedQ15mulr false p a b = irelaxedQ15mulr true .det a b := rfl
theorem irelaxedLaneselect_false {n : Nat} (a b c : BitVec n) :
    irelaxedLaneselect false p a b c = irelaxedLaneselect true .det a b c := rfl
theorem irelaxedSwizzleLane_false {n : Nat} (c : List (BitVec n)) (i : BitVec n) :
    irelaxedSwizzleLane false p c i = irelaxedSwizzleLane true .det c i := rfl
theorem relaxedTrunc_false (t : FloatType) (sx : Signedness) (x : FloatValue t) :
    relaxedTrunc false p t sx x = relaxedTrunc true .det t sx x := by
  unfold relaxedTrunc; split <;> cases sx <;> rfl

theorem vrelaxedMaddRel_false (s : FloatShape) (op : VecFloatTernOp) (a b c : V128) :
    vrelaxedMaddRel false p s op a b c = vrelaxedMaddRel true .det s op a b c := rfl
theorem vbinopFloatRelaxedRel_false (s : FloatShape) (op : VecFloatBinOp) (a b : V128) :
    vbinopFloatRelaxedRel false p s op a b = vbinopFloatRelaxedRel true .det s op a b := rfl
theorem vbinopIntRelaxed_false (s : IntShape) (op : VecIntBinOp) (a b : V128) :
    vbinopIntRelaxed false p s op a b = vbinopIntRelaxed true .det s op a b := rfl
theorem vrelaxedLaneselect_false (s : IntShape) (a b c : V128) :
    vrelaxedLaneselect false p s a b c = vrelaxedLaneselect true .det s a b c := rfl
theorem vrelaxedSwizzle_false (a b : V128) :
    vrelaxedSwizzle false p a b = vrelaxedSwizzle true .det a b := rfl
theorem vrelaxedTruncRel_false (sx : Signedness) (src : FloatShape) (a : V128) :
    vrelaxedTruncRel false p sx src a = vrelaxedTruncRel true .det sx src a := by
  have h : ∀ t, relaxedTrunc false p t sx = relaxedTrunc true .det t sx :=
    fun t => funext fun x => relaxedTrunc_false p t sx x
  cases src <;> funext r <;> unfold vrelaxedTruncRel <;> rw [h, h]
theorem vrelaxedDot_false (a b : V128) : vrelaxedDot false p a b = vrelaxedDot true .det a b := rfl
theorem vrelaxedDotAdd_false (a b c : V128) :
    vrelaxedDotAdd false p a b c = vrelaxedDotAdd true .det a b c := rfl

/-- Inclusion: every deterministic-profile result is a non-deterministic result
for some choice of the global parameters (namely `det`). -/
theorem vrelaxedMaddRel_mem (s : FloatShape) (op : VecFloatTernOp) (a b c r : V128)
    (h : vrelaxedMaddRel false p s op a b c r) : ∃ q, vrelaxedMaddRel true q s op a b c r :=
  ⟨.det, h⟩
theorem vbinopFloatRelaxedRel_mem (s : FloatShape) (op : VecFloatBinOp) (a b r : V128)
    (h : vbinopFloatRelaxedRel false p s op a b r) : ∃ q, vbinopFloatRelaxedRel true q s op a b r :=
  ⟨.det, h⟩
theorem vrelaxedTruncRel_mem (sx : Signedness) (src : FloatShape) (a r : V128)
    (h : vrelaxedTruncRel false p sx src a r) : ∃ q, vrelaxedTruncRel true q sx src a r :=
  ⟨.det, by rw [← vrelaxedTruncRel_false p]; exact h⟩
theorem vbinopIntRelaxed_mem (s : IntShape) (op : VecIntBinOp) (a b : V128) :
    ∃ q, vbinopIntRelaxed true q s op a b = vbinopIntRelaxed false p s op a b := ⟨.det, rfl⟩
theorem vrelaxedLaneselect_mem (s : IntShape) (a b c : V128) :
    ∃ q, vrelaxedLaneselect true q s a b c = vrelaxedLaneselect false p s a b c := ⟨.det, rfl⟩
theorem vrelaxedSwizzle_mem (a b : V128) :
    ∃ q, vrelaxedSwizzle true q a b = vrelaxedSwizzle false p a b := ⟨.det, rfl⟩
theorem vrelaxedDot_mem (a b : V128) :
    ∃ q, vrelaxedDot true q a b = vrelaxedDot false p a b := ⟨.det, rfl⟩
theorem vrelaxedDotAdd_mem (a b c : V128) :
    ∃ q, vrelaxedDotAdd true q a b c = vrelaxedDotAdd false p a b c := ⟨.det, rfl⟩

end Profile

/-! ## Agreement of the deterministic profile with the non-relaxed operators -/

theorem frelaxedMin_false_nonspecial (p : RelaxedParams) (t : FloatType) (a b : FloatValue t) :
    frelaxedMin false p t a b = floatBinOpRel t .min a b := by
  unfold frelaxedMin; split_ifs <;> rfl

theorem frelaxedMax_false_eq (p : RelaxedParams) (t : FloatType) (a b : FloatValue t) :
    frelaxedMax false p t a b = floatBinOpRel t .max a b := by
  unfold frelaxedMax; split_ifs <;> rfl

/-- Deterministic relaxed min/max coincide with `min`/`max`. -/
theorem vbinopFloatRelaxedRel_false_min (p : RelaxedParams) (s : FloatShape) (a b : V128) :
    vbinopFloatRelaxedRel false p s .relaxedMin a b = vbinopFloatRel s .min a b := by
  have h : frelaxedMin false p s.floatType = fun x y => floatBinOpRel s.floatType .min x y :=
    funext₂ fun x y => frelaxedMin_false_nonspecial p _ x y
  funext r
  show invLanesSet _ (lanesRel2 (frelaxedMin false p s.floatType) _ _) r =
    invLanesSet _ (lanesRel2 (floatBinOpRel s.floatType .min) _ _) r
  rw [h]

theorem vbinopFloatRelaxedRel_false_max (p : RelaxedParams) (s : FloatShape) (a b : V128) :
    vbinopFloatRelaxedRel false p s .relaxedMax a b = vbinopFloatRel s .max a b := by
  have h : frelaxedMax false p s.floatType = fun x y => floatBinOpRel s.floatType .max x y :=
    funext₂ fun x y => frelaxedMax_false_eq p _ x y
  funext r
  show invLanesSet _ (lanesRel2 (frelaxedMax false p s.floatType) _ _) r =
    invLanesSet _ (lanesRel2 (floatBinOpRel s.floatType .max) _ _) r
  rw [h]

/-- Deterministic relaxed swizzle is `swizzle`. -/
theorem irelaxedSwizzleLane_false_eq {n : Nat} (p : RelaxedParams) (c : List (BitVec n))
    (i : BitVec n) : irelaxedSwizzleLane false p c i = iswizzleLane c i := by
  unfold irelaxedSwizzleLane iswizzleLane
  split_ifs with h
  · rfl
  all_goals simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt h)]

theorem vrelaxedSwizzle_false_eq (p : RelaxedParams) (a b : V128) :
    some (vrelaxedSwizzle false p a b) = vswizzlop .swizzle a b := by
  have h := funext₂ fun c i => irelaxedSwizzleLane_false_eq (n := 8) p c i
  simp only [vrelaxedSwizzle, vswizzlop, IntShape.laneWidth] at h ⊢
  rw [h]

/-- Deterministic relaxed laneselect is lane-wise `bitselect`. -/
theorem irelaxedLaneselect_false_eq {n : Nat} (p : RelaxedParams) (a b c : BitVec n) :
    irelaxedLaneselect false p a b c = ibitselect a b c := rfl

/-- Deterministic relaxed trunc is `trunc_sat` (lane-wise). -/
theorem relaxedTrunc_false_iff (p : RelaxedParams) (t : FloatType) (sx : Signedness)
    (x : FloatValue t) (r : IntValue .i32) :
    relaxedTrunc false p t sx x r ↔ r = truncSatFloat t .i32 sx x := by
  unfold relaxedTrunc
  cases hx : truncFloat t .i32 sx x with
  | ok y =>
    show r = y ↔ _
    rw [truncSatFloat_agrees t .i32 sx x y hx]
  | error e => cases sx <;> exact Iff.rfl

/-- Deterministic relaxed q15mulr is `q15mulr_sat_s` on i16 lanes. -/
theorem irelaxedQ15mulr_false_eq (p : RelaxedParams) (a b : BitVec 16) :
    irelaxedQ15mulr false p a b = iq15mulrSatS a b := by
  unfold irelaxedQ15mulr
  split
  next h => obtain ⟨rfl, rfl⟩ := h; rw [relaxed2_false]; decide
  next => rfl

/-- Deterministic relaxed madd is the unfused `fadd(fmul(..))`. -/
theorem frelaxedMadd_false_eq (p : RelaxedParams) (t : FloatType) (a b c r : FloatValue t) :
    frelaxedMadd false p t a b c r ↔
      ∃ m, floatBinOpRel t .mul a b m ∧ floatBinOpRel t .add m c r := Iff.rfl

/-! ## Examples -/

example : irelaxedQ15mulr true { iq15mulr := 1 } (0x8000#16) (0x8000#16) = 0x8000#16 := by decide
example : irelaxedQ15mulr false { iq15mulr := 1 } (0x8000#16) (0x8000#16) = 0x7fff#16 := by decide
example : irelaxedLaneselect true { laneselect := 1 } (0xff#8) (0x00#8) (0x81#8) = 0xff#8 := by decide
example : irelaxedLaneselect false { laneselect := 1 } (0xff#8) (0x00#8) (0x81#8) = 0x81#8 := by decide

end Silmaril.Wasm.Numerics
