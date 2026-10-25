module

public import Silmaril.Wasm.Numerics.VectorLanes

@[expose] public section

/-!
# Deterministic v128 numerics (spec 3.2-numerics.vector)

Lane-wise transcription of the spec's vector functions. Integer operators are
deterministic functions. Floating operators whose scalar counterpart is
NaN-nondeterministic are given as relations `V128 → Prop` built from the
existing scalar relations `floatUnOpRel`/`floatBinOpRel`/`convertRel`: the
allowed result set is the spec's `$setproduct_` of the lane sets, mapped
through `$inv_lanes_` (`invLanesSet`). A canonical executable function is
provided alongside, with a `*_self` lemma placing it in the relation.

Relaxed operators (`relaxed_*`) are *not* handled here: the dispatchers
return `none`/`False` on them. They live in `Numerics/Relaxed.lean`.
-/

namespace Silmaril.Wasm.Numerics

/-! ## Local width-parametric integer lane helpers

Kept in `VecLane` so they can be deduplicated against a later width-parametric
integer library. -/

namespace VecLane

/-- `$signed_` / plain unsigned interpretation. -/
def toIntSx {n : Nat} : Signedness → BitVec n → Int
  | .signed, x => x.toInt
  | .unsigned, x => x.toNat

/-- `$sat_s_`. -/
def satS (n : Nat) (i : Int) : Int := max (-(2 ^ (n - 1) : Int)) (min i (2 ^ (n - 1) - 1))
/-- `$sat_u_`. -/
def satU (n : Nat) (i : Int) : Int := max 0 (min i (2 ^ n - 1))

def sat (n : Nat) : Signedness → Int → Int
  | .signed => satS n
  | .unsigned => satU n

def ineg {n : Nat} (x : BitVec n) : BitVec n := -x
def iabs {n : Nat} (x : BitVec n) : BitVec n := if 0 ≤ x.toInt then x else -x
def ipopcnt {n : Nat} (x : BitVec n) : BitVec n := x.cpop

def iaddSat {n : Nat} (sx : Signedness) (x y : BitVec n) : BitVec n :=
  BitVec.ofInt n (sat n sx (toIntSx sx x + toIntSx sx y))
def isubSat {n : Nat} (sx : Signedness) (x y : BitVec n) : BitVec n :=
  BitVec.ofInt n (sat n sx (toIntSx sx x - toIntSx sx y))
def imin {n : Nat} (sx : Signedness) (x y : BitVec n) : BitVec n :=
  if toIntSx sx x ≤ toIntSx sx y then x else y
def imax {n : Nat} (sx : Signedness) (x y : BitVec n) : BitVec n :=
  if toIntSx sx x ≥ toIntSx sx y then x else y
/-- `$iavgr_u`: `truncz((i1 + i2 + 1) / 2)`. -/
def iavgrU {n : Nat} (x y : BitVec n) : BitVec n := BitVec.ofNat n ((x.toNat + y.toNat + 1) / 2)
/-- `$iq15mulr_sat_s`: `sat_s(ishr_s(i1 * i2 + 2^14, 15))` on signed values
(arithmetic shift = floor division, which `Int./` is for positive divisors). -/
def iq15mulrSatS {n : Nat} (x y : BitVec n) : BitVec n :=
  BitVec.ofInt n (satS n ((x.toInt * y.toInt + 2 ^ 14) / 2 ^ 15))

def iandnot {n : Nat} (x y : BitVec n) : BitVec n := x &&& ~~~y
/-- `$ibitselect_`. -/
def ibitselect {n : Nat} (x y m : BitVec n) : BitVec n := (x &&& m) ||| (y &&& ~~~m)

/-- `$extend__(1, N, S, b)` of a boolean. -/
def ibool {n : Nat} (b : Bool) : BitVec n := if b then BitVec.allOnes n else 0

def irelop {n : Nat} : IntRelOp → BitVec n → BitVec n → Bool
  | .eq, x, y => x == y
  | .ne, x, y => x != y
  | .lt sx, x, y => decide (toIntSx sx x < toIntSx sx y)
  | .gt sx, x, y => decide (toIntSx sx x > toIntSx sx y)
  | .le sx, x, y => decide (toIntSx sx x ≤ toIntSx sx y)
  | .ge sx, x, y => decide (toIntSx sx x ≥ toIntSx sx y)

/-- `$ishl_`: count taken modulo the lane width. -/
def ishl {n : Nat} (x : BitVec n) (k : BitVec 32) : BitVec n := x <<< (k.toNat % n)
/-- `$ishr_`. -/
def ishr {n : Nat} : Signedness → BitVec n → BitVec 32 → BitVec n
  | .unsigned, x, k => x >>> (k.toNat % n)
  | .signed, x, k => x.sshiftRight (k.toNat % n)

/-- `$extend__(M, N, sx, i)`. -/
def extend {m : Nat} (n : Nat) : Signedness → BitVec m → BitVec n
  | .signed, x => x.signExtend n
  | .unsigned, x => x.setWidth n

/-- `$narrow__(M, N, sx, i)`: saturate the *signed* interpretation. -/
def narrow {m : Nat} (n : Nat) (sx : Signedness) (x : BitVec m) : BitVec n :=
  BitVec.ofInt n (sat n sx x.toInt)

/-- `$ivadd_pairwise_`. -/
def addPairwise {n : Nat} : List (BitVec n) → List (BitVec n)
  | a :: b :: rest => (a + b) :: addPairwise rest
  | _ => []

/-- `$ivmul_`. -/
def mulLanes {n : Nat} (xs ys : List (BitVec n)) : List (BitVec n) := List.zipWith (· * ·) xs ys

/-- `$ivdot_`. -/
def dot {n : Nat} (xs ys : List (BitVec n)) : List (BitVec n) := addPairwise (mulLanes xs ys)

/-- `$ivdot_sat_`. -/
def satPairwise {n : Nat} : List (BitVec n) → List (BitVec n)
  | a :: b :: rest => iaddSat .signed a b :: satPairwise rest
  | _ => []

def dotSat {n : Nat} (xs ys : List (BitVec n)) : List (BitVec n) := satPairwise (mulLanes xs ys)

/-- `$half(half, i, j)`. -/
def half : Half → Nat → Nat → Nat
  | .low, i, _ => i
  | .high, _, j => j

/-- Spec slice `l[i : k]`. -/
def slice {α : Type} (l : List α) (i k : Nat) : List α := (l.drop i).take k

end VecLane

open VecLane

/-! ## Generic lane combinators and set products -/

theorem forall₂_map_self {α β : Type} {R : α → β → Prop} (f : α → β) (h : ∀ a, R a (f a)) :
    ∀ l : List α, List.Forall₂ R l (l.map f)
  | [] => .nil
  | a :: l => .cons (h a) (forall₂_map_self f h l)

/-- Lane-wise relation, unary. -/
def lanesRel1 {α β : Type} (R : α → β → Prop) (xs : List α) : List β → Prop := List.Forall₂ R xs
/-- Lane-wise relation, binary. -/
def lanesRel2 {α β : Type} (R : α → α → β → Prop) (xs ys : List α) : List β → Prop :=
  List.Forall₂ (fun p z => R p.1 p.2 z) (xs.zip ys)
/-- Lane-wise relation, ternary. -/
def lanesRel3 {α β : Type} (R : α → α → α → β → Prop) (xs ys zs : List α) : List β → Prop :=
  List.Forall₂ (fun p z => R p.1 p.2.1 p.2.2 z) (xs.zip (ys.zip zs))

/-! ## Bitwise v128 operations -/

def vvunop : VecUnOp → V128 → V128
  | .not, v => ~~~v

def vvbinop : VecBinOp → V128 → V128 → V128
  | .and, v, w => v &&& w
  | .andnot, v, w => iandnot v w
  | .or, v, w => v ||| w
  | .xor, v, w => v ^^^ w

def vvternop : VecTernOp → V128 → V128 → V128 → V128
  | .bitselect, v, w, m => ibitselect v w m

/-- `any_true` is `$inez_(128, v)`. -/
def vvtestop : VecTestOp → V128 → BitVec 32
  | .anyTrue, v => bool32 (v != 0)

/-! ## Integer lane-wise operations -/

def ivunop (s : IntShape) (f : ILane s → ILane s) (v : V128) : V128 :=
  s.invLanes ((s.lanesOf v).map f)

def ivbinop (s : IntShape) (f : ILane s → ILane s → ILane s) (v w : V128) : V128 :=
  s.invLanes (List.zipWith f (s.lanesOf v) (s.lanesOf w))

def vunopInt (s : IntShape) : VecIntUnOp → V128 → V128
  | .abs => ivunop s iabs
  | .neg => ivunop s ineg
  | .popcnt => ivunop s ipopcnt

/-- `none` exactly on the relaxed operator `relaxed_q15mulr_s`. -/
def vbinopInt (s : IntShape) : VecIntBinOp → V128 → V128 → Option V128
  | .add, v, w => some (ivbinop s (· + ·) v w)
  | .sub, v, w => some (ivbinop s (· - ·) v w)
  | .mul, v, w => some (ivbinop s (· * ·) v w)
  | .addSat sx, v, w => some (ivbinop s (iaddSat sx) v w)
  | .subSat sx, v, w => some (ivbinop s (isubSat sx) v w)
  | .min sx, v, w => some (ivbinop s (imin sx) v w)
  | .max sx, v, w => some (ivbinop s (imax sx) v w)
  | .avgrU, v, w => some (ivbinop s iavgrU v w)
  | .q15mulrSatS, v, w => some (ivbinop s iq15mulrSatS v w)
  | .relaxedQ15mulrS, _, _ => none

def vrelopInt (s : IntShape) (op : IntRelOp) (v w : V128) : V128 :=
  ivbinop s (fun x y => ibool (irelop op x y)) v w

def vshiftop (s : IntShape) (op : VecShiftOp) (v : V128) (k : BitVec 32) : V128 :=
  match op with
  | .shl => ivunop s (fun x => ishl x k) v
  | .shr sx => ivunop s (fun x => ishr sx x k) v

/-- Pack booleans little-endian into a natural number. -/
def bitsNat : List Bool → Nat
  | [] => 0
  | b :: bs => b.toNat + 2 * bitsNat bs

/-- `$ivbitmaskop_`: bit `i` of the result is the sign bit of lane `i`. -/
def vbitmask (s : IntShape) (v : V128) : BitVec 32 :=
  BitVec.ofNat 32 (bitsNat ((s.lanesOf v).map fun x => decide (x.toInt < 0)))

/-- `all_true`: `$prod($inez_(N, i)*)`. -/
def vtestop (s : IntShape) (v : V128) : BitVec 32 :=
  bool32 ((s.lanesOf v).all fun x => x != 0)

/-- `$iswizzle_lane_`. -/
def iswizzleLane {n : Nat} (c : List (BitVec n)) (i : BitVec n) : BitVec n := c.getD i.toNat 0

/-- `swizzle` (i8x16). `none` on `relaxed_swizzle`. -/
def vswizzlop : VecSwizzleOp → V128 → V128 → Option V128
  | .swizzle, v, w =>
    some (IntShape.i8x16.invLanes ((IntShape.i8x16.lanesOf w).map
      (iswizzleLane (IntShape.i8x16.lanesOf v))))
  | .relaxedSwizzle, _, _ => none

/-- `$ivshufflop_` (i8x16); lane indices are validated `< 32`. -/
def vshuffle (idx : List Nat) (v w : V128) : V128 :=
  IntShape.i8x16.invLanes (idx.map fun i =>
    (IntShape.i8x16.lanesOf v ++ IntShape.i8x16.lanesOf w).getD i 0)

/-- `vsplat`: `$lpacknum_` wraps the unpacked operand to the lane width. -/
def vsplat (s : Shape) {n : Nat} (c : BitVec n) : V128 :=
  s.invLanes (List.replicate s.lanes (c.setWidth s.laneWidth))

/-- `vextract_lane` for unpacked lanes. -/
def vextractLane (s : Shape) (i : Nat) (v : V128) : BitVec s.laneWidth := (s.lanesOf v).getD i 0

/-- `vextract_lane` for packed lanes (i8x16, i16x8): extend to i32. -/
def vextractLanePacked (s : IntShape) (sx : Signedness) (i : Nat) (v : V128) : BitVec 32 :=
  extend 32 sx ((s.lanesOf v).getD i 0)

/-- `vreplace_lane`. -/
def vreplaceLane (s : Shape) (i : Nat) {n : Nat} (c : BitVec n) (v : V128) : V128 :=
  s.invLanes ((s.lanesOf v).set i (c.setWidth s.laneWidth))

/-- `vnarrow`: source shape `s1`, target shape `s2` (both integer). -/
def vnarrow (s1 s2 : IntShape) (sx : Signedness) (v w : V128) : V128 :=
  s2.invLanes ((s1.lanesOf v).map (narrow s2.laneWidth sx) ++
    (s1.lanesOf w).map (narrow s2.laneWidth sx))

/-- `$ivextunop__`. -/
def ivextunop (s1 s2 : IntShape) (f : List (ILane s2) → List (ILane s2)) (sx : Signedness)
    (v : V128) : V128 :=
  s2.invLanes (f ((s1.lanesOf v).map (extend s2.laneWidth sx)))

/-- `$ivextbinop__`. -/
def ivextbinop (s1 s2 : IntShape) (f : List (ILane s2) → List (ILane s2) → List (ILane s2))
    (sx1 sx2 : Signedness) (i k : Nat) (v w : V128) : V128 :=
  s2.invLanes (f ((slice (s1.lanesOf v) i k).map (extend s2.laneWidth sx1))
    ((slice (s1.lanesOf w) i k).map (extend s2.laneWidth sx2)))

def vextunop (s1 s2 : IntShape) : VecExtUnOp → V128 → V128
  | .extaddPairwise sx => ivextunop s1 s2 addPairwise sx

/-- `none` exactly on `relaxed_dot`. -/
def vextbinop (s1 s2 : IntShape) : VecExtBinOp → V128 → V128 → Option V128
  | .extmul h sx, v, w => some (ivextbinop s1 s2 mulLanes sx sx (half h 0 s2.lanes) s2.lanes v w)
  | .dotS, v, w => some (ivextbinop s1 s2 dot .signed .signed 0 s1.lanes v w)
  | .relaxedDotS, _, _ => none

/-! ## Floating lane-wise operations -/

/-- Allowed results of `$fvunop_`. -/
def vunopFloatRel (s : FloatShape) (op : FloatUnOp) (v r : V128) : Prop :=
  invLanesSet _ (lanesRel1 (floatUnOpRel s.floatType op) (s.lanesOf v)) r

/-- Canonical-NaN choice for `$fvunop_`. -/
def vunopFloat (s : FloatShape) (op : FloatUnOp) (v : V128) : V128 :=
  s.invLanes ((s.lanesOf v).map (floatUnOp s.floatType op))

/-- `$fpmin_`: `z2` if `z2 < z1`, else `z1` (bit-exact). -/
def fpmin (t : FloatType) (x y : FloatValue t) : FloatValue t :=
  if floatRelOp t .lt y x = 1 then y else x
/-- `$fpmax_`: `z2` if `z1 < z2`, else `z1` (bit-exact). -/
def fpmax (t : FloatType) (x y : FloatValue t) : FloatValue t :=
  if floatRelOp t .lt x y = 1 then y else x

/-- Lane relation of a non-relaxed float binary vector operator. -/
def floatVecBinRel (t : FloatType) : VecFloatBinOp → Option (FloatValue t → FloatValue t → FloatValue t → Prop)
  | .add => some (floatBinOpRel t .add)
  | .sub => some (floatBinOpRel t .sub)
  | .mul => some (floatBinOpRel t .mul)
  | .div => some (floatBinOpRel t .div)
  | .min => some (floatBinOpRel t .min)
  | .max => some (floatBinOpRel t .max)
  | .pmin => some fun x y z => z = fpmin t x y
  | .pmax => some fun x y z => z = fpmax t x y
  | .relaxedMin | .relaxedMax => none

/-- Canonical lane function of a non-relaxed float binary vector operator. -/
def floatVecBin (t : FloatType) : VecFloatBinOp → Option (FloatValue t → FloatValue t → FloatValue t)
  | .add => some (floatBinOp t .add)
  | .sub => some (floatBinOp t .sub)
  | .mul => some (floatBinOp t .mul)
  | .div => some (floatBinOp t .div)
  | .min => some (floatBinOp t .min)
  | .max => some (floatBinOp t .max)
  | .pmin => some (fpmin t)
  | .pmax => some (fpmax t)
  | .relaxedMin | .relaxedMax => none

/-- Allowed results of `$fvbinop_` (False for relaxed operators). -/
def vbinopFloatRel (s : FloatShape) (op : VecFloatBinOp) (v w r : V128) : Prop :=
  match floatVecBinRel s.floatType op with
  | none => False
  | some R => invLanesSet _ (lanesRel2 R (s.lanesOf v) (s.lanesOf w)) r

def vbinopFloat (s : FloatShape) (op : VecFloatBinOp) (v w : V128) : Option V128 :=
  (floatVecBin s.floatType op).map fun f => s.invLanes (List.zipWith f (s.lanesOf v) (s.lanesOf w))

/-- Scalar float comparison as a boolean. -/
def floatRelBool : (t : FloatType) → FloatRelOp → FloatValue t → FloatValue t → Bool
  | .f32, op, x, y => floatRelOp32 op (asF32 x) (asF32 y)
  | .f64, op, x, y => floatRelOp64 op (asF64 x) (asF64 y)

/-- `$fvrelop_`: all-ones / zero lanes of the same width. -/
def vrelopFloat (s : FloatShape) (op : FloatRelOp) (v w : V128) : V128 :=
  s.invLanes (List.zipWith (fun x y => ibool (floatRelBool s.floatType op x y))
    (s.lanesOf v) (s.lanesOf w))

/-! ## Conversions (`$vcvtop__`) -/

/-- Canonical-NaN deterministic `$vcvtop__`. -/
def vcvtop : VecConvertOp → (src tgt : Shape) → V128 → Option V128
  | .extend h sx, .int s, .int t, v =>
    if t.laneWidth = 2 * s.laneWidth then
      some (t.invLanes ((slice (s.lanesOf v) (half h 0 t.lanes) t.lanes).map (extend t.laneWidth sx)))
    else none
  | .convert none sx, .int .i32x4, .float .f32x4, v =>
    some (FloatShape.f32x4.invLanes ((IntShape.i32x4.lanesOf v).map (convertInt .i32 .f32 sx)))
  | .convert (some .low) sx, .int .i32x4, .float .f64x2, v =>
    some (FloatShape.f64x2.invLanes
      ((slice (IntShape.i32x4.lanesOf v) 0 2).map (convertInt .i32 .f64 sx)))
  -- `$convert__(16, 32, sx, c)`: widening the 16-bit lane to 32 bits (by `sx`)
  -- preserves its `sx`-interpretation, so this is exactly the spec's conversion.
  | .convert (some .low) sx, .int .i16x8, .float .f32x4, v =>
    some (FloatShape.f32x4.invLanes
      ((slice (IntShape.i16x8.lanesOf v) 0 4).map
        (fun x => convertInt .i32 .f32 sx (extend 32 sx x))))
  | .truncSat sx false, .float .f32x4, .int .i32x4, v =>
    some (IntShape.i32x4.invLanes ((FloatShape.f32x4.lanesOf v).map (truncSatFloat .f32 .i32 sx)))
  | .truncSat sx true, .float .f64x2, .int .i32x4, v =>
    some (IntShape.i32x4.invLanes
      ((FloatShape.f64x2.lanesOf v).map (truncSatFloat .f64 .i32 sx) ++ [0, 0]))
  | .demoteZero, .float .f64x2, .float .f32x4, v =>
    some (FloatShape.f32x4.invLanes
      ((FloatShape.f64x2.lanesOf v).map (fun x => (asF64 x).toF32.bits.toBitVec) ++ [0, 0]))
  | .promoteLow, .float .f32x4, .float .f64x2, v =>
    some (FloatShape.f64x2.invLanes
      ((slice (FloatShape.f32x4.lanesOf v) 0 2).map (fun x => (asF32 x).toF64.bits.toBitVec)))
  | _, _, _, _ => none

/-- Allowed results of `$vcvtop__`. Only `demote_zero`/`promote_low` are
NaN-nondeterministic (via the scalar `convertRel`); every other conversion is
the deterministic `vcvtop`. No result (`False`) on invalid shape pairs and on
`relaxed_trunc` (see `Relaxed.lean`). -/
def vcvtopRel (op : VecConvertOp) (src tgt : Shape) (v r : V128) : Prop :=
  match op, src, tgt with
  | .demoteZero, .float .f64x2, .float .f32x4 =>
    ∃ c : List (FloatValue .f32),
      List.Forall₂ (fun x y => convertRel .demote x (.ok y)) (FloatShape.f64x2.lanesOf v) c ∧
      r = FloatShape.f32x4.invLanes (c ++ [0, 0])
  | .promoteLow, .float .f32x4, .float .f64x2 =>
    ∃ c : List (FloatValue .f64),
      List.Forall₂ (fun x y => convertRel .promote x (.ok y))
        (slice (FloatShape.f32x4.lanesOf v) 0 2) c ∧
      r = FloatShape.f64x2.invLanes c
  | _, _, _ => vcvtop op src tgt v = some r

/-! ## Agreement lemmas -/

theorem vunopFloatRel_self (s : FloatShape) (op : FloatUnOp) (v : V128) :
    vunopFloatRel s op v (vunopFloat s op v) :=
  ⟨_, forall₂_map_self _ (floatUnOpRel_self _ op) _, rfl⟩

theorem zipWith_eq_map_zip {α β γ : Type} (f : α → β → γ) (xs : List α) (ys : List β) :
    List.zipWith f xs ys = (xs.zip ys).map fun p => f p.1 p.2 := by
  induction xs generalizing ys with
  | nil => rfl
  | cons x xs ih => cases ys <;> simp [ih]

theorem vbinopFloatRel_self (s : FloatShape) (op : VecFloatBinOp) (v w r : V128)
    (h : vbinopFloat s op v w = some r) : vbinopFloatRel s op v w r := by
  unfold vbinopFloat at h
  unfold vbinopFloatRel
  cases op <;> simp only [floatVecBin, floatVecBinRel, Option.map_some, Option.map_none,
    Option.some.injEq, reduceCtorEq] at h ⊢ <;> subst h <;> refine ⟨_, ?_, rfl⟩ <;>
    unfold lanesRel2 <;> rw [zipWith_eq_map_zip] <;>
    exact forall₂_map_self _ (fun p => by first
        | exact floatBinOpRel_self _ _ p.1 p.2
        | rfl) _

theorem vcvtopRel_self (op : VecConvertOp) (src tgt : Shape) (v r : V128)
    (h : vcvtop op src tgt v = some r) : vcvtopRel op src tgt v r := by
  unfold vcvtopRel
  split
  · obtain rfl := Option.some.inj h
    exact ⟨_, forall₂_map_self (fun x : FloatValue .f64 => (asF64 x).toF32.bits.toBitVec)
      (fun x => convertRel_self .demote x) _, rfl⟩
  · obtain rfl := Option.some.inj h
    exact ⟨_, forall₂_map_self (fun x : FloatValue .f32 => (asF32 x).toF64.bits.toBitVec)
      (fun x => convertRel_self .promote x) _, rfl⟩
  · exact h

/-- Lane-level characterization of the float set product. -/
theorem vunopFloatRel_iff (s : FloatShape) (op : FloatUnOp) (v r : V128) :
    vunopFloatRel s op v r ↔
      List.Forall₂ (floatUnOpRel s.floatType op) (s.lanesOf v) (s.lanesOf r) :=
  invLanesSet_forall₂_iff s.size _ (length_lanesW _ _ _) _ r

theorem lanesOf_ivunop (s : IntShape) (f : ILane s → ILane s) (v : V128) :
    s.lanesOf (ivunop s f v) = (s.lanesOf v).map f :=
  s.lanesOf_invLanes _ (by simp)

theorem lanesOf_vsplat (s : Shape) {n : Nat} (c : BitVec n) :
    s.lanesOf (vsplat s c) = List.replicate s.lanes (c.setWidth s.laneWidth) :=
  s.lanesOf_invLanes _ (by simp)

theorem vextractLane_vreplaceLane (s : Shape) (i : Nat) (hi : i < s.lanes) {n : Nat}
    (c : BitVec n) (v : V128) :
    vextractLane s i (vreplaceLane s i c v) = c.setWidth s.laneWidth := by
  unfold vextractLane vreplaceLane
  rw [s.lanesOf_invLanes _ (by simp)]
  simp [List.getD_eq_getElem?_getD, hi]

theorem vextractLane_vsplat (s : Shape) (i : Nat) (hi : i < s.lanes) {n : Nat} (c : BitVec n) :
    vextractLane s i (vsplat s c) = c.setWidth s.laneWidth := by
  unfold vextractLane
  rw [lanesOf_vsplat]
  simp [List.getD_eq_getElem?_getD, hi]

/-! ## Examples -/

example : vbinopInt .i8x16 .add (BitVec.allOnes 128) 0x01010101010101010101010101010101#128 =
    some 0 := by decide
example : vbitmask .i32x4 0x80000000_00000000_80000000_00000001#128 = 0b1010#32 := by decide
example : vshiftop .i16x8 .shl 0x0001#128 17#32 = 0x0002#128 := by decide
example : vnarrow .i16x8 .i8x16 .signed 0x0100#128 0#128 = 0x7f#128 := by decide
example : vextunop .i8x16 .i16x8 (.extaddPairwise .signed) 0xffff#128 = 0xfffe#128 := by decide

end Silmaril.Wasm.Numerics
