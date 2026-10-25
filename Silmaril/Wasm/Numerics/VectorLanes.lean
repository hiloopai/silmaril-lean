module

public import Silmaril.Wasm.Numerics.Float
public import Mathlib.Data.List.Forall2

@[expose] public section

/-!
# v128 lane plumbing

Spec `$lanes_` / `$inv_lanes_` (3.2-numerics.vector, declared `builtin`): a
`v128` value is split little-endian into `M` lanes of `N` bits, lane `0`
occupying the least significant bits. Lanes are carried as `BitVec N` for both
integer and floating shapes (float lanes are raw bit patterns, as in
`Numerics.Float`). Both round trips are proven arithmetically on `Nat`.
-/

namespace Silmaril.Wasm.Numerics

abbrev V128 := BitVec 128

/-- Little-endian lane split of a natural number into `m` lanes of `w` bits. -/
def lanesNat (w : Nat) : Nat → Nat → List (BitVec w)
  | 0, _ => []
  | m + 1, n => BitVec.ofNat w n :: lanesNat w m (n / 2 ^ w)

/-- Little-endian lane join into a natural number. -/
def joinNat (w : Nat) : List (BitVec w) → Nat
  | [] => 0
  | l :: ls => l.toNat + 2 ^ w * joinNat w ls

/-- `$lanes_` at lane width `w` and lane count `m`. -/
def lanesW (w m : Nat) (v : V128) : List (BitVec w) := lanesNat w m v.toNat

/-- `$inv_lanes_` at lane width `w`. -/
def invLanesW (w : Nat) (ls : List (BitVec w)) : V128 := BitVec.ofNat 128 (joinNat w ls)

@[simp] theorem length_lanesNat (w m n : Nat) : (lanesNat w m n).length = m := by
  induction m generalizing n with
  | zero => rfl
  | succ m ih => simp [lanesNat, ih]

@[simp] theorem length_lanesW (w m : Nat) (v : V128) : (lanesW w m v).length = m :=
  length_lanesNat _ _ _

theorem joinNat_lt (w : Nat) (ls : List (BitVec w)) : joinNat w ls < 2 ^ (w * ls.length) := by
  induction ls with
  | nil => simp [joinNat]
  | cons l ls ih =>
    simp only [joinNat, List.length_cons, Nat.mul_succ, Nat.pow_add]
    have hl := l.isLt
    have : 2 ^ w * joinNat w ls + 2 ^ w ≤ 2 ^ w * 2 ^ (w * ls.length) := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ ih
    rw [Nat.mul_comm (2 ^ (w * ls.length))]
    omega

theorem lanesNat_joinNat (w : Nat) (ls : List (BitVec w)) :
    lanesNat w ls.length (joinNat w ls) = ls := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    have hl := l.isLt
    have hp : 0 < 2 ^ w := Nat.two_pow_pos w
    simp only [List.length_cons, lanesNat, joinNat]
    congr 1
    · apply BitVec.eq_of_toNat_eq
      simp only [BitVec.toNat_ofNat]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hl]
    · rw [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hl, Nat.zero_add, ih]

theorem joinNat_lanesNat (w m n : Nat) :
    joinNat w (lanesNat w m n) = n % 2 ^ (w * m) := by
  induction m generalizing n with
  | zero => simp [lanesNat, joinNat, Nat.mod_one]
  | succ m ih =>
    simp only [lanesNat, joinNat, ih, BitVec.toNat_ofNat, Nat.mul_succ, Nat.pow_add]
    rw [Nat.mul_comm (2 ^ (w * m)) (2 ^ w), Nat.mod_mul]

/-- `inv_lanes (lanes v) = v` whenever the shape fills the 128 bits. -/
theorem invLanesW_lanesW {w m : Nat} (h : w * m = 128) (v : V128) :
    invLanesW w (lanesW w m v) = v := by
  apply BitVec.eq_of_toNat_eq
  simp only [invLanesW, lanesW, BitVec.toNat_ofNat, joinNat_lanesNat, h, Nat.mod_mod]
  exact Nat.mod_eq_of_lt v.isLt

/-- `lanes (inv_lanes ls) = ls` for a lane list of the right length. -/
theorem lanesW_invLanesW {w m : Nat} (h : w * m ≤ 128) (ls : List (BitVec w))
    (hl : ls.length = m) : lanesW w m (invLanesW w ls) = ls := by
  subst hl
  have hlt : joinNat w ls < 2 ^ 128 :=
    Nat.lt_of_lt_of_le (joinNat_lt w ls) (Nat.pow_le_pow_right (by decide) h)
  simp only [lanesW, invLanesW, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  exact lanesNat_joinNat w ls

theorem lanesW_injective {w m : Nat} (h : w * m = 128) {v u : V128}
    (e : lanesW w m v = lanesW w m u) : v = u := by
  rw [← invLanesW_lanesW h v, e, invLanesW_lanesW h u]

/-- Lane `i` is the bit field `[w*i, w*i + w)`. -/
theorem getElem_lanesNat (w m n i : Nat) (hi : i < m) :
    (lanesNat w m n)[i]'(by simp [hi]) = BitVec.ofNat w (n / 2 ^ (w * i)) := by
  induction m generalizing n i with
  | zero => omega
  | succ m ih =>
    cases i with
    | zero => simp [lanesNat]
    | succ i =>
      simp only [lanesNat, List.getElem_cons_succ]
      rw [ih _ _ (by omega), Nat.div_div_eq_div_mul, ← Nat.pow_add, Nat.mul_succ, Nat.add_comm w]

theorem getElem_lanesW (w m : Nat) (v : V128) (i : Nat) (hi : i < m) :
    (lanesW w m v)[i]'(by simp [hi]) = v.extractLsb' (w * i) w := by
  apply BitVec.eq_of_toNat_eq
  simp only [lanesW, getElem_lanesNat _ _ _ _ hi, BitVec.toNat_ofNat, BitVec.extractLsb'_toNat,
    Nat.shiftRight_eq_div_pow]

/-! ## Shapes -/

def _root_.Silmaril.Wasm.FloatShape.floatType : FloatShape → FloatType
  | .f32x4 => .f32 | .f64x2 => .f64

/-- The integer shape with the same lane layout as a float shape (used by `vrelop`). -/
def _root_.Silmaril.Wasm.FloatShape.intShape : FloatShape → IntShape
  | .f32x4 => .i32x4 | .f64x2 => .i64x2

theorem _root_.Silmaril.Wasm.IntShape.size (s : IntShape) : s.laneWidth * s.lanes = 128 := by cases s <;> rfl
theorem _root_.Silmaril.Wasm.FloatShape.size (s : FloatShape) : s.floatType.width * s.lanes = 128 := by cases s <;> rfl
theorem _root_.Silmaril.Wasm.Shape.size (s : Shape) : s.laneWidth * s.lanes = 128 := by cases s <;> rename_i s <;> cases s <;> rfl

/-- Integer lanes. -/
abbrev ILane (s : IntShape) := BitVec s.laneWidth
/-- Float lanes, typed as `Numerics.FloatValue` so scalar float operations apply directly. -/
abbrev FLane (s : FloatShape) := FloatValue s.floatType

def _root_.Silmaril.Wasm.IntShape.lanesOf (s : IntShape) (v : V128) : List (ILane s) := lanesW s.laneWidth s.lanes v
def _root_.Silmaril.Wasm.IntShape.invLanes (s : IntShape) (ls : List (ILane s)) : V128 := invLanesW s.laneWidth ls
def _root_.Silmaril.Wasm.FloatShape.lanesOf (s : FloatShape) (v : V128) : List (FLane s) :=
  lanesW s.floatType.width s.lanes v
def _root_.Silmaril.Wasm.FloatShape.invLanes (s : FloatShape) (ls : List (FLane s)) : V128 :=
  invLanesW s.floatType.width ls
/-- Generic `$lanes_` over any shape. -/
def _root_.Silmaril.Wasm.Shape.lanesOf (s : Shape) (v : V128) : List (BitVec s.laneWidth) := lanesW s.laneWidth s.lanes v
def _root_.Silmaril.Wasm.Shape.invLanes (s : Shape) (ls : List (BitVec s.laneWidth)) : V128 := invLanesW s.laneWidth ls

@[simp] theorem _root_.Silmaril.Wasm.IntShape.length_lanesOf (s : IntShape) (v : V128) : (s.lanesOf v).length = s.lanes :=
  length_lanesW _ _ _
@[simp] theorem _root_.Silmaril.Wasm.FloatShape.length_lanesOf (s : FloatShape) (v : V128) :
    (s.lanesOf v).length = s.lanes := length_lanesW _ _ _
@[simp] theorem _root_.Silmaril.Wasm.Shape.length_lanesOf (s : Shape) (v : V128) : (s.lanesOf v).length = s.lanes :=
  length_lanesW _ _ _

@[simp] theorem _root_.Silmaril.Wasm.IntShape.invLanes_lanesOf (s : IntShape) (v : V128) : s.invLanes (s.lanesOf v) = v :=
  invLanesW_lanesW s.size v
@[simp] theorem _root_.Silmaril.Wasm.FloatShape.invLanes_lanesOf (s : FloatShape) (v : V128) :
    s.invLanes (s.lanesOf v) = v := invLanesW_lanesW s.size v
@[simp] theorem _root_.Silmaril.Wasm.Shape.invLanes_lanesOf (s : Shape) (v : V128) : s.invLanes (s.lanesOf v) = v :=
  invLanesW_lanesW s.size v

theorem _root_.Silmaril.Wasm.IntShape.lanesOf_invLanes (s : IntShape) (ls : List (ILane s)) (h : ls.length = s.lanes) :
    s.lanesOf (s.invLanes ls) = ls := lanesW_invLanesW (Nat.le_of_eq s.size) ls h
theorem _root_.Silmaril.Wasm.FloatShape.lanesOf_invLanes (s : FloatShape) (ls : List (FLane s))
    (h : ls.length = s.lanes) : s.lanesOf (s.invLanes ls) = ls :=
  lanesW_invLanesW (Nat.le_of_eq s.size) ls h
theorem _root_.Silmaril.Wasm.Shape.lanesOf_invLanes (s : Shape) (ls : List (BitVec s.laneWidth))
    (h : ls.length = s.lanes) : s.lanesOf (s.invLanes ls) = ls :=
  lanesW_invLanesW (Nat.le_of_eq s.size) ls h

/-- Spec `$setproduct_` followed by `$inv_lanes_`: the vectors whose lanes are
drawn from the lane-wise result sets. -/
def invLanesSet (w : Nat) (P : List (BitVec w) → Prop) (r : V128) : Prop :=
  ∃ c, P c ∧ r = invLanesW w c

/-- Lane-wise relation form of a set product: result `r` is allowed iff its
lanes are pointwise allowed. Requires the relation to be witnessed lane-wise. -/
theorem invLanesSet_forall₂_iff {α : Type} {w m : Nat} (h : w * m = 128) (xs : List α)
    (hx : xs.length = m) (R : α → BitVec w → Prop) (r : V128) :
    invLanesSet w (List.Forall₂ R xs) r ↔ List.Forall₂ R xs (lanesW w m r) := by
  constructor
  · rintro ⟨c, hc, rfl⟩
    rw [lanesW_invLanesW (Nat.le_of_eq h) c (by rw [← hc.length_eq, hx])]
    exact hc
  · intro hr
    exact ⟨_, hr, (invLanesW_lanesW h r).symm⟩

end Silmaril.Wasm.Numerics
