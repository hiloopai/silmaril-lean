module

public import Mathlib.Algebra.Order.Interval.Set.Instances
public import Mathlib.Algebra.Order.ZeroLEOne
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Order.Fin.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.LatticeIntervals

/-! Truth-value operations for the chain examples in the many-valued logic catalogue.
See `docs/projects/many-valued-logic-catalogue.md` for sources and signatures. -/

@[expose] public section

namespace Silmaril.Logic.ManyValuedCatalogue

namespace Goedel

variable {A : Type*} [LinearOrder A] [BoundedOrder A]

def and (x y : A) : A := min x y

def or (x y : A) : A := max x y

def imp (x y : A) : A := if x ≤ y then ⊤ else y

def neg (x : A) : A := imp x ⊥

def designated (x : A) : Prop := x = ⊤

end Goedel

/-- The finite grid of `n + 2` values. Index `i` represents `i / (n + 1)`. -/
abbrev Grid (n : ℕ) := Fin (n + 2)

namespace Grid

variable {n : ℕ}

def lukNeg (x : Grid n) : Grid n :=
  ⟨n + 1 - x.val, by omega⟩

def lukImp (x y : Grid n) : Grid n :=
  ⟨min (n + 1) (n + 1 + y.val - x.val), by omega⟩

/-- Strong conjunction, with a cut at zero. Weak conjunction is `min`. -/
def lukAnd (x y : Grid n) : Grid n :=
  ⟨x.val + y.val - (n + 1), by have := x.isLt; have := y.isLt; omega⟩

end Grid

/-- The closed unit interval over an ordered field. -/
abbrev UnitInterval (K : Type*) [Preorder K] [Zero K] [One K] := Set.Icc (0 : K) 1

namespace UnitInterval

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def lukNeg (x : UnitInterval K) : UnitInterval K :=
  ⟨1 - x.val, sub_nonneg.mpr x.2.2, sub_le_self _ x.2.1⟩

def lukImp (x y : UnitInterval K) : UnitInterval K :=
  ⟨min 1 (1 - x.val + y.val),
    le_min zero_le_one (add_nonneg (sub_nonneg.mpr x.2.2) y.2.1), min_le_left ..⟩

/-- Łukasiewicz strong conjunction. -/
def lukAnd (x y : UnitInterval K) : UnitInterval K :=
  ⟨max 0 (x.val + y.val - 1), le_max_left ..,
    max_le zero_le_one (sub_le_iff_le_add.mpr (add_le_add x.2.2 y.2.2))⟩

/-- Product strong conjunction. -/
def prodAnd (x y : UnitInterval K) : UnitInterval K :=
  ⟨x.val * y.val, mul_nonneg x.2.1 y.2.1,
    (mul_le_of_le_one_left y.2.1 x.2.2).trans y.2.2⟩

def prodImp (x y : UnitInterval K) : UnitInterval K :=
  if h : x ≤ y then ⊤
  else
    have hyx : y.val < x.val := lt_of_not_ge h
    have hx := y.2.1.trans_lt hyx
    ⟨y.val / x.val, div_nonneg y.2.1 hx.le, (div_le_one hx).mpr hyx.le⟩

def prodNeg (x : UnitInterval K) : UnitInterval K := prodImp x ⊥

/-- The meet defined from product conjunction and its residual. -/
def prodMeet (x y : UnitInterval K) : UnitInterval K := prodAnd x (prodImp x y)

/-- The equally spaced finite grid inside an ordered field's unit interval. -/
def ofGrid {n : ℕ} (x : Grid n) : UnitInterval K :=
  have hn : (0 : K) < (n : K) + 1 := add_pos_of_nonneg_of_pos (Nat.cast_nonneg _) zero_lt_one
  ⟨(x.val : K) / ((n : K) + 1),
    div_nonneg (Nat.cast_nonneg _) hn.le,
    (div_le_one hn).mpr (by
      rw [← Nat.cast_one, ← Nat.cast_add, Nat.cast_le]
      omega)⟩

/-- The rational degrees as real degrees. -/
def ofRat (x : UnitInterval ℚ) : UnitInterval ℝ :=
  ⟨(x.val : ℝ), Rat.cast_nonneg.mpr x.2.1, by
    rw [← Rat.cast_one (α := ℝ), Rat.cast_le]
    exact x.2.2⟩

end UnitInterval

end Silmaril.Logic.ManyValuedCatalogue
