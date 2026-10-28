module

public import Silmaril.Semantics.Dataflow.Framework
public import Mathlib.Data.Set.Basic
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Tactic.Linarith

/-! # §11 Abstract interpretation (notes p. 20; slides pp. 89–92)

The rule of signs (notes p. 20): the abstract values `(−)`, `(0)`, `(+)` and
`(?)` ("no knowledge"), with abstract multiplication `⊗` and addition `⊕`
given by the notes' tables. `Sign.ofInt` (the notes' `abs`) maps an integer to its sign.

* `ofInt_mul`: `⊗` is exact, `abs (a * b) = abs a ⊗ abs b`;
* `ofInt_add_le`: `⊕` is *safe*, `abs (a + b) ⊑ abs a ⊕ abs b`, where `⊑` is the
  information order with `(?)` on top ("`(−) ⊆ (?)`");
* `ofInt_example`: the notes' `(−1515) + 37` loses precision.

The concretisation `γ` maps a sign to a set of integers; safety is stated as
`γ`-soundness of the abstract operations, and the general fixpoint-transfer
theorem `Silmaril.Semantics.Dataflow.lfp_le_of_galoisConnection` lifts such per-operation
soundness to least fixed points. A second domain, intervals, is used by
exercise sheet 2, question 1.
-/

@[expose] public section

namespace Silmaril.Courses.Cambridge.OptimisingCompilers.AbstractInterpretation

/-- Signs, plus `top` for "no knowledge" (`(?)` in the notes). -/
inductive Sign where
  | neg | zero | pos | top
  deriving DecidableEq

namespace Sign

/-- The abstraction of an integer. -/
def ofInt (n : ℤ) : Sign := if n < 0 then .neg else if n = 0 then .zero else .pos

/-- The concretisation of a sign. -/
def γ : Sign → Set ℤ
  | .neg => {n | n < 0}
  | .zero => {0}
  | .pos => {n | 0 < n}
  | .top => Set.univ

/-- The information order: `s ⊑ t` when `t` is `s` or `(?)`. -/
def le (s t : Sign) : Prop := s = t ∨ t = .top

/-- `⊗`, the table of notes p. 20 (extended by `(?)`). -/
def mul : Sign → Sign → Sign
  | .zero, _ | _, .zero => .zero
  | .top, _ | _, .top => .top
  | .neg, .neg | .pos, .pos => .pos
  | .neg, .pos | .pos, .neg => .neg

/-- `⊕`, the table of notes p. 20, with `(?) ⊕ x = (?) = x ⊕ (?)`. -/
def add : Sign → Sign → Sign
  | .top, _ | _, .top => .top
  | .zero, s | s, .zero => s
  | .neg, .neg => .neg
  | .pos, .pos => .pos
  | .neg, .pos | .pos, .neg => .top

theorem ofInt_trichotomy (n : ℤ) :
    (n < 0 ∧ ofInt n = .neg) ∨ (n = 0 ∧ ofInt n = .zero) ∨ (0 < n ∧ ofInt n = .pos) := by
  unfold ofInt
  split_ifs with h₁ h₂
  · exact Or.inl ⟨h₁, rfl⟩
  · exact Or.inr (Or.inl ⟨h₂, rfl⟩)
  · exact Or.inr (Or.inr ⟨by omega, rfl⟩)

theorem mem_γ_ofInt (n : ℤ) : n ∈ γ (ofInt n) := by
  unfold ofInt
  split_ifs with h₁ h₂
  · exact h₁
  · exact h₂
  · show 0 < n
    omega

/-- `⊗` is exact. -/
theorem ofInt_mul (a b : ℤ) : ofInt (a * b) = mul (ofInt a) (ofInt b) := by
  rcases ofInt_trichotomy a with ⟨ha, ea⟩ | ⟨ha, ea⟩ | ⟨ha, ea⟩ <;>
  rcases ofInt_trichotomy b with ⟨hb, eb⟩ | ⟨hb, eb⟩ | ⟨hb, eb⟩ <;>
  rcases ofInt_trichotomy (a * b) with ⟨hc, ec⟩ | ⟨hc, ec⟩ | ⟨hc, ec⟩ <;>
  rw [ea, eb, ec] <;>
  first | rfl | (exfalso; nlinarith)

/-- `⊕` is safe. -/
theorem ofInt_add_le (a b : ℤ) : le (ofInt (a + b)) (add (ofInt a) (ofInt b)) := by
  rcases ofInt_trichotomy a with ⟨ha, ea⟩ | ⟨ha, ea⟩ | ⟨ha, ea⟩ <;>
  rcases ofInt_trichotomy b with ⟨hb, eb⟩ | ⟨hb, eb⟩ | ⟨hb, eb⟩ <;>
  rcases ofInt_trichotomy (a + b) with ⟨hc, ec⟩ | ⟨hc, ec⟩ | ⟨hc, ec⟩ <;>
  rw [ea, eb, ec] <;>
  first | exact Or.inl rfl | exact Or.inr rfl | (exfalso; omega)

/-- Soundness via concretisation: `γ s ⊕ γ t ⊆ γ (s ⊕ t)`, and similarly `⊗`. -/
theorem add_sound {s t : Sign} {a b : ℤ} (ha : a ∈ γ s) (hb : b ∈ γ t) : a + b ∈ γ (add s t) := by
  cases s <;> cases t <;>
    simp only [γ, add, Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_univ] at ha hb ⊢ <;>
    omega

theorem mul_sound {s t : Sign} {a b : ℤ} (ha : a ∈ γ s) (hb : b ∈ γ t) : a * b ∈ γ (mul s t) := by
  cases s <;> cases t <;>
    simp only [γ, mul, Set.mem_ofPred_eq, Set.mem_singleton_iff, Set.mem_univ] at ha hb ⊢ <;>
    first | trivial | (subst_vars; simp) | nlinarith

/-- The notes' example (p. 20): `abs((−1515) + 37) = (−)` but
`abs(−1515) ⊕ abs(37) = (?)`. -/
theorem ofInt_example : ofInt (-1515 + 37) = .neg ∧ add (ofInt (-1515)) (ofInt 37) = .top := by
  decide

end Sign

/-! ## Intervals -/

/-- Integer intervals `[lo, hi]`. -/
structure Interval where
  lo : ℤ
  hi : ℤ
  deriving DecidableEq

namespace Interval

/-- The concretisation of an interval. -/
def γ (I : Interval) : Set ℤ := {n | I.lo ≤ n ∧ n ≤ I.hi}

/-- `α(x + y) = [lx + ly, hx + hy]` (exercise sheet 2, Q1). -/
def add (I J : Interval) : Interval := ⟨I.lo + J.lo, I.hi + J.hi⟩

/-- `α(x − y) = [lx − hy, hx − ly]` (exercise sheet 2, Q1). -/
def sub (I J : Interval) : Interval := ⟨I.lo - J.hi, I.hi - J.lo⟩

theorem add_sound {I J : Interval} {a b : ℤ} (ha : a ∈ I.γ) (hb : b ∈ J.γ) :
    a + b ∈ (I.add J).γ := by
  obtain ⟨h₁, h₂⟩ := ha
  obtain ⟨h₃, h₄⟩ := hb
  exact ⟨show I.lo + J.lo ≤ a + b by omega, show a + b ≤ I.hi + J.hi by omega⟩

theorem sub_sound {I J : Interval} {a b : ℤ} (ha : a ∈ I.γ) (hb : b ∈ J.γ) :
    a - b ∈ (I.sub J).γ := by
  obtain ⟨h₁, h₂⟩ := ha
  obtain ⟨h₃, h₄⟩ := hb
  exact ⟨show I.lo - J.hi ≤ a - b by omega, show a - b ≤ I.hi - J.lo by omega⟩

end Interval

end Silmaril.Courses.Cambridge.OptimisingCompilers.AbstractInterpretation
