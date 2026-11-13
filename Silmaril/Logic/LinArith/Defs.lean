module

public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic

@[expose] public section

/-!
# Linear inequality systems and Farkas certificates

A **system** is a list of linear inequalities `∑ⱼ aⱼ xⱼ ≤ b` with integer coefficients, in
sparse form (`Ineq.coeffs` lists pairs `(j, aⱼ)`; repeated indices add up, missing ones are
`0`). It is **feasible over** an ordered field `K` (`Feasible K S`) if some `x : ℕ → K`
satisfies every inequality.

A **Farkas certificate** gives each inequality a multiplier `y ≥ 0`. It is valid
(`WRows.IsCert`) if the weighted sum of the left-hand sides is the zero form (`comb rs j = 0`
for every variable `j`) and the weighted sum of the bounds is negative (`combB rs < 0`).
Summing the inequalities with these weights gives `0 ≤ combB rs < 0`, so a valid certificate
refutes the system over every ordered field, in particular over `ℚ` and `ℝ`
(`Silmaril.Logic.LinArith.Thms`). A rational system becomes an integer one by clearing
denominators, and rational multipliers become integer ones the same way.

* `WRows`: weighted rows (multiplier, inequality), the form the checkers use;
* `checkCert S y`: the executable check of the explicit certificate `y` for the system `S`;
* `Cmd`, `load`: the **streaming** presentation used by the Wasm checker
  (`Silmaril.Wasm.Examples.Farkas`): `row y b` starts an inequality with bound `b` and multiplier
  `y`, `entry j a` adds the coefficient `a` of variable `j` to the current inequality; `load`
  gives the weighted rows of a command list (entries before the first row are ignored).

Only the soundness direction of Farkas' lemma is formalised here. No converse theorem
constructing a certificate for every infeasible system is proved, and no geometric
separation theorem is connected to a certificate construction in this development.

A Silmaril addition.
-/

namespace Silmaril.Logic.LinArith

/-- A linear inequality `∑ (j, a) ∈ coeffs, a * x j ≤ bound` with integer coefficients. -/
structure Ineq where
  /-- The coefficients, as `(variable, coefficient)` pairs. -/
  coeffs : List (ℕ × ℤ)
  /-- The right-hand side. -/
  bound : ℤ
  deriving DecidableEq, Repr

/-- A system of linear inequalities. -/
abbrev System := List Ineq

namespace Ineq

/-- The left-hand side at the point `x`. -/
def eval {K : Type*} [Field K] (r : Ineq) (x : ℕ → K) : K :=
  (r.coeffs.map fun e => (e.2 : K) * x e.1).sum

/-- The point `x` satisfies the inequality. -/
def Sat {K : Type*} [Field K] [LinearOrder K] (r : Ineq) (x : ℕ → K) : Prop :=
  r.eval x ≤ (r.bound : K)

/-- The total coefficient of variable `j`. -/
def coeff (r : Ineq) (j : ℕ) : ℤ :=
  (r.coeffs.map fun e => if e.1 = j then e.2 else 0).sum

end Ineq

/-- The system has a solution over `K`. -/
def Feasible (K : Type*) [Field K] [LinearOrder K] (S : System) : Prop :=
  ∃ x : ℕ → K, ∀ r ∈ S, r.Sat x

/-- Weighted rows: inequalities with their multipliers. -/
abbrev WRows := List (ℤ × Ineq)

namespace WRows

/-- The coefficient of variable `j` in the weighted sum of the rows. -/
def comb (rs : WRows) (j : ℕ) : ℤ := (rs.map fun p => p.1 * p.2.coeff j).sum

/-- The weighted sum of the bounds. -/
def combB (rs : WRows) : ℤ := (rs.map fun p => p.1 * p.2.bound).sum

/-- The inequalities. -/
def system (rs : WRows) : System := rs.map Prod.snd

/-- **A valid Farkas certificate**: nonnegative multipliers whose weighted sum of the rows is
`0 ≤ c` with `c < 0`. -/
structure IsCert (rs : WRows) : Prop where
  /-- The multipliers are nonnegative. -/
  nonneg : ∀ p ∈ rs, 0 ≤ p.1
  /-- The left-hand sides cancel. -/
  comb_zero : ∀ j, rs.comb j = 0
  /-- The bounds add up to a negative number. -/
  combB_neg : rs.combB < 0

/-- The variables mentioned by the rows. -/
def support (rs : WRows) : List ℕ := rs.flatMap fun p => p.2.coeffs.map Prod.fst

/-- **The executable certificate check.** -/
def check (rs : WRows) : Bool :=
  rs.all (fun p => decide (0 ≤ p.1)) && (rs.support.all fun j => rs.comb j == 0) &&
    decide (rs.combB < 0)

end WRows

/-- Pair a system with its multipliers. -/
def weigh (S : System) (y : List ℤ) : WRows := y.zip S

/-- **Check the certificate `y` for the system `S`**: one multiplier per inequality, and the
weighted rows pass `WRows.check`. -/
def checkCert (S : System) (y : List ℤ) : Bool := y.length == S.length && (weigh S y).check

/-! ## The streaming presentation -/

/-- A loading command of the streaming checker. -/
inductive Cmd where
  /-- Start an inequality with multiplier `y` and bound `b`. -/
  | row (y b : ℤ)
  /-- Add the coefficient `a` of variable `j` to the current inequality. -/
  | entry (j : ℕ) (a : ℤ)
  deriving DecidableEq, Repr

/-- One command on the weighted rows, the current row first. -/
def Cmd.apply : WRows → Cmd → WRows
  | rs, .row y b => (y, ⟨[], b⟩) :: rs
  | [], .entry _ _ => []
  | (y, r) :: rs, .entry j a => (y, ⟨(j, a) :: r.coeffs, r.bound⟩) :: rs

/-- The weighted rows loaded by a command list (the last row first). -/
def load (cs : List Cmd) : WRows := cs.foldl Cmd.apply []

/-- The system loaded by a command list. -/
def loadSystem (cs : List Cmd) : System := (load cs).system

end Silmaril.Logic.LinArith
