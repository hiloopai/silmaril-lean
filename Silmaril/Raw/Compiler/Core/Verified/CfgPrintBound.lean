module

public import Silmaril.Compiler.Core.Verified.CfgPrintStmt.Defs
/-! # A state-dependent print allowance for a positive additive recurrence

A bound indexed only by block cannot strictly decrease around a printing back edge.
For the loop `while (a < limit) { print(a); t = a; a = t + p; p = t; }`,
`rank` handles the initial `p = 0` iteration as well as the increasing iterations.
This is a mathematical certificate for current runtime values, not an evaluator or
an accepted compiler fragment. A frontend must still establish and maintain its
slot invariant at the print header.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.CfgPrintBound

/-- The zero predecessor gets one extra iteration; every later predecessor is positive. -/
def rank (limit a p : Int) : Nat := 2 * (limit - a).toNat + if p = 0 then 1 else 0

/-- While the condition is true, there is at least one remaining print allowance. -/
theorem rank_pos {limit a p : Int} (hlt : a < limit) : 0 < rank limit a p := by
  unfold rank
  split <;> omega

/-- The additive update decreases the allowance, including its initial non-increasing step. -/
theorem rank_step {limit a p : Int} (ha : 1 ≤ a) (hp : 0 ≤ p) (hlt : a < limit) :
    rank limit (a + p) a < rank limit a p := by
  unfold rank
  have hn : a ≠ 0 := by omega
  rw [ite_eq_right hn]
  by_cases hz : p = 0
  · simp [hz]
  · rw [ite_eq_right hz]
    by_cases hnext : a + p < limit <;> omega

/-- A state invariant can bound the allowance from its lower bound on `a`. -/
theorem rank_le {limit a p : Int} (ha : 1 ≤ a) :
    rank limit a p ≤ 2 * (limit - 1).toNat + 1 := by
  unfold rank
  split <;> omega

/-- Both the output and allocation allowances can be advanced by one print when its
runtime successor has a smaller rank. -/
theorem budgets_step {before after used bytes cap : Nat} {frontier frontier' : Int}
    (drop : after < before) (output : used + bytes * before ≤ cap)
    (alloc : 64 + 32 * (before : Int) ≤ frontier)
    (consumed : frontier - 32 ≤ frontier') {actual : Nat} (small : actual ≤ bytes) :
    used + actual + bytes * after ≤ cap ∧ 64 + 32 * (after : Int) ≤ frontier' := by
  constructor
  · have hmul := Nat.mul_le_mul_left bytes (Nat.succ_le_of_lt drop)
    rw [Nat.mul_succ] at hmul
    omega
  · omega

/-- A static block potential cannot pay for a nonempty print on a cycle. -/
theorem no_static_print_cycle {atPrint afterPrint cost : Nat} (positive : 0 < cost)
    (printEdge : cost + afterPrint ≤ atPrint) (backEdge : atPrint ≤ afterPrint) : False := by
  omega

/-- The three requested Fibonacci-loop rows start with this conservative allowance.
The repeated initial value is accounted for; no execution trace is baked into code. -/
theorem rank_100_initial : rank 100 1 0 = 199 := by decide

end Silmaril.Compile.Core.Verified.CfgPrintBound
