module

public import Silmaril.Compiler.Core.Verified.LoopBlocks.Defs
/-! # A mutable counter loop, with memory and caller frames left arbitrary

The target structure matches `ci/0055-while_acc.c`: test `ret < 10`,
assign `ret = ret + 1`, and jump back. The checks exercise both branch
outcomes and repeated reads after assignment, rather than a bare self-jump.
No whole-document compiler acceptance is asserted here.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.LoopBlocks.Checks

open Silmaril.Machine
open StateExpr (Key Term)

/-- Register 3 holds the counter; all temporaries start at register 4. -/
def regs : Key → Mir.Reg := fun _ => 3

def condition (q : Key) : Term := .cmp .lt 1 0 (.var q) (.lit 10)
def increment (q : Key) : Term := .bin .add (.var q) (.lit 1)

/-- Header, assignment/backedge, and return, in an actual Lir function. -/
def counter (q : Key) : Lir.Prog Mir.Reg :=
  ⟨[⟨[], 0, [testBlock regs 4 (condition q) 1 2,
    assignBlock regs 4 q (increment q) 0, ⟨[], .ret [.reg 3]⟩]⟩]⟩

/-- A live iteration updates the counter and returns to the test, preserving all
registers below 3 as well as memory and the caller stack. -/
theorem iteration (q : Key) (n : Int) (range : 0 ≤ n ∧ n < 10)
    (fr : Lir.Frame Mir.Reg) (holds : fr.get 3 = some (BitVec.ofInt 64 n))
    (stack : List (Lir.Activation Mir.Reg)) (mem : Lir.Memory) :
    ∃ fr', Relation.TransGen (Lir.Step (counter q)) ⟨⟨0, 0, 0⟩, fr, stack, mem⟩
        ⟨⟨0, 0, 0⟩, fr', stack, mem⟩ ∧
      fr'.get 3 = some (BitVec.ofInt 64 (n + 1)) ∧
      ∀ r < 3, fr'.get r = fr.get r := by
  let σ : Key → Int := fun _ => n
  have ok : (condition q).Ok σ := by
    simp [condition, StateExpr.Term.Ok, σ, ConvInt.IsInt]
    omega
  have val : (condition q).val σ = 1 := by
    simp [condition, StateExpr.Term.val, Guard.compare, Guard.holds, σ, range.2]
  obtain ⟨f, test, keep⟩ := test_steps regs σ 4 (condition q) 1 2 (counter q) 0 0 rfl fr stack mem ok
    (by intro k hk; simp [regs, holds, σ])
  rw [val] at test
  simp only [show (1 : Int) ≠ 0 by decide, ite_false] at test
  have holds' : f.get 3 = some (BitVec.ofInt 64 n) := by rw [keep 3 (by decide)]; exact holds
  have ok' : (increment q).Ok σ := by
    simp [increment, StateExpr.Term.Ok, StateExpr.Term.val, Guard.apply, σ, ConvInt.IsInt]
    omega
  obtain ⟨f', body, value, keep'⟩ := assign_steps regs σ 4 q (increment q) 0 (counter q) 0 1 rfl
    f stack mem ok' (by intro k hk; simp [regs, holds', σ])
  refine ⟨f', test.trans body, ?_, ?_⟩
  · simpa [regs, increment, StateExpr.Term.val, Guard.apply, σ] using value
  · intro r hr
    have h4 : r < 4 := Nat.lt_succ_of_lt hr
    have ne : r ≠ regs q := by exact Nat.ne_of_lt hr
    rw [keep' r h4 ne, keep r h4]

/-- Once the counter reaches 10, the next test exits, and the whole-program
return exposes 10. This also checks the zero-test branch orientation. -/
theorem exits (q : Key) (fr : Lir.Frame Mir.Reg)
    (holds : fr.get 3 = some (BitVec.ofInt 64 10)) (mem : Lir.Memory) :
    Lir.Behaves (counter q) ⟨⟨0, 0, 0⟩, fr, [], mem⟩ (.returned [BitVec.ofInt 64 10] mem) := by
  let σ : Key → Int := fun _ => 10
  have ok : (condition q).Ok σ := by
    simp [condition, StateExpr.Term.Ok, σ, ConvInt.IsInt]
  have val : (condition q).val σ = 0 := by rfl
  obtain ⟨f, path, keep⟩ := test_steps regs σ 4 (condition q) 1 2 (counter q) 0 0 rfl fr [] mem ok
    (by intro k hk; simp [regs, holds, σ])
  rw [val] at path
  simp only [ite_true] at path
  have result : f.get 3 = some (BitVec.ofInt 64 10) := by rw [keep 3 (by decide)]; exact holds
  refine ⟨_, path.to_reflTransGen, ?_⟩
  simp [Lir.step, Lir.Prog.fetch, Lir.Prog.block?, Lir.Prog.func?, counter, Lir.Frame.readAll,
    Lir.Frame.read, show f.regs 3 = some (BitVec.ofInt 64 10) from result]

/-- Repeated iterations read the updated register rather than its initializer.
The target loop terminates at 10 from every starting value between 0 and 10. -/
theorem returns (q : Key) (n : Int) (range : 0 ≤ n ∧ n ≤ 10)
    (fr : Lir.Frame Mir.Reg) (holds : fr.get 3 = some (BitVec.ofInt 64 n)) (mem : Lir.Memory) :
    Lir.Behaves (counter q) ⟨⟨0, 0, 0⟩, fr, [], mem⟩ (.returned [BitVec.ofInt 64 10] mem) := by
  generalize distance : (10 - n).toNat = fuel
  induction fuel using Nat.strong_induction_on generalizing n fr with
  | ind fuel ih =>
    by_cases hn10 : n = 10
    · subst n; exact exits q fr holds mem
    · have lt : n < 10 := by omega
      obtain ⟨fr', path, value, _⟩ := iteration q n ⟨range.1, lt⟩ fr holds [] mem
      have less : (10 - (n + 1)).toNat < fuel := by omega
      have next := ih _ less (n + 1) (by constructor <;> omega) fr' value rfl
      obtain ⟨last, rest, final⟩ := next
      exact ⟨last, path.to_reflTransGen.trans rest, final⟩

end Silmaril.Compile.Core.Verified.LoopBlocks.Checks
