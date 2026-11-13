module

public import Silmaril.Compiler.Core.Verified.TyLoopCondition.Defs
/-! # A typed wrapping back edge

An unsigned-char counter starts at 255, increments through an int promotion,
wraps to zero at the store, and exits on the next test. The test reads the updated
register; retaining the initializer would loop forever. Memory is arbitrary and
the productive back-edge theorem accepts arbitrary caller stacks.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.TyLoopChecks

open Silmaril.Machine
open TyExpr (Key Term)
open TyLoopStep (assignBlock assign_steps)
open TyLoopCondition (testBlock test_steps)

def regs : Key → Mir.Reg := fun _ => 3

def condition (q : Key) : Term :=
  .bin (.cmp (.unsigned .ichar) .eq 1 0) (.var q (.unsigned .ichar)) (.lit 0)

def increment (q : Key) : Term :=
  .bin (.arith (.signed .int) .add) (.var q (.unsigned .ichar)) (.lit 1)

/-- Stop at zero; otherwise increment with unsigned-char destination conversion. -/
def counter (q : Key) : Lir.Prog Mir.Reg :=
  ⟨[⟨[], 0, [testBlock regs 4 (condition q) 1 2,
    assignBlock regs 4 q (.unsigned .ichar) (increment q) 0, ⟨[], .ret [.reg 3]⟩]⟩]⟩

/-- A wrapping iteration goes from 255 to zero and returns to the header. -/
theorem wraps (q : Key) (fr : Lir.Frame Mir.Reg)
    (holds : fr.get 3 = some (BitVec.ofInt 64 255))
    (stack : List (Lir.Activation Mir.Reg)) (mem : Lir.Memory) :
    ∃ fr', Relation.TransGen (Lir.Step (counter q)) ⟨⟨0, 0, 0⟩, fr, stack, mem⟩
        ⟨⟨0, 0, 0⟩, fr', stack, mem⟩ ∧ fr'.get 3 = some 0 ∧
      ∀ r < 3, fr'.get r = fr.get r := by
  let σ : Key → Int := fun _ => 255
  have val : (condition q).val σ = 0 := by
    change (TyGuard.G.cmp (.unsigned .ichar) .eq 1 0).val 255 0 = 0
    decide
  obtain ⟨f, test, keep⟩ := test_steps regs σ 4 (condition q)
    (by exact ⟨⟨rfl, rfl⟩, trivial, trivial⟩) rfl
    1 2 (counter q) 0 0 rfl fr stack mem (by intro k hk; simp [regs, holds, σ])
  rw [val] at test
  simp only [show (0 : Int) ≠ 1 by decide, ite_false] at test
  have holds' : f.get 3 = some (BitVec.ofInt 64 255) := by rw [keep 3 (by decide)]; exact holds
  obtain ⟨f', body, value, keep'⟩ := assign_steps regs σ 4 q (.unsigned .ichar) rfl
    (increment q) (by exact ⟨⟨rfl, rfl⟩, trivial, trivial⟩) 0 (counter q) 0 1 rfl f stack mem
    (by intro k hk; simp [regs, holds', σ])
  have wrap : (TyStmt.convT (.unsigned .ichar) (increment q)).val σ = 0 := by
    change (TyGuard.G.wrap (.unsigned .ichar) .add).val
      ((TyGuard.G.arith (.signed .int) .add).val 255 1) 0 = 0
    decide
  refine ⟨f', test.trans body, ?_, ?_⟩
  · simpa [regs, wrap] using value
  · intro r hr
    have h4 : r < 4 := Nat.lt_succ_of_lt hr
    have ne : r ≠ regs q := by simpa [regs] using Nat.ne_of_lt hr
    rw [keep' r h4 ne, keep r h4]

/-- The next test sees the wrapped value, exits and returns zero. -/
theorem exits (q : Key) (fr : Lir.Frame Mir.Reg) (holds : fr.get 3 = some 0)
    (mem : Lir.Memory) :
    Lir.Behaves (counter q) ⟨⟨0, 0, 0⟩, fr, [], mem⟩ (.returned [0] mem) := by
  let σ : Key → Int := fun _ => 0
  have val : (condition q).val σ = 1 := by
    change (TyGuard.G.cmp (.unsigned .ichar) .eq 1 0).val 0 0 = 1
    decide
  obtain ⟨f, path, keep⟩ := test_steps regs σ 4 (condition q)
    (by exact ⟨⟨rfl, rfl⟩, trivial, trivial⟩) rfl
    1 2 (counter q) 0 0 rfl fr [] mem (by intro k hk; simpa [regs, σ] using holds)
  rw [val] at path
  simp only [ite_true] at path
  have result : f.get 3 = some 0 := by rw [keep 3 (by decide)]; exact holds
  refine ⟨_, path.to_reflTransGen, ?_⟩
  simp [Lir.step, Lir.Prog.fetch, Lir.Prog.block?, Lir.Prog.func?, counter, Lir.Frame.readAll,
    Lir.Frame.read, show f.regs 3 = some 0 from result]

/-- A real target loop terminates after unsigned wrap, with memory unchanged. -/
theorem returns_after_wrap (q : Key) (fr : Lir.Frame Mir.Reg)
    (holds : fr.get 3 = some (BitVec.ofInt 64 255)) (mem : Lir.Memory) :
    Lir.Behaves (counter q) ⟨⟨0, 0, 0⟩, fr, [], mem⟩ (.returned [0] mem) := by
  obtain ⟨fr', path, zero, _⟩ := wraps q fr holds [] mem
  obtain ⟨s, done, halt⟩ := exits q fr' zero mem
  exact ⟨s, path.to_reflTransGen.trans done, halt⟩

end Silmaril.Compile.Core.Verified.TyLoopChecks
