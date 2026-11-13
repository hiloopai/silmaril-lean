module

public import Silmaril.Compiler.Core.Verified.StateExprLir.Defs

/-! # Conditional tests and assignment back edges for integer loops

These are blocks in the ordinary Lir small-step semantics, with the current
values of several locals in registers. The test is recomputed at run time and
only the selected successor is entered. Assignment jumps back to the test.
The lemmas expose actual nonempty paths, so a future Core simulation cannot
mistake a zero-step stutter for a productive loop iteration.

This is a target-side foundation; it does not extend `Verified.compile`.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.LoopBlocks

open Silmaril.Machine
open StateExpr (Key Term)
open StateExprLir

/-- A C integer condition: nonzero selects `yes`, zero selects `no`. -/
def testBlock (regs : Key → Mir.Reg) (d : Nat) (t : Term) (yes no : Lir.Label) :
    Lir.Block Mir.Reg := ⟨(ops regs d t).map .op, .branch d yes no⟩

/-- Cerberus's statement conversion is `Specified(z)` to the boolean `z ≠ 1`.
The expression it converts is normally the C condition compared with zero. -/
def coreTest (t : Term) : Term := .cmp .eq 0 1 t (.lit 1)

@[simp] theorem coreTest_val (t : Term) (σ : Key → Int) :
    (coreTest t).val σ = if t.val σ = 1 then 0 else 1 := by
  simp [coreTest, StateExpr.Term.val, Guard.compare, Guard.holds]

theorem coreTest_ok (t : Term) (σ : Key → Int) (ok : t.Ok σ) : (coreTest t).Ok σ := by
  change t.Ok σ ∧ ConvInt.IsInt 1 ∧ ConvInt.IsInt 0 ∧ ConvInt.IsInt 1
  exact ⟨ok, by constructor <;> decide, by constructor <;> decide, by constructor <;> decide⟩

/-- Assign a local using its old value, then transfer to the loop header. -/
def assignBlock (regs : Key → Mir.Reg) (d : Nat) (q : Key) (t : Term) (header : Lir.Label) :
    Lir.Block Mir.Reg := ⟨(assignOps regs d q t).map .op, .jump header⟩

/-- The test reaches exactly the selected successor without touching local registers
or linear memory. The path includes the branch instruction even for empty operations. -/
theorem test_steps (regs : Key → Mir.Reg) (σ : Key → Int) (d : Nat) (t : Term)
    (yes no : Lir.Label) (p : Lir.Prog Mir.Reg) (f : Lir.FuncId) (label : Lir.Label)
    (block : p.block? f label = some (testBlock regs d t yes no))
    (fr : Lir.Frame Mir.Reg) (stack : List (Lir.Activation Mir.Reg)) (mem : Lir.Memory)
    (ok : t.Ok σ)
    (reads : ∀ q ∈ t.vars, regs q < d ∧ fr.get (regs q) = some (BitVec.ofInt 64 (σ q))) :
    ∃ fr', Relation.TransGen (Lir.Step p) ⟨⟨f, label, 0⟩, fr, stack, mem⟩
        ⟨⟨f, if t.val σ = 0 then no else yes, 0⟩, fr', stack, mem⟩ ∧
      ∀ r < d, fr'.get r = fr.get r := by
  obtain ⟨fr', w, exec, result, value, below⟩ := ops_exec regs σ t d fr mem reads
  rw [value ok] at result
  have path := Lir.steps_execOps (p := p) (os := ops regs d t)
    (s := ⟨⟨f, label, 0⟩, fr, stack, mem⟩) (rest := []) block (by simp [testBlock]) exec
  have fetch := Lir.Prog.fetch_eq_term (p := p)
    (pt := ⟨f, label, (ops regs d t).length⟩) block (by simp [testBlock])
  have zero : (BitVec.ofInt 64 (t.val σ) = 0#64) ↔ t.val σ = 0 := by
    constructor
    · intro hz
      have h := IntExpr.ofInt_eq_zero (StateExpr.Term.int_of_ok t ok)
      rw [hz] at h
      simpa using h.symm
    · intro hz; simp [hz]
  refine ⟨fr', ?_, below⟩
  apply Relation.TransGen.tail' path
  change Lir.step p _ = .running _
  simp [Lir.step, fetch, testBlock, result, zero]

/-- Match the boolean conversion in `StmtIf.boolSource`, rather than branching on
its loaded input directly (which would reverse the usual C loop condition). -/
theorem core_test_steps (regs : Key → Mir.Reg) (σ : Key → Int) (d : Nat) (t : Term)
    (yes no : Lir.Label) (p : Lir.Prog Mir.Reg) (f : Lir.FuncId) (label : Lir.Label)
    (block : p.block? f label = some (testBlock regs d (coreTest t) yes no))
    (fr : Lir.Frame Mir.Reg) (stack : List (Lir.Activation Mir.Reg)) (mem : Lir.Memory)
    (ok : t.Ok σ)
    (reads : ∀ q ∈ t.vars, regs q < d ∧ fr.get (regs q) = some (BitVec.ofInt 64 (σ q))) :
    ∃ fr', Relation.TransGen (Lir.Step p) ⟨⟨f, label, 0⟩, fr, stack, mem⟩
        ⟨⟨f, if t.val σ = 1 then no else yes, 0⟩, fr', stack, mem⟩ ∧
      ∀ r < d, fr'.get r = fr.get r := by
  have reads' : ∀ q ∈ (coreTest t).vars,
      regs q < d ∧ fr.get (regs q) = some (BitVec.ofInt 64 (σ q)) := by
    simpa [coreTest, StateExpr.Term.vars] using reads
  have path := test_steps regs σ d (coreTest t) yes no p f label block fr stack mem
    (coreTest_ok t σ ok) reads'
  by_cases h : t.val σ = 1 <;> simpa [h] using path

/-- The body updates the assigned local and jumps back, preserving every other
local register. This is a productive path for arbitrary incoming caller stacks. -/
theorem assign_steps (regs : Key → Mir.Reg) (σ : Key → Int) (d : Nat) (q : Key) (t : Term)
    (header : Lir.Label) (p : Lir.Prog Mir.Reg) (f : Lir.FuncId) (label : Lir.Label)
    (block : p.block? f label = some (assignBlock regs d q t header))
    (fr : Lir.Frame Mir.Reg) (stack : List (Lir.Activation Mir.Reg)) (mem : Lir.Memory)
    (ok : t.Ok σ)
    (reads : ∀ k ∈ t.vars, regs k < d ∧ fr.get (regs k) = some (BitVec.ofInt 64 (σ k))) :
    ∃ fr', Relation.TransGen (Lir.Step p) ⟨⟨f, label, 0⟩, fr, stack, mem⟩
        ⟨⟨f, header, 0⟩, fr', stack, mem⟩ ∧
      fr'.get (regs q) = some (BitVec.ofInt 64 (t.val σ)) ∧
      ∀ r < d, r ≠ regs q → fr'.get r = fr.get r := by
  obtain ⟨fr', exec, result, below⟩ := assignOps_exec regs σ d q t fr mem ok reads
  have path := Lir.steps_execOps (p := p) (os := assignOps regs d q t)
    (s := ⟨⟨f, label, 0⟩, fr, stack, mem⟩) (rest := []) block (by simp [assignBlock]) exec
  have fetch := Lir.Prog.fetch_eq_term (p := p)
    (pt := ⟨f, label, (assignOps regs d q t).length⟩) block (by simp [assignBlock])
  refine ⟨fr', ?_, result, below⟩
  apply Relation.TransGen.tail' path
  change Lir.step p _ = .running _
  simp [Lir.step, fetch, assignBlock]

end Silmaril.Compile.Core.Verified.LoopBlocks
