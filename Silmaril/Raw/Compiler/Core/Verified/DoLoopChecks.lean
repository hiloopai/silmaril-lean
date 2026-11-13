module

public import Silmaril.Compiler.Core.Verified.DoMain.Defs
/-! # Runtime checks for body-first loops

The same graph used by `DoMain.blocks` increments a current register and tests
it afterwards. An initially false condition still executes the body once.
The caller memory is arbitrary and preserved throughout.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.DoLoopChecks

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Silmaril.Machine
open StateExpr (Key Term)

def x : Sym := ⟨⟨[]⟩, 504, .objectAddress "x"⟩
def increment : Term := .bin .add (.var x.key) (.lit 1)
def condition : Term := .cmp .lt 1 0 (.var x.key) (.lit 3)

def plan : LoopMain.Plan :=
  ⟨[x], [], condition, .assign x increment, .skip, .var x.key⟩

def prog : Lir.Prog Mir.Reg := ⟨[⟨[], 0, DoMain.blocks plan⟩]⟩

def regs : Key → Mir.Reg := LoopMain.regOf [x.key]

/-- A body is executed even when the initial value already fails the test.
This catches a `do` loop incorrectly emitted as a `while` loop. -/
theorem initially_false (fr : Lir.Frame Mir.Reg)
    (holds : fr.get 0 = some (BitVec.ofInt 64 3)) (mem : Lir.Memory) :
    Lir.Behaves prog ⟨⟨0, 1, 0⟩, fr, [], mem⟩ (.returned [BitVec.ofInt 64 4] mem) := by
  let σ : Key → Int := fun _ => 3
  have reads : ∀ q ∈ increment.vars,
      regs q < 1 ∧ fr.get (regs q) = some (BitVec.ofInt 64 (σ q)) := by
    intro q hq
    simp only [increment, Term.vars, List.mem_append, List.mem_singleton, List.not_mem_nil,
      or_false] at hq
    subst q
    exact ⟨by decide, holds⟩
  have ok : increment.Ok σ := by
    simp [increment, Term.Ok, Term.val, Guard.apply, σ, ConvInt.IsInt]
  obtain ⟨frB, exec, result, _⟩ := StateExprLir.assignOps_exec regs σ 1 x.key increment fr mem ok reads
  have body := LoopIteration.body_steps regs 1 plan.body 2 prog 0 1 rfl fr frB [] mem exec
  have current : frB.get 0 = some (BitVec.ofInt 64 4) := by
    simpa [regs, increment, Term.val, Guard.apply, σ, LoopMain.regOf] using result
  let σ' : Key → Int := fun _ => 4
  have ok' : condition.Ok σ' := by
    simp [condition, Term.Ok, σ', ConvInt.IsInt]
  obtain ⟨frT, test, keep⟩ := LoopBlocks.test_steps regs σ' 1 condition 1 3 prog 0 2 rfl
    frB [] mem ok' (by
      intro q hq
      simp only [condition, Term.vars, List.mem_append, List.mem_singleton, List.not_mem_nil,
        or_false] at hq
      subst q
      exact ⟨by decide, current⟩)
  have zero : condition.val σ' = 0 := by decide
  rw [zero] at test
  simp only [ite_true] at test
  have matchRet : frT.get 0 = some (BitVec.ofInt 64 4) := by
    rw [keep 0 (by decide)]
    exact current
  have retReads : ∀ q ∈ (plan.ret).vars,
      regs q < 1 ∧ frT.get (regs q) = some (BitVec.ofInt 64 (σ' q)) := by
    intro q hq
    have hq' : q = x.key := by simpa [plan, Term.vars] using hq
    subst q
    exact ⟨by decide, matchRet⟩
  obtain ⟨frR, w, execR, resR, valR, _⟩ := StateExprLir.ops_exec regs σ' plan.ret 1 frT mem retReads
  have okR : plan.ret.Ok σ' := by
    simp [plan, Term.Ok, σ', ConvInt.IsInt]
  have w4 : w = BitVec.ofInt 64 4 := by simpa [plan, Term.val, σ'] using valR okR
  let os := StateExprLir.ops regs 1 plan.ret
  have path := Lir.steps_execOps (p := prog) (os := os) (s := ⟨⟨0, 3, 0⟩, frT, [], mem⟩)
    (rest := []) (show prog.block? 0 3 = some ⟨os.map .op, .ret [.reg 1]⟩ from rfl) rfl execR
  have fetch := Lir.Prog.fetch_eq_term (p := prog) (pt := ⟨0, 3, os.length⟩)
    (show prog.block? 0 3 = some ⟨os.map .op, .ret [.reg 1]⟩ from rfl) (by simp)
  refine ⟨_, (body.trans test).to_reflTransGen.trans path, ?_⟩
  have res : frR.regs 1 = some w := resR
  simp [Lir.step, fetch, Lir.Frame.readAll, Lir.Frame.read, res, w4]

/-- The direct test treats both positive and negative integers as true.
In particular it must not reuse the while conversion's comparison with 1. -/
example : (.var x.key : Term).val (fun _ => -1) ≠ 0 := by decide
example : (.var x.key : Term).val (fun _ => 1) ≠ 0 := by decide
example : (.var x.key : Term).val (fun _ => 0) = 0 := by decide

end Silmaril.Compile.Core.Verified.DoLoopChecks
