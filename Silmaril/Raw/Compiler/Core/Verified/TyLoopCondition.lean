module

public import Silmaril.Compiler.Core.Verified.TyLoopStep.Defs
public import Silmaril.Compiler.Core.Verified.TyRun.Defs
/-! # Typed conditional macro-steps over mutable registers

Reuse `TyRun.ifParts` and its source proof with `TyInput`'s current-register
evaluation. Cerberus's statement conversion selects the first arm when its loaded
comparison is not `1`. For a boolean-valued typed term, an ordinary Lir branch
with its destinations exchanged has exactly this behavior.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.TyLoopCondition

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Dynamics
open Silmaril.Machine
open TyExpr (Key Term values)
open TyMem (Local Inv Defined defsOf)
open TyLoopStep (Layout Registers)

/-- Branch on a boolean-valued loaded comparison, using Cerberus's statement conversion. -/
def testBlock (regs : Key → Mir.Reg) (d : Nat) (t : Term) (yes no : Lir.Label) :
    Lir.Block Mir.Reg := ⟨(TyInput.ops regs d t).map .op, .branch d no yes⟩

/-- The target test is productive and retains every local register and all memory. -/
theorem test_steps (regs : Key → Mir.Reg) (σ : Key → Int) (d : Nat) (t : Term)
    (wf : t.Wf) (boolean : TyState.Term.bool01 t = true)
    (yes no : Lir.Label) (p : Lir.Prog Mir.Reg) (f : Lir.FuncId) (label : Lir.Label)
    (block : p.block? f label = some (testBlock regs d t yes no))
    (fr : Lir.Frame Mir.Reg) (stack : List (Lir.Activation Mir.Reg)) (mem : Lir.Memory)
    (reads : ∀ q ∈ t.vars, regs q.1 < d ∧ fr.get (regs q.1) = some (BitVec.ofInt 64 (σ q.1))) :
    ∃ fr', Relation.TransGen (Lir.Step p) ⟨⟨f, label, 0⟩, fr, stack, mem⟩
        ⟨⟨f, if t.val σ = 1 then no else yes, 0⟩, fr', stack, mem⟩ ∧
      ∀ r < d, fr'.get r = fr.get r := by
  obtain ⟨fr', exec, result, below⟩ := TyInput.ops_exec regs σ t wf d fr mem reads
  have path := Lir.steps_execOps (p := p) (os := TyInput.ops regs d t)
    (s := ⟨⟨f, label, 0⟩, fr, stack, mem⟩) (rest := []) block (by simp [testBlock]) exec
  have fetch := Lir.Prog.fetch_eq_term (p := p)
    (pt := ⟨f, label, (TyInput.ops regs d t).length⟩) block (by simp [testBlock])
  refine ⟨fr', ?_, below⟩
  apply Relation.TransGen.tail' path
  change Lir.step p _ = .running _
  rcases TyState.Term.bool01_val boolean σ with zero | one
  · simp [Lir.step, fetch, testBlock, result, zero]
  · simp [Lir.step, fetch, testBlock, result, one]

/-- Match the existing typed source conditional against a mutable-register branch.
Both successors remain Core syntax, and overflow is a source UB escape. -/
theorem test_step {file : Program} {labels : Labels} {xs : TyStmt.Vars}
    {e yes no : EE} {t : Term} (shape : TyRun.ifParts file xs e = some (t, yes, no))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option Term}
    (inv : Inv env m ls ds) (keys : TyStmt.Keys ls xs) (defined : Defined ds t = true)
    (typed : TyStmt.typedIn xs t = true) (wf : t.Wf) (boolean : TyState.Term.bool01 t = true)
    (k : List Frame) (regs : Key → Mir.Reg) (d : Nat) (layout : Layout regs d ls)
    (fr : Lir.Frame Mir.Reg) (matched : Registers regs ds fr)
    (p : Lir.Prog Mir.Reg) (f : Lir.FuncId) (label yesLabel noLabel : Lir.Label)
    (block : p.block? f label = some (testBlock regs d t yesLabel noLabel))
    (stack : List (Lir.Activation Mir.Reg)) (mem : Lir.Memory) :
    StateStmt.Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
      ∃ env' m' fr', m'.stdout = m.stdout ∧ TyStmt.SameAlloc m m' ∧
        Inv env' m' ls ds ∧ Registers regs ds fr' ∧
        PureEval.Reaches file labels ⟨.effectExpr e env, k, m⟩
          ⟨.effectExpr (if t.val (values (defsOf ds)) = 1 then no else yes) env', k, m'⟩ ∧
        Relation.TransGen (Lir.Step p) ⟨⟨f, label, 0⟩, fr, stack, mem⟩
          ⟨⟨f, if t.val (values (defsOf ds)) = 1 then noLabel else yesLabel, 0⟩,
            fr', stack, mem⟩ := by
  rcases TyRun.if_runs shape inv keys defined typed k with
    ub | ⟨env', m', out, alloc, inv', source⟩
  · exact .inl ub
  · obtain ⟨fr', target, below⟩ := test_steps regs (values (defsOf ds)) d t wf boolean
      yesLabel noLabel p f label block fr stack mem (TyLoopStep.reads layout inv matched defined)
    refine .inr ⟨env', m', fr', out, alloc, inv', ?_, source, target⟩
    intro q a ha
    obtain ⟨_, l, hl, hk, _⟩ := inv.defs q a ha
    rw [below _ (by rw [← hk]; exact layout.below l hl)]
    exact matched q a ha

end Silmaril.Compile.Core.Verified.TyLoopCondition
