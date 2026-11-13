module

public import Silmaril.Compiler.Core.Verified.LoopFallthrough.Defs

/-! # A productive iteration of a mutable Core/Lir loop

Compose the actual loaded condition, fall-through statement body and saved
pointer back edge. Both paths return to the header with the updated slots
and registers related. Source and target paths are nonempty, so these
macro-steps can be iterated without introducing false divergence.

This is a local simulation boundary, not document startup or artifact wiring.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.LoopIteration

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Dynamics
open Silmaril.Machine
open StateExpr (Key Term values)
open StateMem (Local Inv defsOf)
open StateLoopStep (Layout Registers)
open PureEval (Reaches)

def bodyBlock (regs : Key → Mir.Reg) (d : Nat) (body : LoopFallthrough.Stmt)
    (header : Lir.Label) : Lir.Block Mir.Reg :=
  ⟨(body.ops regs d).map .op, .jump header⟩

/-- Flattened statement operations execute before the back edge. -/
theorem body_steps (regs : Key → Mir.Reg) (d : Nat) (body : LoopFallthrough.Stmt)
    (header : Lir.Label) (p : Lir.Prog Mir.Reg) (f : Lir.FuncId) (label : Lir.Label)
    (block : p.block? f label = some (bodyBlock regs d body header))
    (fr fr' : Lir.Frame Mir.Reg) (stack : List (Lir.Activation Mir.Reg)) (mem : Lir.Memory)
    (exec : Lir.execOps (body.ops regs d) fr mem = some (fr', mem)) :
    Relation.TransGen (Lir.Step p) ⟨⟨f, label, 0⟩, fr, stack, mem⟩
      ⟨⟨f, header, 0⟩, fr', stack, mem⟩ := by
  have path := Lir.steps_execOps (p := p) (os := body.ops regs d)
    (s := ⟨⟨f, label, 0⟩, fr, stack, mem⟩) (rest := []) block (by simp [bodyBlock]) exec
  have fetch := Lir.Prog.fetch_eq_term (p := p)
    (pt := ⟨f, label, (body.ops regs d).length⟩) block (by simp [bodyBlock])
  apply Relation.TransGen.tail' path
  change Lir.step p _ = .running _
  simp [Lir.step, fetch, bodyBlock]

variable {file : Program} {labels : Labels}

/-- One true-test iteration, including all sequencing and saved-label frames.
The arbitrary incoming `k` is discarded at the run; the collected label's
right continuations are restored with the new environment. Linear memory and
the target caller stack are preserved. -/
theorem iterate {xs : List Sym} {head body no : EE} {t : Term} {st : LoopFallthrough.Stmt}
    (ann patann : List Annot) (ty : BaseType) (rann pann : List Annot) (label x : Sym)
    (condition : LoopCondition.recognize file xs head = some (t,
      .mk ann (.sseq (.mk patann (.base (none, ty))) body
        (.mk rann (.run () label [.mk pann () (.sym x)]))), no))
    (shape : LoopFallthrough.Shape file body st)
    (c : LoopContext.Context) (localLabels : Labels)
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    (inv : Inv env m ls ds) (keys : StateStmt.Keys ls xs) (defined : StateMem.Defined ds t = true)
    (ready : st.Ready ls ds) (active : t.val (values (defsOf ds)) ≠ 1)
    {l : Local} (hl : l ∈ ls) (key : x.key = l.sym.key)
    (k retained : List Frame)
    (context : procedureContext labels k = (localLabels, retained))
    (lookup : localLabels.lookup label = some ([x], c.fill head))
    (regs : Key → Mir.Reg) (d : Nat) (layout : Layout regs d ls)
    (fr : Lir.Frame Mir.Reg) (matched : Registers regs ds fr)
    (p : Lir.Prog Mir.Reg) (f : Lir.FuncId) (header bodyLabel exitLabel : Lir.Label)
    (testBlock : p.block? f header =
      some (LoopBlocks.testBlock regs d (LoopBlocks.coreTest t) bodyLabel exitLabel))
    (bodyBlock : p.block? f bodyLabel = some (bodyBlock regs d st header))
    (stack : List (Lir.Activation Mir.Reg)) (mem : Lir.Memory) :
    StateStmt.Overflows (file := file) (labels := labels) ⟨.effectExpr head env, k, m⟩ ∨
      ∃ env' m' fr', m'.stdout = m.stdout ∧ Inv env' m' ls (st.defs ds) ∧
        Registers regs (st.defs ds) fr' ∧
        Relation.TransGen (Spec.coreStep file labels) ⟨.effectExpr head env, k, m⟩
          ⟨.effectExpr head env', c.frames env' retained, m'⟩ ∧
        Relation.TransGen (Lir.Step p) ⟨⟨f, header, 0⟩, fr, stack, mem⟩
          ⟨⟨f, header, 0⟩, fr', stack, mem⟩ := by
  rcases LoopCondition.test_step condition inv keys defined k regs d layout fr matched p f header
      bodyLabel exitLabel testBlock stack mem with ub | ⟨env₁, m₁, fr₁, out₁, inv₁, match₁, srcTest, tgtTest⟩
  · exact .inl ub
  · simp only [ite_eq_right active] at srcTest tgtTest
    let RUN : EE := .mk rann (.run () label [.mk pann () (.sym x)])
    let K := Frame.strongBind (.mk patann (.base (none, ty))) RUN env₁ :: k
    have enter : Relation.TransGen (Spec.coreStep file labels)
        ⟨.effectExpr (.mk ann (.sseq (.mk patann (.base (none, ty))) body RUN)) env₁, k, m₁⟩
        ⟨.effectExpr body env₁, K, m₁⟩ := by
      apply Relation.TransGen.single
      refine ⟨.tau, Step.respond (by intro o; simp) ?_⟩
      have req : request file labels
          ⟨.effectExpr (.mk ann (.sseq (.mk patann (.base (none, ty))) body RUN)) env₁, k, m₁⟩ =
          .next (.effectExpr body env₁) K := by simp [request, requestAux, awaitsScheduling, K]
      rw [req]
      exact Respond.next
    have enteredPrefix := srcTest.trans enter.to_reflTransGen
    rcases shape.exec inv₁ ready K regs d layout fr₁ match₁ mem with
      ub | ⟨m₂, fr₂, out₂, inv₂, match₂, srcBody, tgtBody⟩
    · exact .inl (StateStmt.Overflows.pre enteredPrefix ub)
    · have next := StateStmt.seq_next (file := file) (labels := labels)
        (show Cond.OneAnn [] [] from .inl ⟨rfl, rfl⟩) .unit patann ty RUN env₁ k m₂
      have back := LoopContext.backedge (file := file) (labels := labels)
        c head rann pann label x inv₂ hl key k retained context lookup
      dsimp only at back
      obtain ⟨inv₃, srcBack⟩ := back
      refine .inr ⟨_, _, fr₂, ?_, inv₃, match₂, ?_, ?_⟩
      · simpa only [ReturnConst.focusMemory_stdout] using out₂.trans out₁
      · exact Relation.TransGen.trans_right srcTest
          (Relation.TransGen.trans_left enter (srcBody.trans (next.trans srcBack)))
      · exact tgtTest.trans (body_steps regs d st header p f bodyLabel bodyBlock fr₁ fr₂ stack mem tgtBody)

end Silmaril.Compile.Core.Verified.LoopIteration
