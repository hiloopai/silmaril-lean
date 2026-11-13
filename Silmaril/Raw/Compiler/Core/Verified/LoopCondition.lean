module

public import Silmaril.Compiler.Core.Verified.StateLoopStep.Defs

/-! # The source and target condition boundary of a mutable loop

Recognize Cerberus's loaded test, boolean conversion and two arbitrary
effectful successors. A successful test preserves the concrete slots and
enters only the selected branch. Compose this with the runtime Lir test;
an exceptional integer operation is the source UB escape.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.LoopCondition

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Dynamics
open Silmaril.Machine
open StateExpr (Key Term term values)
open StateMem (Local Inv Defined defsOf)
open StateStmt
open StateLoopStep (Layout Registers)
open PureEval (Reaches)

/-- Both successors remain syntax; neither is evaluated by the recognizer. -/
def recognize (file : File Codec.wireModel Unit Unit) (xs : List Sym) :
    EE → Option (Term × EE × EE)
  | .mk _ (.sseq (.mk _ (.base (some c, _))) (.mk _ (.bound ec))
      (.mk _ (.sseq (.mk _ (.base (some b, _))) cb
        (.mk _ (.if_ (.mk _ () (.sym b')) yes no))))) =>
      if b'.key = b.key ∧ StmtIf.boolSource c cb = true ∧
          isFresh xs c = true ∧ isFresh xs b = true then
        (term file ec).map fun t => (t, yes, no)
      else none
  | _ => none

theorem recognize_inv {file : File Codec.wireModel Unit Unit} {xs : List Sym}
    {e yes no : EE} {t : Term} (h : recognize file xs e = some (t, yes, no)) :
    ∃ (a0 a1 : List Annot) (c : Sym) (cty : BaseType) (a2 : List Annot) (ec : EE)
      (a3 a4 : List Annot) (b : Sym) (bty : BaseType) (cb : EE)
      (a5 a6 : List Annot) (b' : Sym),
      e = .mk a0 (.sseq (.mk a1 (.base (some c, cty))) (.mk a2 (.bound ec))
        (.mk a3 (.sseq (.mk a4 (.base (some b, bty))) cb
          (.mk a5 (.if_ (.mk a6 () (.sym b')) yes no))))) ∧
      b'.key = b.key ∧ StmtIf.boolSource c cb = true ∧ isFresh xs c = true ∧
      isFresh xs b = true ∧ term file ec = some t := by
  unfold recognize at h
  split at h
  · split at h
    · rename_i hc
      simp only [Option.map_eq_some_iff, Prod.mk.injEq] at h
      obtain ⟨t', ht, rfl, rfl, rfl⟩ := h
      exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, rfl,
        hc.1, hc.2.1, hc.2.2.1, hc.2.2.2, ht⟩
    · cases h
  · cases h

/-- The two temporaries a statement test binds. -/
def binders : EE → List Sym
  | .mk _ (.sseq (.mk _ (.base (some c, _))) _ (.mk _ (.sseq (.mk _ (.base (some b, _))) _ _))) => [c, b]
  | _ => []

variable {file : Program} {labels : Labels}

/-- Enter the selected effectful branch, preserving the locals and stdout.
The temporary test bindings are fresh for all local object pointers. -/
theorem runs {xs : List Sym} {e yes no : EE} {t : Term}
    (shape : recognize file xs e = some (t, yes, no))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    (inv : Inv env m ls ds) (keys : Keys ls xs) (defined : Defined ds t = true)
    (k : List Frame) :
    Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
      t.Ok (values (defsOf ds)) ∧ ∃ env' m',
        LoadTask.Touched m m' ∧ Inv env' m' ls ds ∧
        (∀ y : Sym, (∀ z ∈ binders e, z.key ≠ y.key) → env'.lookup y = env.lookup y) ∧
        Reaches file labels ⟨.effectExpr e env, k, m⟩
          ⟨.effectExpr (if t.val (values (defsOf ds)) = 1 then no else yes) env', k, m'⟩ := by
  obtain ⟨a0, a1, c, cty, a2, ec, a3, a4, b, bty, cb, a5, a6, b', rfl,
    hb', hcb, hfc, hfb, htc⟩ := recognize_inv shape
  let σ := values (defsOf ds)
  let IF : EE := .mk a5 (.if_ (.mk a6 () (.sym b')) yes no)
  let REST : EE := .mk a3 (.sseq (.mk a4 (.base (some b, bty))) cb IF)
  let K := Frame.strongBind (.mk a1 (.base (some c, cty))) REST env :: k
  have pre : Reaches file labels
      ⟨.effectExpr (.mk a0 (.sseq (.mk a1 (.base (some c, cty))) (.mk a2 (.bound ec)) REST)) env, k, m⟩
      ⟨.effectExpr ec env, .bound :: K, m⟩ :=
    (ReturnConst.sequence_reaches file labels a0 _ _ _ env k m).trans
      (ReturnLit.bound_reaches a2 _ env _ m)
  by_cases ok : t.Ok σ
  · right
    obtain ⟨xs', m₁, fr, hfr, _, tch, run⟩ := StateExpr.term_runs (file := file) (labels := labels)
      t htc ok (.bound :: K) m (inv.locs defined)
    let cv := t.val σ
    let env₁ := extendEnv [(c, IntExpr.spec cv)] env
    let KB := Frame.strongBind (.mk a4 (.base (some b, bty))) IF env₁ :: k
    obtain ⟨m₂, tch₂, conv⟩ := boolSource_touched (file := file) (labels := labels) hcb env₁ KB m₁ cv
      (ConvInt.lookup_one rfl)
    let flag := decide (cv ≠ 1)
    let env₂ := extendEnv [(b, boolean flag)] env₁
    have hp : SeqReach.PureEval file labels (.mk a6 () (.sym b')) env₂ (boolean flag) :=
      SeqReach.pure_symbol a6 b' env₂ _ (ConvInt.lookup_one hb')
    have enter : Reaches file labels ⟨.effectExpr ec env, .bound :: K, m⟩
        ⟨.effectExpr (if flag then yes else no) env₂, k, SeqReach.focusMemory a5 m₂⟩ :=
      (Interleave.reaches_of_local file labels run).trans ((bound_pop hfr _ K m₁).trans
        ((ReturnLit.bind_reaches a1 c cty _ REST env k m₁).trans
          ((ReturnConst.sequence_reaches file labels a3 _ cb IF env₁ k m₁).trans
            (conv.trans ((ReturnLit.bind_reaches a4 b bty _ IF env₁ k m₂).trans
              (SeqReach.effect_if_reaches a5 flag hp k m₂))))))
    have touched := tch.trans (tch₂.trans (seqFocus_touched a5 m₂))
    refine ⟨ok, env₂, _, touched,
      ((inv.touched touched).extend (keys.fresh hfc)).extend (keys.fresh hfb), fun y hy => ?_, ?_⟩
    · have h1 : y.key ≠ c.key := fun h => hy c (by simp [binders]) h.symm
      have h2 : y.key ≠ b.key := fun h => hy b (by simp [binders]) h.symm
      simp only [env₂, env₁]
      rw [ConvInt.lookup_one_other h2, ConvInt.lookup_one_other h1]
    have select : (if flag then yes else no) =
        (if t.val (values (defsOf ds)) = 1 then no else yes) := by
      change (if flag then yes else no) = (if cv = 1 then no else yes)
      by_cases h : cv = 1 <;> simp [flag, h]
    rw [select] at enter
    exact pre.trans enter
  · left
    exact Overflows.pre pre (fails_overflows (StateExpr.term_fails (file := file) (labels := labels)
      t htc ok (.bound :: K) m (inv.locs defined)))

/-- A complete conditional macro-step in both machines. The Lir path is
nonempty, reads the current registers and preserves every local register.
The source enters the same successor and keeps the register/slot relation. -/
theorem test_step {xs : List Sym} {e yes no : EE} {t : Term}
    (shape : recognize file xs e = some (t, yes, no))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    (inv : Inv env m ls ds) (keys : Keys ls xs) (defined : Defined ds t = true)
    (k : List Frame) (regs : Key → Mir.Reg) (d : Nat) (layout : Layout regs d ls)
    (fr : Lir.Frame Mir.Reg) (matched : Registers regs ds fr)
    (p : Lir.Prog Mir.Reg) (f : Lir.FuncId) (label yesLabel noLabel : Lir.Label)
    (block : p.block? f label = some (LoopBlocks.testBlock regs d (LoopBlocks.coreTest t) yesLabel noLabel))
    (stack : List (Lir.Activation Mir.Reg)) (mem : Lir.Memory) :
    Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
      ∃ env' m' fr', m'.stdout = m.stdout ∧ Inv env' m' ls ds ∧ Registers regs ds fr' ∧
        Reaches file labels ⟨.effectExpr e env, k, m⟩
          ⟨.effectExpr (if t.val (values (defsOf ds)) = 1 then no else yes) env', k, m'⟩ ∧
        Relation.TransGen (Lir.Step p) ⟨⟨f, label, 0⟩, fr, stack, mem⟩
          ⟨⟨f, if t.val (values (defsOf ds)) = 1 then noLabel else yesLabel, 0⟩, fr', stack, mem⟩ := by
  rcases runs shape inv keys defined k with ub | ⟨ok, env', m', touched, inv', -, source⟩
  · exact .inl ub
  · obtain ⟨fr', target, below⟩ := LoopBlocks.core_test_steps regs (values (defsOf ds)) d t
      yesLabel noLabel p f label block fr stack mem ok (StateLoopStep.reads layout inv matched defined)
    refine .inr ⟨env', m', fr', touched.stdout, inv', ?_, source, target⟩
    intro q a ha
    obtain ⟨_, l, hl, hk, _⟩ := inv.defs q a ha
    rw [below _ (by rw [← hk]; exact layout.below l hl)]
    exact matched q a ha

end Silmaril.Compile.Core.Verified.LoopCondition
