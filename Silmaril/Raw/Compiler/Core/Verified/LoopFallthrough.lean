module

public import Silmaril.Compiler.Core.Verified.LoopCondition.Defs
public import Silmaril.Compiler.Core.Verified.LoopContext.Defs

/-! # Fall-through statements between a loop test and its back edge

Recognize unit glue, assignments, strong sequencing and saved labels carrying
one unchanged local object pointer. These are the assignment/continue/break
wrappers in `ci/0055-while_acc.c`. The result is a syntax tree of statements,
not an interpreter. Evolving closed definitions below are proof witnesses;
runtime register code is supplied by `StateExprLir` and `LoopBlocks`.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.LoopFallthrough

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Dynamics
open Silmaril.Machine
open StateExpr (Key Term close)
open StateMem (Local Inv Defined defsOf update)
open StateStmt
open PureEval (Reaches)

inductive Stmt where
  | skip
  | assign (x : Sym) (t : Term)
  | seq (a b : Stmt)
  | save (x : Sym) (body : Stmt)

/-- Symbolic definitions after a finite fall-through body, used only in proofs. -/
def Stmt.defs (ds : Key → Option IntExpr.Term) : Stmt → Key → Option IntExpr.Term
  | .skip => ds
  | .assign x t => update ds x.key (some (close (defsOf ds) t))
  | .seq a b => b.defs (a.defs ds)
  | .save _ b => b.defs ds

/-- Every read and every pointer carried by a save belongs to a live local. -/
def Stmt.Ready (ls : List Local) (ds : Key → Option IntExpr.Term) : Stmt → Prop
  | .skip => True
  | .assign x t => (∃ l ∈ ls, x.key = l.sym.key) ∧ Defined ds t = true
  | .seq a b => a.Ready ls ds ∧ b.Ready ls (a.defs ds)
  | .save x b => (∃ l ∈ ls, x.key = l.sym.key) ∧ b.Ready ls ds

/-- Defined integer operations along the selected finite body. -/
def Stmt.Valid (ds : Key → Option IntExpr.Term) : Stmt → Prop
  | .skip => True
  | .assign _ t => t.Ok (StateExpr.values (defsOf ds))
  | .seq a b => a.Valid ds ∧ b.Valid (a.defs ds)
  | .save _ b => b.Valid ds

/-- Runtime operations: reads always use the current local registers. -/
def Stmt.ops (regs : Key → Mir.Reg) (d : Nat) : Stmt → List (Lir.Op Mir.Reg)
  | .skip => []
  | .assign x t => StateExprLir.assignOps regs d x.key t
  | .seq a b => a.ops regs d ++ b.ops regs d
  | .save _ b => b.ops regs d

/-- Definitions name only local objects. -/
def Supported (ls : List Local) (ds : Key → Option IntExpr.Term) : Prop :=
  ∀ q t, ds q = some t → ∃ l ∈ ls, l.sym.key = q

theorem supported_inv {ls : List Local} {ds : Key → Option IntExpr.Term}
    {env : Env} {m : Mem.Concrete.State} (inv : Inv env m ls ds) : Supported ls ds := by
  intro q t ht
  obtain ⟨_, l, hl, hk, _⟩ := inv.defs q t ht
  exact ⟨l, hl, hk⟩

theorem Stmt.supported {ls : List Local} {ds : Key → Option IntExpr.Term} (st : Stmt)
    (ready : st.Ready ls ds) (support : Supported ls ds) : Supported ls (st.defs ds) := by
  induction st generalizing ds with
  | skip => exact support
  | assign x t =>
    intro q a ha
    unfold Stmt.defs update at ha
    split at ha
    · rename_i hq
      obtain ⟨l, hl, key⟩ := ready.1
      exact ⟨l, hl, key.symm.trans hq.symm⟩
    · exact support q a ha
  | seq a b iha ihb => exact ihb ready.2 (iha ready.1 support)
  | save x body ih => exact ih ready.2 support

/-- A defined fall-through body executes from current registers and leaves
exactly the new definitions there. Source definitions never enter `ops`. -/
theorem Stmt.ops_exec {ls : List Local} {ds : Key → Option IntExpr.Term} (st : Stmt)
    (regs : Key → Mir.Reg) (d : Nat) (layout : StateLoopStep.Layout regs d ls)
    (support : Supported ls ds) (ready : st.Ready ls ds) (valid : st.Valid ds)
    (fr : Lir.Frame Mir.Reg) (matched : StateLoopStep.Registers regs ds fr) (mem : Lir.Memory) :
    ∃ fr', Lir.execOps (st.ops regs d) fr mem = some (fr', mem) ∧
      StateLoopStep.Registers regs (st.defs ds) fr' := by
  induction st generalizing ds fr with
  | skip => exact ⟨fr, rfl, matched⟩
  | assign x t =>
    obtain ⟨⟨l, hl, key⟩, defined⟩ := ready
    have reads : ∀ q ∈ t.vars,
        regs q < d ∧ fr.get (regs q) = some (BitVec.ofInt 64 (StateExpr.values (defsOf ds) q)) := by
      intro q hq
      obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (List.all_eq_true.mp defined q hq)
      obtain ⟨l', hl', hk⟩ := support q a ha
      exact ⟨by rw [← hk]; exact layout.below l' hl', by simpa [StateExpr.values, defsOf, ha] using matched q a ha⟩
    obtain ⟨fr', exec, result, other⟩ := StateExprLir.assignOps_exec regs _ d x.key t fr mem valid reads
    refine ⟨fr', exec, ?_⟩
    intro q a ha
    unfold Stmt.defs update at ha
    split at ha
    · rename_i hq
      cases ha
      rw [hq, StateExpr.close_val]
      exact result
    · rename_i hq
      obtain ⟨l', hl', hk⟩ := support q a ha
      have neq : regs q ≠ regs x.key := by
        rw [← hk, key]
        exact layout.apart l' hl' l hl (by rw [hk, ← key]; exact hq)
      rw [other _ (by rw [← hk]; exact layout.below l' hl') neq]
      exact matched q a ha
  | seq a b iha ihb =>
    obtain ⟨fr₁, exec₁, matched₁⟩ := iha support ready.1 valid.1 fr matched
    obtain ⟨fr₂, exec₂, matched₂⟩ := ihb (a.supported ready.1 support) ready.2 valid.2 fr₁ matched₁
    refine ⟨fr₂, ?_, matched₂⟩
    simp [Stmt.ops, Lir.execOps_append, exec₁, exec₂]
  | save x body ih => exact ih support ready.2 valid fr matched

/-- Syntax only: an assignment is recognized before its internal sequences. -/
def recognize (file : File Codec.wireModel Unit Unit) (e : EE) : Option Stmt :=
  match assignStmt file e with
  | some (x, t) => some (.assign x t)
  | none => match e with
    | .mk _ (.pure (.mk _ () (.val .unit))) => some .skip
    | .mk _ (.sseq (.mk _ (.base (none, _))) a b) => do
        return .seq (← recognize file a) (← recognize file b)
    | .mk _ (.save _ [(x, (_, .mk _ () (.sym x')))] body) =>
        if x'.key = x.key then (recognize file body).map (.save x) else none
    | _ => none
termination_by sizeOf e
decreasing_by all_goals (simp_all; omega)

/-- A syntactic derivation, retaining annotations and sequencing patterns. -/
inductive Shape (file : File Codec.wireModel Unit Unit) : EE → Stmt → Prop where
  | assign {e x t} (h : assignStmt file e = some (x, t)) : Shape file e (.assign x t)
  | skip (ann pann) : Shape file (.mk ann (.pure (.mk pann () (.val .unit)))) .skip
  | seq (ann pann ty) {a b sa sb} (ha : Shape file a sa) (hb : Shape file b sb) :
      Shape file (.mk ann (.sseq (.mk pann (.base (none, ty))) a b)) (.seq sa sb)
  | save (ann label info pann) {x x' body sb} (key : x'.key = x.key) (hb : Shape file body sb) :
      Shape file (.mk ann (.save label [(x, (info, .mk pann () (.sym x')))] body)) (.save x sb)

theorem recognize_shape {file : File Codec.wireModel Unit Unit} {e : EE} {st : Stmt}
    (h : recognize file e = some st) : Shape file e st := by
  unfold recognize at h
  split at h
  · rename_i x t hx
    cases h
    exact .assign hx
  · split at h
    · cases h; exact .skip _ _
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨a, ha, b, hb, eq⟩ := h
      cases eq
      exact .seq _ _ _ (recognize_shape ha) (recognize_shape hb)
    · split at h
      · rename_i hk
        simp only [Option.map_eq_some_iff] at h
        obtain ⟨sb, hb, eq⟩ := h
        cases eq
        exact .save _ _ _ _ hk (recognize_shape hb)
      · cases h
    · cases h
termination_by sizeOf e

variable {file : Program} {labels : Labels}

/-- A finite body either reaches source UB or falls through with exactly its
updated slots. Assignments may read their own previous value. Nested saves
preserve the allocation, rather than allocating a new local each iteration. -/
theorem Shape.runs {e : EE} {st : Stmt} (shape : Shape file e st)
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    (inv : Inv env m ls ds) (ready : st.Ready ls ds) (k : List Frame) :
    Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
      st.Valid ds ∧ ∃ m', m'.stdout = m.stdout ∧ Inv env m' ls (st.defs ds) ∧
        Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, k, m'⟩ := by
  induction shape generalizing env m ds k with
  | assign h =>
    obtain ⟨⟨l, hl, key⟩, defined⟩ := ready
    rcases assign_runs h inv hl key defined k with ub | ⟨ok, m', out, inv', run⟩
    · exact .inl ub
    · right
      refine ⟨ok, m', out, ?_, run⟩
      simpa [Stmt.defs, key] using inv'
  | skip ann pann =>
    exact .inr ⟨trivial, _, ReturnConst.focusMemory_stdout ann m, inv.focus ann,
      pure_unit_reaches ann pann env k m⟩
  | @seq ann pann ty a b sa sb ha hb iha ihb =>
    let K := Frame.strongBind (.mk pann (.base (none, ty))) b env :: k
    have enter := ReturnConst.sequence_reaches file labels ann (.mk pann (.base (none, ty))) a b env k m
    rcases iha inv ready.1 K with ub | ⟨ok₁, m₁, out₁, inv₁, run₁⟩
    · exact .inl (Overflows.pre enter ub)
    · have next := (enter.trans run₁).trans
        (ReturnConst.wildcard_sequence_reaches file labels pann ty .unit b env k m₁)
      rcases ihb inv₁ ready.2 k with ub | ⟨ok₂, m₂, out₂, inv₂, run₂⟩
      · exact .inl (Overflows.pre next ub)
      · exact .inr ⟨⟨ok₁, ok₂⟩, m₂, out₂.trans out₁, inv₂, next.trans run₂⟩
  | @save ann label info pann x x' body sb key hb ih =>
    obtain ⟨⟨l, hl, localKey⟩, readyBody⟩ := ready
    let env' := extendEnv [(x, StateMem.ptr l)] env
    have inv' : Inv env' (ReturnConst.focusMemory ann m) ls ds :=
      LoopTransfer.rebind (inv.focus ann) hl x localKey
    have enter := LoopReach.save_reaches (file := file) (labels := labels)
      ann label [(x, (info, .mk pann () (.sym x')))] body env
      [StateMem.ptr l]
      (.cons (SeqReach.pure_symbol pann x' env _ (inv.lookup hl (key.trans localKey))) .nil) k m
    rcases ih inv' readyBody k with ub | ⟨ok, m', out, inv'', run⟩
    · exact .inl (Overflows.pre enter ub)
    · right
      refine ⟨ok, m', by simpa using out, ?_, enter.trans run⟩
      exact { inv'' with env := inv.env }

/-- The whole finite body agrees in both machines, including self-assignments
and the saved continue/break wrappers around them. -/
theorem Shape.exec {e : EE} {st : Stmt} (shape : Shape file e st)
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    (inv : Inv env m ls ds) (ready : st.Ready ls ds) (k : List Frame)
    (regs : Key → Mir.Reg) (d : Nat) (layout : StateLoopStep.Layout regs d ls)
    (fr : Lir.Frame Mir.Reg) (matched : StateLoopStep.Registers regs ds fr) (mem : Lir.Memory) :
    Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
      ∃ m' fr', m'.stdout = m.stdout ∧ Inv env m' ls (st.defs ds) ∧
        StateLoopStep.Registers regs (st.defs ds) fr' ∧
        Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, k, m'⟩ ∧
        Lir.execOps (st.ops regs d) fr mem = some (fr', mem) := by
  rcases shape.runs inv ready k with ub | ⟨valid, m', out, inv', source⟩
  · exact .inl ub
  · obtain ⟨fr', target, matched'⟩ := st.ops_exec regs d layout (supported_inv inv) ready valid fr matched mem
    exact .inr ⟨m', fr', out, inv', matched', source, target⟩

end Silmaril.Compile.Core.Verified.LoopFallthrough
