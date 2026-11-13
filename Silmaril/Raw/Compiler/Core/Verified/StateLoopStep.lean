module

public import Silmaril.Compiler.Core.Verified.StateStmt.Defs
public import Silmaril.Compiler.Core.Verified.LoopBlocks.Defs

/-! # The assignment boundary of a mutable-local loop simulation

Relate the existing source slot invariant to current target registers. An
assignment computes the same expression on both sides and preserves this
relation with the updated source definitions. Definitions are proof witnesses;
they are not substituted into the emitted operations. The target always reads
its current local registers, including on a back edge.

This lemma covers the assignment and target transfer. A whole-loop frontend
must additionally match Core's saved-label parameters and continuations.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.StateLoopStep

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Dynamics
open Silmaril.Machine
open StateExpr (Key Term values close)
open StateMem (Local Inv Defined defsOf update)

/-- The finitely many local registers are distinct and below the temporaries. -/
structure Layout (regs : Key → Mir.Reg) (d : Nat) (ls : List Local) : Prop where
  below : ∀ l ∈ ls, regs l.sym.key < d
  apart : ∀ a ∈ ls, ∀ b ∈ ls, a.sym.key ≠ b.sym.key → regs a.sym.key ≠ regs b.sym.key

/-- Each source definition is represented by the current target register. -/
def Registers (regs : Key → Mir.Reg) (ds : Key → Option IntExpr.Term)
    (fr : Lir.Frame Mir.Reg) : Prop :=
  ∀ q t, ds q = some t → fr.get (regs q) = some (BitVec.ofInt 64 (t.val 0))

/-- Every defined read in the source invariant has its corresponding target word. -/
theorem reads {regs : Key → Mir.Reg} {d : Nat} {ls : List Local} {env : Env}
    {m : Mem.Concrete.State} {ds : Key → Option IntExpr.Term} {fr : Lir.Frame Mir.Reg}
    (layout : Layout regs d ls) (inv : Inv env m ls ds) (matched : Registers regs ds fr)
    {t : Term} (defined : Defined ds t = true) :
    ∀ q ∈ t.vars, regs q < d ∧ fr.get (regs q) = some (BitVec.ofInt 64 (values (defsOf ds) q)) := by
  intro q hq
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (List.all_eq_true.mp defined q hq)
  obtain ⟨_, l, hl, hk, _⟩ := inv.defs q a ha
  refine ⟨by rw [← hk]; exact layout.below l hl, ?_⟩
  simpa [values, defsOf, ha] using matched q a ha

/-- A runtime assignment keeps the register/slot relation, including self-assignment. -/
theorem registers_assign {regs : Key → Mir.Reg} {d : Nat} {ls : List Local} {env : Env}
    {m : Mem.Concrete.State} {ds : Key → Option IntExpr.Term} {fr : Lir.Frame Mir.Reg}
    (layout : Layout regs d ls) (inv : Inv env m ls ds) (matched : Registers regs ds fr)
    {l : Local} (hl : l ∈ ls) {t : Term}
    {fr' : Lir.Frame Mir.Reg}
    (result : fr'.get (regs l.sym.key) = some (BitVec.ofInt 64 (t.val (values (defsOf ds)))))
    (other : ∀ r < d, r ≠ regs l.sym.key → fr'.get r = fr.get r) :
    Registers regs (update ds l.sym.key (some (close (defsOf ds) t))) fr' := by
  intro q a ha
  unfold update at ha
  split at ha
  · rename_i hq
    cases ha
    rw [hq, StateExpr.close_val]
    exact result
  · rename_i hq
    obtain ⟨_, l', hl', hk, _⟩ := inv.defs q a ha
    have neq : regs q ≠ regs l.sym.key := by
      rw [← hk]
      exact layout.apart l' hl' l hl (by rw [hk]; exact hq)
    rw [other _ (by rw [← hk]; exact layout.below l' hl') neq]
    exact matched q a ha

/-- One source assignment and one target assignment block preserve the same evolving
state. Source overflow is the UB escape; otherwise both compute the current RHS value.
The target path is nonempty and ends at the chosen loop header. -/
theorem assign_step {file : Program} {labels : Labels} {e : EE} {x : Sym} {t : Term}
    (shape : StateStmt.assignStmt file e = some (x, t))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option IntExpr.Term}
    (inv : Inv env m ls ds) {l : Local} (hl : l ∈ ls) (key : x.key = l.sym.key)
    (defined : Defined ds t = true) (k : List Frame)
    (regs : Key → Mir.Reg) (d : Nat) (layout : Layout regs d ls)
    (fr : Lir.Frame Mir.Reg) (matched : Registers regs ds fr)
    (p : Lir.Prog Mir.Reg) (f : Lir.FuncId) (label header : Lir.Label)
    (block : p.block? f label = some (LoopBlocks.assignBlock regs d l.sym.key t header))
    (stack : List (Lir.Activation Mir.Reg)) (mem : Lir.Memory) :
    StateStmt.Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
      ∃ m' fr', m'.stdout = m.stdout ∧
        Inv env m' ls (update ds l.sym.key (some (close (defsOf ds) t))) ∧
        Registers regs (update ds l.sym.key (some (close (defsOf ds) t))) fr' ∧
        PureEval.Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, k, m'⟩ ∧
        Relation.TransGen (Lir.Step p) ⟨⟨f, label, 0⟩, fr, stack, mem⟩
          ⟨⟨f, header, 0⟩, fr', stack, mem⟩ := by
  rcases StateStmt.assign_runs shape inv hl key defined k with ub | ⟨ok, m', out, inv', source⟩
  · exact .inl ub
  · obtain ⟨fr', target, result, other⟩ := LoopBlocks.assign_steps regs (values (defsOf ds)) d
      l.sym.key t header p f label block fr stack mem ok (reads layout inv matched defined)
    exact .inr ⟨m', fr', out, inv', registers_assign layout inv matched hl result other,
      source, target⟩

end Silmaril.Compile.Core.Verified.StateLoopStep
