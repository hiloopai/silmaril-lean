module

public import Silmaril.Compiler.Core.Verified.TyInput.Defs
public import Silmaril.Compiler.Core.Verified.TyStmt.Defs
/-! # Typed mutable slots and their current target registers

The definitions in `TyMem.Inv` witness the values stored in Core objects. They are
used only in proofs: emitted expressions read the current registers. Typed stores
include the destination conversion, even when the RHS reads that destination.
The step lemmas retain allocation metadata for the CFG's exit budget and expose
productive target paths through ordinary Lir blocks.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.TyLoopStep

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Dynamics
open Silmaril.Machine
open TyExpr (Key Term zero values close)
open TyMem (Local Inv Defined Typed defsOf update)

/-- Distinct local registers below the temporary base, at every integer width. -/
structure Layout (regs : Key → Mir.Reg) (d : Nat) (ls : List Local) : Prop where
  below : ∀ l ∈ ls, regs l.sym.key < d
  apart : ∀ a ∈ ls, ∀ b ∈ ls, a.sym.key ≠ b.sym.key → regs a.sym.key ≠ regs b.sym.key

/-- Current register words agree with the proof witnesses for defined slots. -/
def Registers (regs : Key → Mir.Reg) (ds : Key → Option Term) (fr : Lir.Frame Mir.Reg) : Prop :=
  ∀ q t, ds q = some t → fr.get (regs q) = some (BitVec.ofInt 64 (t.val zero))

/-- Every defined source read has a current target word below the temporaries. -/
theorem reads {regs : Key → Mir.Reg} {d : Nat} {ls : List Local} {env : Env}
    {m : Mem.Concrete.State} {ds : Key → Option Term} {fr : Lir.Frame Mir.Reg}
    (layout : Layout regs d ls) (inv : Inv env m ls ds) (matched : Registers regs ds fr)
    {t : Term} (defined : Defined ds t = true) :
    ∀ q ∈ t.vars, regs q.1 < d ∧
      fr.get (regs q.1) = some (BitVec.ofInt 64 (values (defsOf ds) q.1)) := by
  intro q hq
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (List.all_eq_true.mp defined q hq)
  obtain ⟨_, l, hl, hk, _⟩ := inv.defs q.1 a ha
  refine ⟨by rw [← hk]; exact layout.below l hl, ?_⟩
  simpa [values, defsOf, ha] using matched q.1 a ha

/-- Updating a slot's register keeps every other slot matched, including mixed widths. -/
theorem registers_assign {regs : Key → Mir.Reg} {d : Nat} {ls : List Local} {env : Env}
    {m : Mem.Concrete.State} {ds : Key → Option Term} {fr : Lir.Frame Mir.Reg}
    (layout : Layout regs d ls) (inv : Inv env m ls ds) (matched : Registers regs ds fr)
    {l : Local} (hl : l ∈ ls) {t : Term} {fr' : Lir.Frame Mir.Reg}
    (result : fr'.get (regs l.sym.key) = some (BitVec.ofInt 64 (t.val (values (defsOf ds)))))
    (other : ∀ r < d, r ≠ regs l.sym.key → fr'.get r = fr.get r) :
    Registers regs (update ds l.sym.key (some (close (defsOf ds) t))) fr' := by
  intro q a ha
  unfold update at ha
  split at ha
  · rename_i hq
    cases ha
    rw [hq, TyExpr.close_val]
    exact result
  · rename_i hq
    obtain ⟨_, l', hl', hk, _⟩ := inv.defs q a ha
    have neq : regs q ≠ regs l.sym.key := by
      rw [← hk]
      exact layout.apart l' hl' l hl (by rw [hk]; exact hq)
    rw [other _ (by rw [← hk]; exact layout.below l' hl') neq]
    exact matched q a ha

/-- Forgetting an unspecified slot needs no target operation. -/
theorem registers_clear {regs : Key → Mir.Reg} {ds : Key → Option Term}
    {fr : Lir.Frame Mir.Reg} (matched : Registers regs ds fr) (q : Key) :
    Registers regs (update ds q none) fr := by
  intro k t ht
  unfold update at ht
  split at ht
  · cases ht
  · exact matched k t ht

/-- Assignment block with explicit conversion to its destination type. -/
def assignBlock (regs : Key → Mir.Reg) (d : Nat) (q : Key) (ity : IntegerType)
    (t : Term) (next : Lir.Label) : Lir.Block Mir.Reg :=
  ⟨(TyInput.assign regs q d (TyStmt.convT ity t)).map .op, .jump next⟩

/-- Destination conversion preserves the well-formedness of the typed RHS. -/
theorem convT_wf {ity : IntegerType} (supported : TyActions.supported ity = true)
    {t : Term} (wf : t.Wf) : (TyStmt.convT ity t).Wf :=
  ⟨⟨supported, rfl⟩, wf, trivial⟩

/-- The target assignment makes a nonempty path, preserving memory and other locals. -/
theorem assign_steps (regs : Key → Mir.Reg) (σ : Key → Int) (d : Nat) (q : Key)
    (ity : IntegerType) (supported : TyActions.supported ity = true) (t : Term) (wf : t.Wf)
    (next : Lir.Label) (p : Lir.Prog Mir.Reg) (f : Lir.FuncId) (label : Lir.Label)
    (block : p.block? f label = some (assignBlock regs d q ity t next))
    (fr : Lir.Frame Mir.Reg) (stack : List (Lir.Activation Mir.Reg)) (mem : Lir.Memory)
    (reads : ∀ k ∈ t.vars, regs k.1 < d ∧ fr.get (regs k.1) = some (BitVec.ofInt 64 (σ k.1))) :
    ∃ fr', Relation.TransGen (Lir.Step p) ⟨⟨f, label, 0⟩, fr, stack, mem⟩
        ⟨⟨f, next, 0⟩, fr', stack, mem⟩ ∧
      fr'.get (regs q) = some (BitVec.ofInt 64 ((TyStmt.convT ity t).val σ)) ∧
      ∀ r < d, r ≠ regs q → fr'.get r = fr.get r := by
  obtain ⟨fr', exec, result, below⟩ := TyInput.assign_exec regs σ (convT_wf supported wf) q d fr mem (by
      simpa [TyInput.Inputs, TyStmt.convT, Term.vars] using reads)
  have path := Lir.steps_execOps (p := p) (os := TyInput.assign regs q d (TyStmt.convT ity t))
    (s := ⟨⟨f, label, 0⟩, fr, stack, mem⟩) (rest := []) block (by simp [assignBlock]) exec
  have fetch := Lir.Prog.fetch_eq_term (p := p)
    (pt := ⟨f, label, (TyInput.assign regs q d (TyStmt.convT ity t)).length⟩)
    block (by simp [assignBlock])
  refine ⟨fr', ?_, result, below⟩
  apply Relation.TransGen.tail' path
  change Lir.step p _ = .running _
  simp [Lir.step, fetch, assignBlock]

/-- A Core typed assignment and its Lir block preserve the mutable slot/register
relation and the allocation budget. Overflow is an explicit source escape. -/
theorem assign_step {file : Program} {labels : Labels} {e : EE} {x : Sym}
    {ity : IntegerType} {t : Term} (shape : TyStmt.assignStmt file e = some (x, ity, t))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option Term}
    (inv : Inv env m ls ds) {l : Local} (hl : l ∈ ls) (key : x.key = l.sym.key)
    (type : l.ity = ity) (defined : Defined ds t = true) (typed : Typed ls t) (wf : t.Wf)
    (k : List Frame) (regs : Key → Mir.Reg) (d : Nat) (layout : Layout regs d ls)
    (fr : Lir.Frame Mir.Reg) (matched : Registers regs ds fr)
    (p : Lir.Prog Mir.Reg) (f : Lir.FuncId) (label next : Lir.Label)
    (block : p.block? f label = some (assignBlock regs d l.sym.key ity t next))
    (stack : List (Lir.Activation Mir.Reg)) (mem : Lir.Memory) :
    StateStmt.Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
      ∃ m' fr', m'.stdout = m.stdout ∧ TyStmt.SameAlloc m m' ∧
        Inv env m' ls (update ds l.sym.key (some (close (defsOf ds) (TyStmt.convT ity t)))) ∧
        Registers regs (update ds l.sym.key (some (close (defsOf ds) (TyStmt.convT ity t)))) fr' ∧
        PureEval.Reaches file labels ⟨.effectExpr e env, k, m⟩ ⟨.value .unit, k, m'⟩ ∧
        Relation.TransGen (Lir.Step p) ⟨⟨f, label, 0⟩, fr, stack, mem⟩
          ⟨⟨f, next, 0⟩, fr', stack, mem⟩ := by
  rcases TyStmt.assign_runs shape inv hl key type defined typed k with
    ub | ⟨m', out, alloc, inv', source⟩
  · exact .inl ub
  · have hs : TyActions.supported ity = true := by rw [← type]; exact (inv.live l hl).1
    obtain ⟨fr', target, result, other⟩ := assign_steps regs (values (defsOf ds)) d l.sym.key
      ity hs t wf next p f label block fr stack mem (reads layout inv matched defined)
    exact .inr ⟨m', fr', out, alloc, inv',
      registers_assign layout inv matched hl result other, source, target⟩

/-- Initializing a typed local uses the same target block as assignment. The source
retains its store annotations for the CFG's pending-statement relation. -/
theorem init_step {file : Program} {labels : Labels} {e : EE} {x : Sym}
    {ity : IntegerType} {t : Term} (shape : TyStmt.initStmt file e = some (x, ity, t))
    {env : Env} {m : Mem.Concrete.State} {ls : List Local} {ds : Key → Option Term}
    (inv : Inv env m ls ds) {l : Local} (hl : l ∈ ls) (key : x.key = l.sym.key)
    (type : l.ity = ity) (defined : Defined ds t = true) (typed : Typed ls t) (wf : t.Wf)
    (k : List Frame) (regs : Key → Mir.Reg) (d : Nat) (layout : Layout regs d ls)
    (fr : Lir.Frame Mir.Reg) (matched : Registers regs ds fr)
    (p : Lir.Prog Mir.Reg) (f : Lir.FuncId) (label next : Lir.Label)
    (block : p.block? f label = some (assignBlock regs d l.sym.key ity t next))
    (stack : List (Lir.Activation Mir.Reg)) (mem : Lir.Memory) :
    StateStmt.Overflows (file := file) (labels := labels) ⟨.effectExpr e env, k, m⟩ ∨
      ∃ m' fr' xs, m'.stdout = m.stdout ∧ TyStmt.SameAlloc m m' ∧
        Inv env m' ls (update ds l.sym.key (some (close (defsOf ds) (TyStmt.convT ity t)))) ∧
        Registers regs (update ds l.sym.key (some (close (defsOf ds) (TyStmt.convT ity t)))) fr' ∧
        PureEval.Reaches file labels ⟨.effectExpr e env, k, m⟩
          ⟨.value .unit, .annotations xs :: k, m'⟩ ∧
        Relation.TransGen (Lir.Step p) ⟨⟨f, label, 0⟩, fr, stack, mem⟩
          ⟨⟨f, next, 0⟩, fr', stack, mem⟩ := by
  rcases TyStmt.init_runs shape inv hl key type defined typed k with
    ub | ⟨m', xs, out, alloc, inv', source⟩
  · exact .inl ub
  · have hs : TyActions.supported ity = true := by rw [← type]; exact (inv.live l hl).1
    obtain ⟨fr', target, result, other⟩ := assign_steps regs (values (defsOf ds)) d l.sym.key
      ity hs t wf next p f label block fr stack mem (reads layout inv matched defined)
    exact .inr ⟨m', fr', xs, out, alloc, inv',
      registers_assign layout inv matched hl result other, source, target⟩

end Silmaril.Compile.Core.Verified.TyLoopStep
