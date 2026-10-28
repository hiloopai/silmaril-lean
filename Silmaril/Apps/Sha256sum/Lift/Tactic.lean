module

public import Silmaril.Apps.Sha256sum.Lift.Wp8
public import Silmaril.X86.Ext.SymExec
public import Silmaril.Apps.Sha256sum.Lift.Mem
public meta import Lean

/-! # Tactics for the `sha256sum-min` VC

* `sx32_pos`, `sx32_neg`, `sx8_pos`, `sx8_neg`: sign extension of a literal displacement, as
  lemma applications. (`BitVec.reduceSignExtend` followed by `BitVec.reduceAdd` produces
  `rfl` proofs that the kernel rejects with "deep recursion" on 64-bit targets.)
* `x86_simp`: one `simp only` pass that executes an `Ext`/`Ext8` instruction on a state with a
  literal `rip`, evaluates the next address and the cut test.
* `x86_step`: `wp_instr` at the current address (the instruction is found by `rfl` in the
  kernel-checked listing), `x86_simp`, split the memory-access matches (a failed access is a
  fault, which needs nothing), and introduce the next state's `Code`.
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Lift

theorem sx32_pos {n : Nat} (h : n < 2^31) :
    (BitVec.ofNat 32 n).signExtend 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_signExtend]
  simp only [BitVec.msb_eq_decide, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  simp
  split <;> omega

theorem sx32_neg {n : Nat} (h1 : 2^31 ≤ n) (h2 : n < 2^32) :
    (BitVec.ofNat 32 n).signExtend 64 = BitVec.ofNat 64 (n + (2^64 - 2^32)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_signExtend]
  simp only [BitVec.msb_eq_decide, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  simp
  split <;> omega

theorem sx8_pos {n : Nat} (h : n < 2^7) :
    (BitVec.ofNat 8 n).signExtend 64 = BitVec.ofNat 64 n := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_signExtend]
  simp only [BitVec.msb_eq_decide, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  simp
  split <;> omega

theorem sx8_neg {n : Nat} (h1 : 2^7 ≤ n) (h2 : n < 2^8) :
    (BitVec.ofNat 8 n).signExtend 64 = BitVec.ofNat 64 (n + (2^64 - 2^8)) := by
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_signExtend]
  simp only [BitVec.msb_eq_decide, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  simp
  split <;> omega

open Silmaril.X86 (State Reg Word Flags) in
/-- `exec` rebuilds a state from a written one; put the write back outside. -/
theorem mk_write (s : State) (r : Reg) (v : Word) (x : Word) (f : Flags) (fs : Word) :
    State.mk (s.write r v).regs x f fs = (State.mk s.regs x f fs).write r v := rfl

open Silmaril.X86 (State Reg Word Flags) in
theorem read_mk (regs : Silmaril.Machine.RegisterFile Reg Word) (x : Word) (f : Flags) (fs : Word)
    (q : Reg) : (State.mk regs x f fs).read q = regs q := rfl

open Silmaril.X86 (State Reg Word Flags) in
theorem write_write_same (s : State) (r : Reg) (v w : Word) :
    (s.write r v).write r w = s.write r w := by
  cases s; simp only [State.write, State.mk.injEq, and_true]
  funext q; unfold Silmaril.Machine.RegisterFile.write; split <;> rfl

theorem sub_sub_lit (x : Silmaril.X86.Word) (a b : Nat) :
    x - BitVec.ofNat 64 a - BitVec.ofNat 64 b = x - BitVec.ofNat 64 (a + b) := by
  rw [BitVec.sub_sub, BitVec.ofNat_add]

open Silmaril.X86 (State Reg Word Flags) in
theorem core_regs (s : State) (q : Reg) : s.regs q = s.read q := rfl

end Silmaril.Apps.Sha256sum.Lift

/-- Execute one instruction symbolically and evaluate the next address and the cut test. -/
syntax "x86_simp" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| x86_simp) => `(tactic| x86_simp [])
  | `(tactic| x86_simp [$ls,*]) => `(tactic| simp only [Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec,
  Silmaril.X86.Ext.retire, Silmaril.X86.Ext.aluStep, Silmaril.X86.Ext.aluStepR,
  Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.writeRM, Silmaril.X86.Ext.Sz.read,
  Silmaril.X86.Ext.Sz.write, Silmaril.X86.Ext.Sz.bits, Silmaril.X86.Ext.AluOp.resultN,
  Silmaril.X86.pushWord,
  Silmaril.Apps.Sha256sum.Lift.mk_write, Silmaril.Apps.Sha256sum.Lift.read_mk,
  Silmaril.Apps.Sha256sum.Lift.core_regs, Silmaril.Apps.Sha256sum.Lift.write_write_same,
  Silmaril.Apps.Sha256sum.Lift.sub_sub_lit, BitVec.sub_sub, Silmaril.X86.Ext.Mem.addr,
  Silmaril.X86.Ext.Mem.ofReg, Silmaril.X86.Ext.Mem.ofRip, Silmaril.X86.Ext.Mem.ofIndex,
  Silmaril.X86.Ext.Index.value, Silmaril.X86.Ext.Sz.bytes, Silmaril.X86.Ext.Base.value_reg,
  Silmaril.X86.Ext.Base.value_none, Silmaril.X86.Ext.Base.value_rip, Option.map_none,
  Option.getD_none, Option.getD_some, BitVec.add_zero, BitVec.zero_add, BitVec.reduceSignExtend, Option.map_id', Option.map_map,
  Function.comp_def,
  Silmaril.X86.State.read_write_same, Silmaril.X86.State.read_write_other,
  Silmaril.X86.State.write_rip, Silmaril.X86.State.write_flags, Silmaril.X86.State.write_fsBase,
  Silmaril.X86.Ext.read_with_rip, Silmaril.X86.Ext.read_mk_regs, Silmaril.X86.Ext.rip_mk,
  Silmaril.X86.Ext.read_with_flags, Silmaril.X86.Ext.rip_with_flags,
  Silmaril.Apps.Sha256sum.Sys.wpNext,
  Silmaril.Apps.Sha256sum.Lift.sx32_pos, Silmaril.Apps.Sha256sum.Lift.sx32_neg,
  Silmaril.Apps.Sha256sum.Lift.sx8_pos, Silmaril.Apps.Sha256sum.Lift.sx8_neg,
  BitVec.reduceAdd, BitVec.reduceSub, BitVec.reduceToNat, BitVec.toNat_ofNat, Nat.reduceMod,
  Nat.reducePow, Nat.reduceAdd, Nat.reduceSub, Nat.reduceLT, Nat.reduceLeDiff, Nat.reduceBEq,
  Nat.reduceEqDiff, beq_self_eq_true, ite_true, ite_false, Bool.false_eq_true, reduceIte,
  Option.map_some, Option.map_none, reduceCtorEq, Silmaril.Process.Memory.readBytes,
  Silmaril.X86.Ext.leValue_leBytes,
  Silmaril.X86.Ext.loadN, Silmaril.X86.Ext.storeN, ne_eq, not_false_eq_true, implies_true,
  BitVec.reduceSetWidth, BitVec.xor_self, BitVec.setWidth_zero, BitVec.setWidth_eq, true_and,
  and_true, $ls,*])

namespace Silmaril.Apps.Sha256sum.Lift

open Lean Elab Tactic Meta in
/-- The first memory access (`writeBytes`, `readBytes`) left in the goal by `x86_simp`. -/
meta def findMemAccess (e : Lean.Expr) : Option Lean.Expr :=
  e.find? fun t =>
    (t.isAppOfArity ``Silmaril.Process.Memory.writeBytes 3 ||
      t.isAppOfArity ``Silmaril.Process.Memory.readWith 4) && !t.hasLooseBVars

/-- Disjointness of two spans of the VC, by `bv_omega` over the context. -/
macro "x86_disj" : tactic => `(tactic| (simp only [Silmaril.Machine.LittleEndian.encodeWords_length,
  Silmaril.X86.length_encodeWords_singleton, Silmaril.X86.Ext.length_leBytes, List.length_cons,
  List.length_nil, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow,
  Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd] <;> omega))

open Lean Elab Tactic Meta in
/-- The memory of a `readWith`. -/
meta def readMem? (e : Lean.Expr) : Option Lean.Expr :=
  if e.isAppOfArity ``Silmaril.Process.Memory.readWith 4 then some (e.getArg! 0) else none

open Lean Elab Tactic Meta in
/-- Try to resolve the read `e` from the context: through a store hypothesis
`_.writeBytes _ _ = some M` with a disjoint span, or by a fact `M.readWith … = some _`. -/
meta def resolveRead (e : Lean.Expr) : TacticM Bool := withMainContext do
  let some mem := readMem? e | return false
  let lctx ← getLCtx
  for d in lctx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, lhs, rhs) := ty.eq? | continue
    -- a store producing `mem`
    if lhs.isAppOfArity ``Silmaril.Process.Memory.writeBytes 3 &&
        rhs.isAppOfArity ``Option.some 2 then
      if ← isDefEq (rhs.getArg! 1) mem then
        let h ← Term.exprToSyntax d.toExpr
        let ok ← (do
          evalTactic (← `(tactic| rw [Silmaril.Apps.Sha256sum.Lift.readWith_wb_disjoint $h (by x86_disj)]))
          pure true) <|> pure false
        if ok then return true
    -- a fact about this exact read
    if lhs.isAppOfArity ``Silmaril.Process.Memory.readWith 4 then
      if ← isDefEq lhs e then
        let h ← Term.exprToSyntax d.toExpr
        let ok ← (do evalTactic (← `(tactic| rw [$h:term])); pure true) <|> pure false
        if ok then return true
  return false

open Lean Elab Tactic Meta in
/-- `x86_mem`: resolve or case on the first memory access of the goal. A read is first
resolved from the context (`resolveRead`); otherwise the access is cased on: the failing case
is a fault (closed by `x86_simp`, usually to `True`), the succeeding one keeps the access
equation as a hypothesis `hmem…` for later reads. -/
elab "x86_mem" : tactic => withMainContext do
  let g ← instantiateMVars (← getMainTarget)
  let some e := findMemAccess g | throwError "x86_mem: no memory access in the goal"
  if ← resolveRead e then
    evalTactic (← `(tactic| try x86_simp))
    return
  withMainContext do
  let stx ← Term.exprToSyntax e
  let h := mkIdent (← mkFreshUserName `hmem)
  evalTactic (← `(tactic| (cases $h:ident : $stx:term <;> x86_simp [$h:ident])))

end Silmaril.Apps.Sha256sum.Lift

/-- One instruction of the VC: find it in the listing, execute it, assume the next `Code`. -/
syntax "x86_step" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| x86_step) => `(tactic| x86_step [])
  | `(tactic| x86_step [$ls,*]) => `(tactic|
      (refine Silmaril.Apps.Sha256sum.Lift.wp_instr' (by assumption) (by assumption)
          (by first | rfl | assumption) (by rfl) ?_
       x86_simp [$ls,*]
       try dsimp only [Silmaril.X86.Ext.Sz.bits, Silmaril.X86.Ext.Sz.bytes]
       try x86_simp [$ls,*]
       repeat x86_mem
       try intro))

