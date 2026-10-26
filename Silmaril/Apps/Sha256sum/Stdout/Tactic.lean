module

public import Silmaril.Apps.Sha256sum.Lift.Tactic
public meta import Lean

/-! # Symbolic execution of `sha256sum-min` routines with stack frames and a return address

Status: **VERIFIED** (lemmas: no `sorry`, standard axioms only); tactics are tested by the
proofs that use them (`Stdout.OutFlush`).

`Lift.x86_step` executes one listed instruction inside `Sys.wp`. A *routine* (a function with
a return address, called from many sites) needs three more things, which this file adds:

* **Cut tests by `Nat` equality only.** A routine's cut test says "the program counter is a
  loop head, or is outside the routine" (so the return address, a parameter, is a cut). It is
  stated as a disjunction of `n == lit` tests and evaluated by per-address lemmas
  (`cutLemmas`), never by `decide`: a `decide`-based range test makes the kernel unfold `wp`
  and time out.
* **Reads of the routine's own stack slots** (`pop`, `ret`): `rd_same` reads back the bytes a
  store wrote, given read permission before the store, which `perm_wb` carries across earlier
  stores (stores never change the mapping). `xperm` proves that permission from a frame
  hypothesis `Permitted .read lo len` of the entry memory.
* **Reducible-transparency read resolution** (`xmem`). Side conditions are separate goals that
  must be closed (a failing `by` block inside a `rw` term is elaborated to `sorry` with only
  an error message, which would let a failed disjointness proof through). `Lift.x86_mem` compares memory
  terms at default transparency, which unfolds `readWith` and exhausts the recursion limit
  on a literal address; `xmem` compares at reducible transparency, and resolves a read through
  a disjoint store, a same-span store (`rd_same`), or a fact of the precondition.

`xstep [lemmas]` is `x86_step` with `xmem`, and with `lemmas` (the cut lemmas) applied after
every memory resolution as well, so a `wpNext` test is always decided.
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Stdout

open Silmaril.Process (Memory Byte Access)

/-- A store keeps the mapping, so it keeps every permission. -/
theorem perm_wb {m m' : Memory} {a : Nat} {bs : List Byte} (hw : m.writeBytes a bs = some m')
    {acc : Access} {x n : Nat} (h : m.Permitted acc x n) : m'.Permitted acc x n := by
  have w := (Memory.writesOnly_iff_writesWithin _ _ _ _).mp (Memory.writeBytes_writesOnly hw)
  exact (w.permitted_iff acc x n).mpr h

/-- **Read-back of a store** (a `pop` of a pushed register, a `ret` to a pushed address). -/
theorem rd_same {m m' : Memory} {a : Nat} {bs : List Byte} (hw : m.writeBytes a bs = some m')
    (hp : m.Permitted .read a bs.length) : m'.readWith .read a bs.length = some bs :=
  Lift.readWith_wb_same hw hp

/-- `rd_same` at a stated length (the length of an encoded word is not syntactically 8). -/
theorem rd_same' {m m' : Memory} {a : Nat} {bs : List Byte} (hw : m.writeBytes a bs = some m')
    {n : Nat} (hn : bs.length = n) (hp : m.Permitted .read a n) :
    m'.readWith .read a n = some bs := by
  subst hn; exact rd_same hw hp

/-! ### Stack-pointer arithmetic normal form: `x - lit` -/

theorem bv_sub_sub {w : Nat} (x : BitVec w) (a b : Nat) :
    x - BitVec.ofNat w a - BitVec.ofNat w b = x - BitVec.ofNat w (a + b) := by
  rw [BitVec.sub_sub, BitVec.ofNat_add]

theorem bv_sub_add {w : Nat} (x : BitVec w) (a b : Nat) (h : b ≤ a) :
    x - BitVec.ofNat w a + BitVec.ofNat w b = x - BitVec.ofNat w (a - b) := by
  have : BitVec.ofNat w a = BitVec.ofNat w (a - b) + BitVec.ofNat w b := by
    rw [← BitVec.ofNat_add]; congr 1; omega
  rw [this]; ring

theorem bv_sub_zero {w : Nat} (x : BitVec w) : x - BitVec.ofNat w 0 = x := by simp

end Silmaril.Apps.Sha256sum.Stdout

/-- Span arithmetic: `Lift.x86_disj`, also when there is nothing to simplify. -/
macro "xdisj" : tactic => `(tactic| ((try simp only [Silmaril.Machine.LittleEndian.encodeWords_length,
  Silmaril.X86.length_encodeWords_singleton, Silmaril.X86.Ext.length_leBytes, List.length_cons,
  List.length_nil, BitVec.toNat_sub, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow,
  Nat.reduceMod, Nat.reduceSub, Nat.reduceAdd]) <;> omega))

/-- The length of stored bytes. -/
macro "xlen" : tactic => `(tactic| (simp only [Silmaril.X86.length_encodeWords_singleton,
  Silmaril.Machine.LittleEndian.encodeWords_length, Silmaril.X86.Ext.length_leBytes,
  List.length_cons, List.length_nil, List.length_map]; done))

namespace Silmaril.Apps.Sha256sum.Stdout

open Lean Elab Tactic Meta in
/-- A hypothesis whose type is `lhs = rhs` with `pred lhs` and `rhs` reducibly equal to `e`. -/
meta def findStore (e : Lean.Expr) : TacticM (Option Lean.Expr) := withMainContext do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, lhs, rhs) := ty.eq? | continue
    if lhs.isAppOfArity ``Silmaril.Process.Memory.writeBytes 3 &&
        rhs.isAppOfArity ``Option.some 2 then
      if ← withReducible (isDefEq (rhs.getArg! 1) e) then return some d.toExpr
  return none

open Lean Elab Tactic Meta in
/-- Read permission of a span of the current memory: through the stores that produced it
(`perm_wb`), down to a frame hypothesis `Permitted acc lo len` of an earlier memory, whose
sub-span it must be (`Permitted.sub`, bounds by `x86_disj`). -/
elab "xperm" : tactic => do
  for _ in [0:64] do
    let done ← withMainContext do
      let g ← instantiateMVars (← getMainTarget)
      unless g.isAppOfArity ``Silmaril.Process.Memory.Permitted 4 do
        throwError "xperm: not a permission goal"
      let some h ← findStore (g.getArg! 0) | return true
      let hs ← Term.exprToSyntax h
      evalTactic (← `(tactic| refine Silmaril.Apps.Sha256sum.Stdout.perm_wb $hs ?_))
      return false
    if done then break
  withMainContext do
  let g ← instantiateMVars (← getMainTarget)
  let mem := g.getArg! 0
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``Silmaril.Process.Memory.Permitted 4 then
      if ← withReducible (isDefEq (ty.getArg! 0) mem) then
        let hs ← Term.exprToSyntax d.toExpr
        let ok ← (do
          evalTactic (← `(tactic|
            (refine Silmaril.X86.Ext.Memory.Permitted.sub $hs ?_ ?_ ?_ <;> xdisj)))
          pure true) <|> pure false
        if ok then return
  throwError "xperm: no frame hypothesis covers the span"

open Lean Elab Tactic Meta in
/-- Resolve the read `e` from the context, comparing terms at reducible transparency:
through a store with a disjoint span, through a store with exactly the read's span
(`rd_same'`, permission by `xperm`), or by a fact `M.readWith … = some _`. -/
meta def resolveReadR (e : Lean.Expr) : TacticM Bool := withMainContext do
  let some mem := Lift.readMem? e | return false
  let lctx ← getLCtx
  for d in lctx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    let some (_, lhs, rhs) := ty.eq? | continue
    if lhs.isAppOfArity ``Silmaril.Process.Memory.writeBytes 3 &&
        rhs.isAppOfArity ``Option.some 2 then
      if ← withReducible (isDefEq (rhs.getArg! 1) mem) then
        let h ← Term.exprToSyntax d.toExpr
        let ok ← (do
          evalTactic (← `(tactic|
            (rw [Silmaril.Apps.Sha256sum.Lift.readWith_wb_disjoint $h ?_]; swap; xdisj)))
          pure true) <|> pure false
        if ok then return true
        let ok ← (do
          let n0 := (← getGoals).length
          evalTactic (← `(tactic|
            (rw [Silmaril.Apps.Sha256sum.Stdout.rd_same' $h ?_ ?_]
             all_goals first | xlen | xperm | skip)))
          unless (← getGoals).length == n0 do throwError "xmem: side condition left"
          pure true) <|> pure false
        if ok then return true
    if lhs.isAppOfArity ``Silmaril.Process.Memory.readWith 4 then
      if ← withReducible (isDefEq lhs e) then
        let h ← Term.exprToSyntax d.toExpr
        let ok ← (do evalTactic (← `(tactic| rw [$h:term])); pure true) <|> pure false
        if ok then return true
  return false

end Silmaril.Apps.Sha256sum.Stdout

/-- Resolve or case on the first memory access of the goal (see `resolveReadR`), then
simplify with the given lemmas. -/
syntax "xmem" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

open Lean Elab Tactic Meta in
elab_rules : tactic
  | `(tactic| xmem $[[$ls,*]]?) => withMainContext do
    let ls : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := match ls with
      | some ls => ls.getElems
      | none => #[]
    let g ← instantiateMVars (← getMainTarget)
    let some e := Silmaril.Apps.Sha256sum.Lift.findMemAccess g
      | throwError "xmem: no memory access in the goal"
    if ← Silmaril.Apps.Sha256sum.Stdout.resolveReadR e then
      evalTactic (← `(tactic| try x86_simp [$ls,*, Bool.false_eq_true, Option.bind_some,
        Silmaril.X86.wordOfBytes?_encodeWords, Silmaril.Apps.Sha256sum.Stdout.bv_sub_sub,
        Silmaril.Apps.Sha256sum.Stdout.bv_sub_add, Silmaril.Apps.Sha256sum.Stdout.bv_sub_zero]))
      return
    withMainContext do
    let stx ← Term.exprToSyntax e
    let h := mkIdent (← mkFreshUserName `hmem)
    evalTactic (← `(tactic| (cases $h:ident : $stx:term <;> x86_simp [$h:ident, $ls,*, Bool.false_eq_true,
      Option.bind_none, Option.bind_some, Silmaril.X86.wordOfBytes?_encodeWords])))

/-- One instruction of a routine's VC: `x86_step` with `xmem`, the given lemmas (cut tests)
in every simplification. -/
syntax "xstep" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| xstep) => `(tactic| xstep [Bool.false_eq_true])
  | `(tactic| xstep [$ls,*]) => `(tactic|
      (refine Silmaril.Apps.Sha256sum.Lift.wp_instr' (by assumption) (by assumption)
          (by first | rfl | assumption) (by rfl) ?_
       x86_simp [$ls,*, Bool.false_eq_true, Silmaril.X86.popWord, Option.bind_eq_bind,
         Option.bind_some, Option.pure_def, Silmaril.X86.wordOfBytes?_encodeWords,
         Silmaril.Apps.Sha256sum.Stdout.bv_sub_sub, Silmaril.Apps.Sha256sum.Stdout.bv_sub_add,
         Silmaril.Apps.Sha256sum.Stdout.bv_sub_zero]
       try dsimp only [Silmaril.X86.Ext.Sz.bits, Silmaril.X86.Ext.Sz.bytes]
       try x86_simp [$ls,*, Bool.false_eq_true, Silmaril.X86.popWord, Option.bind_eq_bind,
         Option.bind_some, Option.pure_def, Silmaril.X86.wordOfBytes?_encodeWords,
         Silmaril.Apps.Sha256sum.Stdout.bv_sub_sub, Silmaril.Apps.Sha256sum.Stdout.bv_sub_add,
         Silmaril.Apps.Sha256sum.Stdout.bv_sub_zero]
       repeat xmem [$ls,*]
       try intro))
