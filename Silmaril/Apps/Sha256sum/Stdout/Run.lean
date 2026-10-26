module

public import Silmaril.Apps.Sha256sum.Stdout.Tactic
public import Silmaril.Process.LPS.Problems.GnuSha256sum.SysGlue
public import Silmaril.X86.SegVC.Tactic
public meta import Lean

/-! # Retiring runs of `sha256sum-min` routines, for `GStep` segments

Status: **VERIFIED** (lemmas: no `sorry`, standard axioms only).

`Lift.wp` (the VC of the lift track) is a *safety* VC: a faulting instruction needs nothing.
A `Leads` segment of the middle model (`GnuSha256sum.GStep`) needs *progress* as well, so
here every instruction must retire. `RunsTo Q s` says that the `r11`-free internal steps
(`GnuSha256sum.retStep`, the silent steps of `GStep`) take `s` to a state satisfying `Q`.

* `run_instr'`: one listed instruction (`Lift.instrAt`), in the retiring case only; the
  faulting cases are `False`. `rstep` is the tactic (the `xstep` of `Stdout.Tactic` over this
  lemma), with `rmem`: a store is resolved by its write permission (`writeBytes_ne_none`,
  permission by `xperm`), never cased into a fault.
* `RunsTo.leads`: a run followed by a `Leads` segment from its end is a `Leads` segment
  (`GnuSha256sum.leads_seq`).
* `trap_sc3`: the `syscall` of `sc3` (`0x40101c`) is a trap (`GnuSha256sum.Trap`).
* `read_snoc`: a one-byte store at the end of a read span extends the read (the buffer
  invariant of `out_putc`).
-/

@[expose] public section

namespace Silmaril.Apps.Sha256sum.Stdout

open Silmaril.Apps.Sha256sum Silmaril.Apps.Sha256sum.X86Sys
open Silmaril.Process (Memory Byte Access)
open Silmaril.Machine.Execution (Reaches run run_succ)
open Silmaril.Process.LPS.Problems.GnuSha256sum (retStep GS GStep Ok Trap leads_seq Ev)
open Silmaril.Process.LPS.Problems.Sha256Cli (Leads)

/-- A retiring run from `s` to a state satisfying `Q`. -/
def RunsTo (Q : XState → Prop) (s : XState) : Prop :=
  ∃ t, Reaches retStep s t ∧ Q t

theorem RunsTo.done {Q : XState → Prop} {s : XState} (h : Q s) : RunsTo Q s :=
  ⟨s, Reaches.refl _ _, h⟩

theorem RunsTo.mono {Q Q' : XState → Prop} {s : XState} (h : RunsTo Q s)
    (hq : ∀ t, Q t → Q' t) : RunsTo Q' s :=
  let ⟨t, r, q⟩ := h; ⟨t, r, hq t q⟩

theorem RunsTo.bind {Q Q' : XState → Prop} {s : XState} (h : RunsTo Q s)
    (hq : ∀ t, Q t → RunsTo Q' t) : RunsTo Q' s :=
  let ⟨t, r, q⟩ := h
  let ⟨u, r', q'⟩ := hq t q
  ⟨u, r.trans r', q'⟩

theorem RunsTo.cons {Q : XState → Prop} {s t : XState} (hs : retStep s = some t)
    (h : RunsTo Q t) : RunsTo Q s := by
  obtain ⟨u, ⟨n, hn⟩, q⟩ := h
  exact ⟨u, ⟨n + 1, by rw [run_succ, hs, Option.bind_some]; exact hn⟩, q⟩

/-- **One instruction**, retiring. -/
theorem run_instr {Q : XState → Prop} {s : XState} (hf : s.faulted = false)
    (hc : Lift.Code s.memory) {i : X86.Ext8.Instr} {n : Nat}
    (hl : Lift.instrAt s.core.rip.toNat = some (i, n))
    (h : match X86.Ext8.exec i s.core s.memory n with
      | .ok c m => Lift.Code m → RunsTo Q ({ s with core := c, memory := m } : XState)
      | _ => False) :
    RunsTo Q s := by
  have e := Lift.instrAt_ok hl
  have hstep := hc.step e.inText rfl e.notSyscall e.decode e.pos e.le
  cases hx : X86.Ext8.exec i s.core s.memory n with
  | ok c m =>
    rw [hx] at h
    refine RunsTo.cons ?_ (h (hc.of_ro (X86.Ext8.exec8_ro hx)))
    rw [hx] at hstep
    simp [retStep, hf, hstep, Silmaril.Process.CLI.X86Linux.execResult]
  | _ => rw [hx] at h; exact h.elim

/-- `run_instr` at a literal address. -/
theorem run_instr' {Q : XState → Prop} {s : XState} (hf : s.faulted = false)
    (hc : Lift.Code s.memory) {addr : Nat} (hrip : s.core.rip = BitVec.ofNat 64 addr)
    {i : X86.Ext8.Instr} {n : Nat} (hl : Lift.instrAt addr = some (i, n))
    (h : match X86.Ext8.exec i s.core s.memory n with
      | .ok c m => Lift.Code m → RunsTo Q ({ s with core := c, memory := m } : XState)
      | _ => False) :
    RunsTo Q s := by
  have e := Lift.instrAt_ok hl
  have hb : addr < 2 ^ 64 := by
    have := e.inText.2; unfold Lift.textBase Lift.textSize Silmaril.X86.maxInstrLength at this
    omega
  refine run_instr hf hc ?_ h
  rw [hrip, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hb]; exact hl

/-- A store into writable memory succeeds. -/
theorem writeBytes_ne_none {m : Memory} {a : Nat} {bs : List Byte}
    (hp : m.Permitted .write a bs.length) : m.writeBytes a bs ≠ none := by
  have hchk : m.checkSpan .write a bs.length = true := hp
  unfold Memory.writeBytes; rw [hchk]; simp

/-- **A run, then a segment.** -/
theorem RunsTo.leads {w : World} {message : List Byte} {Post : GS → List Ev → Prop}
    {g : GS} {h : List Ev} {Q : XState → Prop} (r : RunsTo Q g.x) (running : g.exited = none)
    (ok : Ok message g h)
    (k : ∀ t, Q t → Leads (GStep w) (Ok message) Post { g with x := t } h) :
    Leads (GStep w) (Ok message) Post g h :=
  let ⟨t, rr, q⟩ := r
  leads_seq rr running ok (k t q)

/-- The text bytes of the `syscall` of `sc3`. -/
theorem text_sc3 : (Lift.text.drop (0x40101c - Lift.textBase)).take 2 = [0x0f, 0x05] := by
  decide +kernel

/-- The `syscall` of `sc3` is a trap. -/
theorem trap_sc3 {s : XState} (hc : Lift.Code s.memory) (hrip : s.core.rip = 0x40101c#64) :
    Trap s := by
  unfold Trap
  rw [hrip, show (0x40101c#64 : Silmaril.X86.Word).toNat = 0x40101c from rfl,
    hc.fetch (by decide) (by decide) (by decide), text_sc3]

/-- **Appending one byte** to a read span (`obuf[olen++] = c`). -/
theorem read_snoc {m m' : Memory} {a k : Nat} {xs : List Byte} {b : Byte}
    (hr : m.readWith .read a k = some xs) (hw : m.writeBytes (a + k) [b] = some m')
    (hp : m.Permitted .read (a + k) 1) : m'.readWith .read a (k + 1) = some (xs ++ [b]) := by
  have h1 : m'.readWith .read a k = some xs := by
    rw [Lift.readWith_wb_disjoint hw (Or.inl (by simp))]; exact hr
  have h2 : m'.readWith .read (a + k) 1 = some [b] := Lift.readWith_wb_same hw hp
  exact Memory.readWith_append h1 h2

/-- A read of a prefix of a store's span (a 4-byte load of an 8-byte store). -/
theorem rd_prefix {m m' : Memory} {a : Nat} {bs : List Byte} (hw : m.writeBytes a bs = some m')
    {n : Nat} (hn : n < bs.length) (hp : m.Permitted .read a bs.length) :
    m'.readWith .read a n = some (bs.take n) := by
  have := Memory.readWith_sub_range (Lift.readWith_wb_same hw hp) (offset := 0) (len := n)
    (by omega) (by omega)
  simpa using this

theorem leBytes_take_4_8 (v : Silmaril.X86.Word) :
    (X86.Ext.leBytes v 8).take 4 = X86.Ext.leBytes v 4 := by
  simp [X86.Ext.leBytes, List.ofFn_succ]

/-- `read_snoc` at any address term of the stored byte. -/
theorem read_snoc' {m m' : Memory} {a k b : Nat} {xs : List Byte} {x : Byte}
    (hw : m.writeBytes b [x] = some m') (hr : m.readWith .read a k = some xs) (hb : b = a + k)
    (hp : m.Permitted .read b 1) : m'.readWith .read a (k + 1) = some (xs ++ [x]) := by
  subst hb; exact read_snoc hr hw hp

/-- A store inside the footprint keeps a footprint claim. -/
theorem ww_store {m0 m m' : Memory} {F : Nat → Prop} {a : Nat} {bs : List Byte}
    (hw : m.writeBytes a bs = some m') (h : Memory.WritesWithin m0 m F)
    (hin : ∀ x, a ≤ x → x < a + bs.length → F x) : Memory.WritesWithin m0 m' F := by
  have w := (Memory.writesOnly_iff_writesWithin _ _ _ _).mp (Memory.writeBytes_writesOnly hw)
  exact h.trans (w.mono fun x hx => hin x hx.1 hx.2)

end Silmaril.Apps.Sha256sum.Stdout

namespace Silmaril.Apps.Sha256sum.Stdout

open Lean Elab Tactic Meta in
/-- `xfoot [defs]`: a footprint goal `WritesWithin m0 m F`, through the stores that produced
`m` (`ww_store`, each span inside `F` by `omega` after unfolding `defs`), down to a
hypothesis about an earlier memory or `WritesWithin.refl`. -/
meta def xfootCore (ls : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) : TacticM Unit := do
  for _ in [0:64] do
    let done ← withMainContext do
      let g ← instantiateMVars (← getMainTarget)
      unless g.isAppOfArity ``Silmaril.Process.Memory.WritesWithin 3 do
        throwError "xfoot: not a footprint goal"
      let some h ← findStore (g.getArg! 1) | return true
      let hs ← Term.exprToSyntax h
      evalTactic (← `(tactic| refine Silmaril.Apps.Sha256sum.Stdout.ww_store $hs ?_ ?_))
      evalTactic (← `(tactic| rotate_left))
      evalTactic (← `(tactic| intro x hx1 hx2))
      evalTactic (← `(tactic| simp only [$ls,*, Silmaril.Machine.LittleEndian.encodeWords_length,
          Silmaril.X86.length_encodeWords_singleton, Silmaril.X86.Ext.length_leBytes,
          List.length_cons, List.length_nil, BitVec.toNat_sub, BitVec.toNat_add,
          BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod, Nat.reduceSub,
          Nat.reduceAdd] at hx1 hx2 ⊢))
      evalTactic (← `(tactic| omega))
      return false
    if done then break
  evalTactic (← `(tactic| first | assumption | exact Silmaril.Process.Memory.WritesWithin.refl _ _))

end Silmaril.Apps.Sha256sum.Stdout

syntax "xfoot" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| xfoot $[[$ls,*]]?) => do
    let ls : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := match ls with
      | some ls => ls.getElems
      | none => #[]
    Silmaril.Apps.Sha256sum.Stdout.xfootCore ls

namespace Silmaril.Apps.Sha256sum.Stdout

open Lean Elab Tactic Meta in
/-- `resolveReadR` of `Stdout.Tactic`, also when the resolved read closes the goal. -/
meta def resolveRead2 (e : Lean.Expr) : TacticM Bool := withMainContext do
  let some mem := Silmaril.Apps.Sha256sum.Lift.readMem? e | return false
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
          unless (← getGoals).length ≤ n0 do throwError "rmem: side condition left"
          pure true) <|> pure false
        if ok then return true
        let ok ← (do
          let n0 := (← getGoals).length
          evalTactic (← `(tactic|
            (rw [Silmaril.Apps.Sha256sum.Stdout.rd_prefix $h ?_ ?_]
             all_goals first | (simp only [Silmaril.X86.Ext.length_leBytes, Nat.reduceLT,
               Silmaril.X86.length_encodeWords_singleton]; done) | xperm | skip)))
          unless (← getGoals).length ≤ n0 do throwError "rmem: side condition left"
          pure true) <|> pure false
        if ok then return true
    if lhs.isAppOfArity ``Silmaril.Process.Memory.readWith 4 then
      if ← withReducible (isDefEq lhs e) then
        let h ← Term.exprToSyntax d.toExpr
        let ok ← (do evalTactic (← `(tactic| rw [$h:term])); pure true) <|> pure false
        if ok then return true
  return false

open Lean Elab Tactic Meta in
/-- `xmem` with stores resolved by permission: the first memory access of the goal is a read
resolved from the context (`resolveReadR`), or a store, cased with the failing case closed by
`writeBytes_ne_none` (permission by `xperm`). -/
meta def rmemCore (ls : Array (TSyntax `Lean.Parser.Tactic.simpLemma)) : TacticM Unit :=
  withMainContext do
    let g ← instantiateMVars (← getMainTarget)
    let some e := Silmaril.Apps.Sha256sum.Lift.findMemAccess g
      | throwError "rmem: no memory access in the goal"
    if ← resolveRead2 e then
      if (← getGoals).isEmpty then return
      evalTactic (← `(tactic| try x86_simp [$ls,*, Bool.false_eq_true, Option.bind_some,
        Silmaril.Apps.Sha256sum.Stdout.leBytes_take_4_8, Nat.reduceMul, Nat.zero_mod,
        Silmaril.X86.wordOfBytes?_encodeWords, Silmaril.Apps.Sha256sum.Stdout.bv_sub_sub,
        Silmaril.Apps.Sha256sum.Stdout.bv_sub_add, Silmaril.Apps.Sha256sum.Stdout.bv_sub_zero]))
      return
    unless e.isAppOfArity ``Silmaril.Process.Memory.writeBytes 3 do
      throwError "rmem: unresolved read {e}"
    withMainContext do
    let stx ← Term.exprToSyntax e
    let h := mkIdent (← mkFreshUserName `hmem)
    let mv := mkIdent (← mkFreshUserName `mem)
    evalTactic (← `(tactic| obtain ⟨$mv:ident, $h:ident⟩ : ∃ m', $stx:term = some m' :=
      Option.ne_none_iff_exists'.mp
        (Silmaril.Apps.Sha256sum.Stdout.writeBytes_ne_none (by xperm))))
    evalTactic (← `(tactic| (x86_simp [$h:ident, $ls,*, Bool.false_eq_true, Option.bind_none,
          Nat.reduceMul, Nat.zero_mod,
          Option.bind_some, Silmaril.X86.wordOfBytes?_encodeWords,
          Silmaril.Apps.Sha256sum.Stdout.bv_sub_sub, Silmaril.Apps.Sha256sum.Stdout.bv_sub_add,
          Silmaril.Apps.Sha256sum.Stdout.bv_sub_zero])))

end Silmaril.Apps.Sha256sum.Stdout

/-- Resolve the first memory access of a `RunsTo` goal (see `rmemCore`). -/
syntax "rmem" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

open Lean Elab Tactic in
elab_rules : tactic
  | `(tactic| rmem $[[$ls,*]]?) => do
    let ls : Array (TSyntax `Lean.Parser.Tactic.simpLemma) := match ls with
      | some ls => ls.getElems
      | none => #[]
    Silmaril.Apps.Sha256sum.Stdout.rmemCore ls

/-- One retiring instruction of a `RunsTo` goal: `run_instr'`, `x86_simp`, `rmem`. -/
syntax "rstep" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| rstep) => `(tactic| rstep [Bool.false_eq_true])
  | `(tactic| rstep [$ls,*]) => `(tactic|
      (refine Silmaril.Apps.Sha256sum.Stdout.run_instr' (by assumption) (by assumption)
          (by first | rfl | assumption) (by rfl) ?_
       x86_simp [$ls,*, Bool.false_eq_true, Silmaril.X86.popWord, Option.bind_eq_bind,
         Option.bind_some, Option.pure_def, Silmaril.X86.wordOfBytes?_encodeWords,
         Silmaril.Apps.Sha256sum.Stdout.bv_sub_sub, Silmaril.Apps.Sha256sum.Stdout.bv_sub_add,
         Silmaril.Apps.Sha256sum.Stdout.bv_sub_zero, Nat.reduceMul, BitVec.and_self,
         Silmaril.X86.SegVC.eval_logic_e, Silmaril.X86.SegVC.eval_logic_ne,
         Silmaril.X86.SegVC.eval_logic_s, Silmaril.X86.SegVC.eval_logic_ns,
         Silmaril.X86.SegVC.eval_sub_8, Silmaril.X86.SegVC.eval_sub_32,
         Silmaril.X86.SegVC.eval_sub_64, Silmaril.X86.Ext.Cond.afterCmp,
         Silmaril.X86.Ext.AluOp.flagsN]
       try dsimp only [Silmaril.X86.Ext.Sz.bits, Silmaril.X86.Ext.Sz.bytes]
       try x86_simp [$ls,*, Bool.false_eq_true, Silmaril.X86.popWord, Option.bind_eq_bind,
         Option.bind_some, Option.pure_def, Silmaril.X86.wordOfBytes?_encodeWords,
         Silmaril.Apps.Sha256sum.Stdout.bv_sub_sub, Silmaril.Apps.Sha256sum.Stdout.bv_sub_add,
         Silmaril.Apps.Sha256sum.Stdout.bv_sub_zero, Nat.reduceMul, BitVec.and_self,
         Silmaril.X86.SegVC.eval_logic_e, Silmaril.X86.SegVC.eval_logic_ne,
         Silmaril.X86.SegVC.eval_logic_s, Silmaril.X86.SegVC.eval_logic_ns,
         Silmaril.X86.SegVC.eval_sub_8, Silmaril.X86.SegVC.eval_sub_32,
         Silmaril.X86.SegVC.eval_sub_64, Silmaril.X86.Ext.Cond.afterCmp,
         Silmaril.X86.Ext.AluOp.flagsN]
       repeat rmem [$ls,*]
       try intro))

/-- Close the field goals of a cut predicate after a symbolic run: register reads (with the
given equations), permissions (`xperm`), memory reads (`rmem`), footprints (`xfoot`). -/
syntax "rfin" " [" Lean.Parser.Tactic.simpLemma,* "]" " [" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| rfin [$ls,*] [$fs,*]) => `(tactic|
      ((all_goals try dsimp only);
       (all_goals try (simp only [$ls,*, Silmaril.X86.State.read_write_same,
          Silmaril.X86.State.read_write_other, ne_eq, reduceCtorEq, not_false_eq_true,
          Silmaril.Apps.Sha256sum.Lift.read_mk, Silmaril.Apps.Sha256sum.Lift.core_regs,
          List.length_nil, Nat.add_zero, List.length_append]; done));
       (all_goals try (xperm; done));
       (all_goals try ((repeat rmem [Bool.false_eq_true]); done));
       (all_goals try (xfoot [$fs,*]; done))))

namespace Silmaril.Apps.Sha256sum.Stdout

open Lean Elab Tactic Meta in
/-- `xsnoc`: a goal `m'.readWith .read a (k + 1) = some (xs ++ [x])` where `m'` is the result
of a one-byte store: `read_snoc'`, the earlier read by `rmem`, the address by `omega`, the
permission by `xperm`. -/
meta def xsnocCore : TacticM Unit := withMainContext do
  let g ← instantiateMVars (← getMainTarget)
  let some (_, lhs, _) := g.eq? | throwError "xsnoc: not an equation"
  let some mem := Silmaril.Apps.Sha256sum.Lift.readMem? lhs | throwError "xsnoc: not a read"
  let some h ← findStore mem | throwError "xsnoc: no store"
  let hs ← Term.exprToSyntax h
  evalTactic (← `(tactic| refine Silmaril.Apps.Sha256sum.Stdout.read_snoc' $hs ?_ ?_ ?_))
  evalTactic (← `(tactic| (repeat rmem [Bool.false_eq_true])))
  evalTactic (← `(tactic| simp only [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.reducePow,
    Nat.reduceMod]))
  evalTactic (← `(tactic| omega))
  evalTactic (← `(tactic| xperm))

end Silmaril.Apps.Sha256sum.Stdout

elab "xsnoc" : tactic => Silmaril.Apps.Sha256sum.Stdout.xsnocCore
