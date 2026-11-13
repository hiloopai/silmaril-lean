module

public import Silmaril.Compiler.Core.Verified.PrintfIntStmt.Defs
public import Silmaril.Compiler.Core.Verified.StateMem.Defs

/-! # The State slots across an open printf statement

A printf call allocates and kills its argument objects below the current allocation
frontier. Earlier local objects keep their lifetimes, bytes and definitions. The frontier
bounds below are independent of startup's concrete address, so this boundary also works
after string-literal globals have been allocated.
-/

@[expose] public section

namespace Silmaril.Compile.Core.Verified.PrintfState

open Silmaril.Cerberus Silmaril.Cerberus.Core
open Dynamics
open StateMem (Local Inv Defined defsOf)
open StrMem (Keeps)

/-- The State objects lie before the next allocation and above its address frontier. -/
structure Earlier (m : Mem.Concrete.State) (ls : List Local) : Prop where
  ids : ∀ l ∈ ls, l.id < m.nextId
  addrs : ∀ l ∈ ls, m.lastAddress ≤ l.addr

/-- Later allocations and output keep earlier locals before the new frontier. -/
theorem Earlier.keeps {m m' : Mem.Concrete.State} {ls : List Local}
    (earlier : Earlier m ls) (keep : Keeps m m') : Earlier m' ls :=
  ⟨fun l hl => lt_of_lt_of_le (earlier.ids l hl) keep.nextId,
    fun l hl => le_trans keep.last (earlier.addrs l hl)⟩

theorem live_keeps {m m' : Mem.Concrete.State} (keep : Keeps m m')
    {id addr : Int} (older : id < m.nextId) (live : Mem.Concrete.LiveInt m id addr) :
    Mem.Concrete.LiveInt m' id addr := by
  refine ⟨fun dead => live.alive ((keep.dead id older).mp dead), ?_⟩
  obtain ⟨a, ha, rest⟩ := live.found
  exact ⟨a, (keep.alloc id older).trans ha, rest⟩

/-- A call preserving earlier objects preserves their State definitions. -/
theorem inv_keeps {env : Env} {m m' : Mem.Concrete.State} {ls : List Local}
    {ds : StateExpr.Key → Option IntExpr.Term} (inv : Inv env m ls ds)
    (earlier : Earlier m ls) (keep : Keeps m m') : Inv env m' ls ds := by
  refine ⟨inv.env, fun l hl => live_keeps keep (earlier.ids l hl) (inv.live l hl), inv.apart, ?_⟩
  intro q d hd
  obtain ⟨ok, l, hl, key, slot⟩ := inv.defs q d hd
  exact ⟨ok, l, hl, key, PrintfVariadic.slot_keeps slot (earlier.ids l hl) (earlier.addrs l hl) keep⟩

/-- **An open printf statement preserves State**: all earlier definitions survive, prior
output is extended by exactly the formatted value, and the frontier moves at most 32 bytes. -/
theorem printf_reaches {file : Program} {labels : Labels} {ls : List (Sym × List Int)}
    {fenv : Fold.WEnv} {e : Dynamics.EE} {pre suf : List Char} {t : StateExpr.Term}
    (shape : PrintfIntStmt.printfTerm file ls fenv e = some (pre, suf, t))
    {env : Env} {m : Mem.Concrete.State} {locals : List Local}
    {ds : StateExpr.Key → Option IntExpr.Term} (inv : Inv env m locals ds)
    (earlier : Earlier m locals) (defined : Defined ds t = true)
    (ok : t.Ok (StateExpr.values (defsOf ds))) (hr : Fold.EnvSub fenv env)
    (hlit : StrLit.LitEnv ls env m) (hdead : PrintfStmt.DeadBelow m)
    (hroom : 64 ≤ m.lastAddress) (ann : List Annot) (k : List Frame) :
    ∃ m', ReturnConst.Reaches file labels ⟨.effectExpr (.mk ann (.bound e)) env, k, m⟩
        ⟨.value (.loaded (.specified (.integer
          (PrintfIntStmt.text pre suf (t.val (StateExpr.values (defsOf ds)))).length))), k, m'⟩ ∧
      m'.stdout = m.stdout ++ PrintfIntStmt.text pre suf (t.val (StateExpr.values (defsOf ds))) ∧
      Inv env m' locals ds ∧ Earlier m' locals ∧ StrLit.LitEnv ls env m' ∧
      PrintfStmt.DeadBelow m' ∧ m.lastAddress - 32 ≤ m'.lastAddress := by
  obtain ⟨m', run, out, keep, dead, room⟩ := PrintfIntStmt.printfTerm_reaches shape ok hr hlit
    (inv.locs defined) hdead hroom ann k
  exact ⟨m', run, out, inv_keeps inv earlier keep, earlier.keeps keep, hlit.keeps keep, dead, room⟩

end Silmaril.Compile.Core.Verified.PrintfState
