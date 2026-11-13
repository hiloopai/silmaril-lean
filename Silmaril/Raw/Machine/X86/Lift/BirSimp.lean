-- Imported from an earlier development
-- Source: Silmaril/X86/Lift/BirSimp.lean; sha256=8f8cadbf839e34e53f47ea6b17a79b39c0428932a5ac909cc9905ca3ef495375
-- Reproduce with tools/mor/examples/import_x86_lift.rs; declaration namespaces retained.
module

public import Silmaril.Raw.Machine.X86.Lift.BirBlock

/-!
# A verified simplifier for Bir, and the checked lifting entry point

`symExec` produces Bir whose operations are exactly `Ext.exec`'s (`alu 64 add
x y`, `zext 64 e`, address sums with zero displacements). `Block.simp`
rewrites it bottom-up into the forms a reader and a downstream proof want
(`x + y`, `e`, `rsp - 8`), and `Block.simp_run` proves it does not change the
block's meaning. The lifter's certificate for a block is

```
liftBlock instrs = some b     -- by decide
```

and `liftBlock_sound` turns it into the simulation equation. Every rewrite is
a smart constructor with its own `den` lemma, so adding a rule is local.
-/

@[expose] public section

namespace Silmaril.X86.Lift.Bir

open Silmaril.X86 (Reg Word State Flags AluOp)
open Silmaril.X86.Ext
open Silmaril.Process (Memory)

/-! ## Smart constructors -/

def mkAdd : E → E → E
  | .imm a, .imm b => .imm (a + b)
  | e, .imm 0 => e
  | .imm 0, e => e
  | .add x (.imm a), .imm b => .add x (.imm (a + b))
  | x, y => .add x y

theorem mkAdd_den (env : Env) (a b : E) : (mkAdd a b).den env = a.den env + b.den env := by
  unfold mkAdd
  split <;> simp_all [E.den, BitVec.add_assoc]

def mkSub : E → E → E
  | .imm a, .imm b => .imm (a - b)
  | e, .imm 0 => e
  | x, y => .sub x y

theorem mkSub_den (env : Env) (a b : E) : (mkSub a b).den env = a.den env - b.den env := by
  unfold mkSub
  split <;> simp_all [E.den]

def mkShl : E → Nat → E
  | e, 0 => e
  | .imm a, k => .imm (a <<< k)
  | e, k => .shl e k

theorem mkShl_den (env : Env) (a : E) (k : Nat) : (mkShl a k).den env = a.den env <<< k := by
  unfold mkShl
  split <;> simp_all [E.den]

def mkZext (w : Nat) : E → E
  | .imm a => .imm ((a.setWidth w).setWidth 64)
  | e => if w = 64 then e else .zext w e

theorem mkZext_den (env : Env) (w : Nat) (a : E) :
    (mkZext w a).den env = ((a.den env).setWidth w).setWidth 64 := by
  unfold mkZext
  split
  · simp [E.den]
  · split
    · subst_vars; simp
    · rfl

def mkAlu (w : Nat) (op : AluOp) (a b : E) : E :=
  if w = 64 then
    match op with
    | .add => mkAdd a b
    | .sub | .cmp => mkSub a b
    | _ => .alu 64 op a b
  else .alu w op a b

theorem mkAlu_den (env : Env) (w : Nat) (op : AluOp) (a b : E) :
    (mkAlu w op a b).den env =
      (AluOp.resultN op ((a.den env).setWidth w) ((b.den env).setWidth w)).setWidth 64 := by
  unfold mkAlu
  split
  · subst_vars
    split <;> simp [mkAdd_den, mkSub_den, E.den, AluOp.resultN]
  · rfl

/-! ## The simplifier -/

def E.simp : E → E
  | .add a b => mkAdd a.simp b.simp
  | .sub a b => mkSub a.simp b.simp
  | .shl a k => mkShl a.simp k
  | .zext w a => mkZext w a.simp
  | .sext w a => .sext w a.simp
  | .alu w op a b => mkAlu w op a.simp b.simp
  | .neg w a => .neg w a.simp
  | .not w a => .not w a.simp
  | .mul w a b => .mul w a.simp b.simp
  | .shift w op a c => .shift w op a.simp c.simp
  | .merge n a b => .merge n a.simp b.simp
  | .sel b x y => .sel b.simp x.simp y.simp
  | .bswap sz a => .bswap sz a.simp
  | .bitcount op w a => .bitcount op w a.simp
  | .signmask w a => .signmask w a.simp
  | e => e

theorem E.simp_den (env : Env) : ∀ e : E, e.simp.den env = e.den env
  | .reg _ | .rip | .fs | .v _ | .imm _ | .xmm _ _ => rfl
  | .add a b => by simp only [E.simp, mkAdd_den, E.simp_den env a, E.simp_den env b, E.den]
  | .sub a b => by simp only [E.simp, mkSub_den, E.simp_den env a, E.simp_den env b, E.den]
  | .shl a k => by simp only [E.simp, mkShl_den, E.simp_den env a, E.den]
  | .zext w a => by simp only [E.simp, mkZext_den, E.simp_den env a, E.den]
  | .sext w a => by simp only [E.simp, E.den, E.simp_den env a]
  | .alu w op a b => by simp only [E.simp, mkAlu_den, E.simp_den env a, E.simp_den env b, E.den]
  | .neg w a => by simp only [E.simp, E.den, E.simp_den env a]
  | .not w a => by simp only [E.simp, E.den, E.simp_den env a]
  | .mul w a b => by simp only [E.simp, E.den, E.simp_den env a, E.simp_den env b]
  | .shift w op a c => by simp only [E.simp, E.den, E.simp_den env a, E.simp_den env c]
  | .merge n a b => by simp only [E.simp, E.den, E.simp_den env a, E.simp_den env b]
  | .sel b x y => by simp only [E.simp, E.den, E.simp_den env b, E.simp_den env x, E.simp_den env y]
  | .bswap sz a => by simp only [E.simp, E.den, E.simp_den env a]
  | .bitcount op w a => by simp only [E.simp, E.den, E.simp_den env a]
  | .signmask w a => by simp only [E.simp, E.den, E.simp_den env a]

def F.simp : F → F
  | .entry => .entry
  | .alu w op a b => .alu w op a.simp b.simp
  | .logic w a => .logic w a.simp
  | .test w a b => .test w a.simp b.simp
  | .inc w a o => .inc w a.simp o.simp
  | .dec w a o => .dec w a.simp o.simp
  | .neg w a => .neg w a.simp
  | .imul w a b => .imul w a.simp b.simp
  | .shift w op a c o => .shift w op a.simp c.simp o.simp
  | .bitcount op w a => .bitcount op w a.simp
  | .bt a c o => .bt a.simp c.simp o.simp
  | .undef => .undef

theorem F.simp_den (env : Env) : ∀ f : F, f.simp.den env = f.den env
  | .entry | .undef => rfl
  | .alu w op a b => by simp only [F.simp, F.den, E.simp_den]
  | .logic w a => by simp only [F.simp, F.den, E.simp_den]
  | .test w a b => by simp only [F.simp, F.den, E.simp_den]
  | .inc w a o => by simp only [F.simp, F.den, E.simp_den, F.simp_den env o]
  | .dec w a o => by simp only [F.simp, F.den, E.simp_den, F.simp_den env o]
  | .neg w a => by simp only [F.simp, F.den, E.simp_den]
  | .imul w a b => by simp only [F.simp, F.den, E.simp_den]
  | .shift w op a c o => by simp only [F.simp, F.den, E.simp_den, F.simp_den env o]
  | .bitcount op w a => by simp only [F.simp, F.den, E.simp_den]
  | .bt a c o => by simp only [F.simp, F.den, E.simp_den, F.simp_den env o]

def Stmt.simp : Stmt → Stmt
  | .load k a => .load k a.simp
  | .store k a x => .store k a.simp x.simp
  | .push a x => .push a.simp x.simp
  | .pop a => .pop a.simp
  | .cond c f => .cond c f.simp
  | .trap => .trap
  | .align a k => .align a.simp k

theorem Stmt.simp_run (env : Env) (st : Stmt) : st.simp.run env = st.run env := by
  cases st <;> simp only [Stmt.simp, Stmt.run, E.simp_den, F.simp_den]

theorem runStmts_simp : ∀ (sts : List Stmt) (env : Env),
    runStmts (sts.map Stmt.simp) env = runStmts sts env
  | [], _ => rfl
  | st :: rest, env => by
    simp only [List.map_cons, runStmts, Stmt.simp_run]
    split <;> simp_all [runStmts_simp rest]

def Block.simp (b : Block) : Block where
  stmts := b.stmts.map Stmt.simp
  regs := b.regs.map fun p => (p.1, p.2.simp)
  flags := b.flags.simp
  rip := b.rip.simp
  xmm := b.xmm.map fun p => (p.1, p.2.1.simp, p.2.2.simp)

theorem lookup_map_simp (r : Reg) : ∀ l : List (Reg × E),
    ((l.map fun p => (p.1, p.2.simp)).lookup r) = (l.lookup r).map E.simp
  | [] => rfl
  | (q, e) :: rest => by
    simp only [List.map_cons, List.lookup]
    split <;> simp_all [lookup_map_simp r rest]

theorem Block.simp_reg_den (b : Block) (env : Env) (r : Reg) :
    (b.simp.reg r).den env = (b.reg r).den env := by
  simp only [Block.reg, Block.simp, lookup_map_simp]
  cases b.regs.lookup r <;> simp [E.simp_den]

theorem lookup_map_simp2 (i : Fin 16) : ∀ l : List (Fin 16 × E × E),
    ((l.map fun p => (p.1, p.2.1.simp, p.2.2.simp)).lookup i) =
      (l.lookup i).map fun p => (p.1.simp, p.2.simp)
  | [] => rfl
  | (q, e) :: rest => by
    simp only [List.map_cons, List.lookup]
    split <;> simp_all [lookup_map_simp2 i rest]

theorem Block.simp_xreg_den (b : Block) (env : Env) (i : Fin 16) :
    (b.simp.xreg i).1.den env = (b.xreg i).1.den env ∧
      (b.simp.xreg i).2.den env = (b.xreg i).2.den env := by
  simp only [Block.xreg, Block.simp, lookup_map_simp2]
  cases b.xmm.lookup i <;> simp [E.simp_den]

theorem Block.simp_state (b : Block) (env : Env) : b.simp.state env = b.state env := by
  have h1 : (fun r => (b.simp.reg r).den env) = fun r => (b.reg r).den env :=
    funext (Block.simp_reg_den b env)
  have h2 : (fun i => (b.simp.xreg i).2.den env ++ (b.simp.xreg i).1.den env) =
      fun i => (b.xreg i).2.den env ++ (b.xreg i).1.den env :=
    funext fun i => by rw [(Block.simp_xreg_den b env i).1, (Block.simp_xreg_den b env i).2]
  have h3 : b.simp.rip.den env = b.rip.den env := E.simp_den env b.rip
  have h4 : b.simp.flags.den env = b.flags.den env := F.simp_den env b.flags
  unfold Block.state
  rw [h1, h2, h3, h4]

theorem Block.simp_run (b : Block) (s : XState) (mem : Memory) : b.simp.run s mem = b.run s mem := by
  have hs : b.simp.stmts = b.stmts.map Stmt.simp := rfl
  unfold Block.run
  rw [hs, runStmts_simp]
  split
  · rfl
  · rw [Block.simp_state]

/-! ## The entry point -/

/-- Lift a block and simplify it. -/
def liftBlock (instrs : List (LInstr × Nat)) : Option Block := (symExec instrs).map Block.simp

/-- **The certificate.** A block whose lift the kernel computes to `b` is
simulated by `b` on every entry state and memory. -/
theorem liftBlock_sound {instrs : List (LInstr × Nat)} {b : Block} (h : liftBlock instrs = some b)
    (s : XState) (mem : Memory) : execBlock instrs s mem = b.run s mem := by
  simp only [liftBlock, Option.map_eq_some_iff] at h
  obtain ⟨b0, h0, rfl⟩ := h
  rw [Block.simp_run, symExec_sound h0]

end Silmaril.X86.Lift.Bir
