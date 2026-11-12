module

public import Silmaril.Raw.Elf.Link.Dyn.Proc.Exec
public import Silmaril.Raw.Elf.Link.Dyn.Proc.Call

/-! # Instruction rewrites at a computed address, for `main` proofs

Each lemma executes one memory instruction given a fact about the address it computes
(`hc`, discharged after the state is known: `rw [lemma h _ _ _ _ _ ?hc]`), and
`cond_g_test` decides `jg` after `test x, x`. -/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Proc

open Silmaril.X86.Ext (loadN)

theorem exec_loadfs_at {fs : Silmaril.X86.Word} {m : Silmaril.Process.Memory} {v : Silmaril.X86.Word} {d : BitVec 32}
    (h : loadN m (fs + d.signExtend 64) 8 = some v) (dst : Silmaril.X86.Reg) (c : Silmaril.X86.State) (l : Nat)
    (hc : c.fsBase = fs) :
    Silmaril.X86.Ext9.exec (.ext8 (.base (.load .q dst (Silmaril.X86.Ext.Mem.ofFs Option.none d)))) c m l =
      .ok { c.write dst v with rip := c.rip + BitVec.ofNat 64 l } m :=
  exec_loadfs dst d c m l v (hc ▸ h)

theorem exec_storeq_at {A : Silmaril.X86.Word} {m : Silmaril.Process.Memory} (h : m.Permitted .write A.toNat 8)
    (base src : Silmaril.X86.Reg) (d : BitVec 32) (c : Silmaril.X86.State) (l : Nat)
    (hc : c.read base + d.signExtend 64 = A) :
    Silmaril.X86.Ext9.exec (.ext8 (.base (.mov .q (.mem (Silmaril.X86.Ext.Mem.ofReg base Option.none d)) src))) c m l =
      .ok { c with rip := c.rip + BitVec.ofNat 64 l } (storeMem m A 8 (c.read src)) := by
  subst hc; exact exec_storeq base src d c m l h

theorem cond_g_test (x : BitVec 64) (h : x.msb = false) :
    Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.logicFlagsN (x &&& x)) Silmaril.X86.Ext.Cond.g = some (x != 0#64) := by
  simp [Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.logicFlagsN, Silmaril.X86.Ext.isZeroN, h,
    Silmaril.X86.Ext.kNot, Silmaril.X86.Ext.kOr, Silmaril.X86.Ext.kXor]
  cases hx : (x == 0#64) <;> simp_all [bne]

/-- `jne` after `test x, x`. -/
theorem cond_ne_test (x : BitVec 64) :
    Silmaril.X86.Ext.Cond.eval (Silmaril.X86.Ext.logicFlagsN (x &&& x)) Silmaril.X86.Ext.Cond.ne = some (x != 0#64) := by
  simp [Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.logicFlagsN, Silmaril.X86.Ext.isZeroN,
    Silmaril.X86.Ext.kNot]
  cases hx : (x == 0#64) <;> simp_all [bne]

theorem exec_loadqd_at {A : Silmaril.X86.Word} {m : Silmaril.Process.Memory} {v : Silmaril.X86.Word}
    (h : loadN m A 8 = some v) (dst base : Silmaril.X86.Reg) (d : BitVec 32) (c : Silmaril.X86.State) (l : Nat)
    (hc : c.read base + d.signExtend 64 = A) :
    Silmaril.X86.Ext9.exec (.ext8 (.base (.load .q dst (Silmaril.X86.Ext.Mem.ofReg base Option.none d)))) c m l =
      .ok { c.write dst v with rip := c.rip + BitVec.ofNat 64 l } m := by
  subst hc; exact exec_loadqd dst base d c m l v h


end Silmaril.Elf.Link.Dyn.Proc
