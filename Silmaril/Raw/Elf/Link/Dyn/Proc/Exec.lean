module

public import Silmaril.Raw.Elf.Link.Dyn.Proc.Call

/-! # One-instruction rewrites for memory operands

Each lemma states what one memory-touching instruction does, from a fact about the memory, so
that proofs never let `simp` evaluate a load or store on a symbolic memory.
-/

@[expose] public section

open Silmaril.Elf.Link.DynElf

namespace Silmaril.Elf.Link.Dyn.Proc

open Silmaril.X86 (Word Byte MState State Reg)
open Silmaril.Process (Memory Access)
open Silmaril.X86.Ext (Loaded loadN)

@[simp] theorem ofReg_idx_addr (base idx : Reg) (h : idx ≠ .rsp) (c : State) (next : Word) :
    (Silmaril.X86.Ext.Mem.ofReg base (some ⟨idx, 0#2, h⟩) 0#32).addr c next = c.read base + c.read idx := by
  simp [Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Mem.ofReg, Silmaril.X86.Ext.Index.value]

/-- `mov [base + d], src` (64-bit). -/
theorem exec_storeq (base src : Reg) (d : BitVec 32) (c : State) (m : Memory) (l : Nat)
    (h : m.Permitted .write (c.read base + d.signExtend 64).toNat 8) :
    Silmaril.X86.Ext9.exec (.ext8 (.base (.mov .q (.mem (Silmaril.X86.Ext.Mem.ofReg base Option.none d)) src)))
      c m l = .ok { c with rip := c.rip + BitVec.ofNat 64 l }
        (storeMem m (c.read base + d.signExtend 64) 8 (c.read src)) := by
  simp [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
    Silmaril.X86.Ext.writeRM, ofReg_addr, storeN_ok h, Silmaril.X86.Ext.Sz.read, Silmaril.X86.Ext.Sz.bytes]

/-- `mov rdst, fs:[d]` (64-bit). -/
theorem exec_loadfs (dst : Reg) (d : BitVec 32) (c : State) (m : Memory) (l : Nat) (v : Word)
    (h : loadN m (c.fsBase + d.signExtend 64) 8 = some v) :
    Silmaril.X86.Ext9.exec (.ext8 (.base (.load .q dst (Silmaril.X86.Ext.Mem.ofFs Option.none d)))) c m l =
      .ok { c.write dst v with rip := c.rip + BitVec.ofNat 64 l } m := by
  simp [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
    Silmaril.X86.Ext.readRM, h, Silmaril.X86.Ext.Sz.bytes, Silmaril.X86.Ext.Sz.write]

/-- `movzx r32, byte [src]`. -/
theorem exec_movzxb (dst src : Reg) (c : State) (m : Memory) (l : Nat) (v : Word)
    (h : loadN m (c.read src) 1 = some v) :
    Silmaril.X86.Ext9.exec (.ext8 (.base (.movx false .d .b dst (.mem (Silmaril.X86.Ext.Mem.ofReg src Option.none 0#32)))))
      c m l = .ok { Silmaril.X86.Ext.Sz.d.write c dst ((v.setWidth 8).setWidth 32) with
        rip := c.rip + BitVec.ofNat 64 l } m := by
  simp [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
    Silmaril.X86.Ext.readNarrow, h, Silmaril.X86.Ext.Narrow.bytes, Silmaril.X86.Ext.Narrow.bits]

/-- `mov byte [base], imm8`. -/
theorem exec_storeb (base : Reg) (imm : BitVec 8) (c : State) (m : Memory) (l : Nat)
    (h : m.Permitted .write (c.read base).toNat 1) :
    Silmaril.X86.Ext9.exec (.ext8 (.base (.movI8 (.mem (Silmaril.X86.Ext.Mem.ofReg base Option.none 0#32)) imm)))
      c m l = .ok { c with rip := c.rip + BitVec.ofNat 64 l } (storeMem m (c.read base) 1 (imm.setWidth 64)) := by
  simp [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
    Silmaril.X86.Ext.writeRM8, storeN_ok h]

/-- The flags of `test byte [m], imm` on the byte `v`. -/
def testFlags8 (v : Word) (imm : BitVec 8) : Silmaril.X86.Flags :=
  Silmaril.X86.Ext.logicFlagsN ((v.setWidth 8) &&& imm)

/-- `test byte [base], imm8`. -/
theorem exec_testI8m (base : Reg) (imm : BitVec 8) (c : State) (m : Memory) (l : Nat) (v : Word)
    (h : loadN m (c.read base) 1 = some v) :
    Silmaril.X86.Ext9.exec (.ext8 (.base (.testI8 (.mem (Silmaril.X86.Ext.Mem.ofReg base Option.none 0#32)) imm)))
      c m l = .ok { c with flags := testFlags8 v imm, rip := c.rip + BitVec.ofNat 64 l } m := by
  simp [Silmaril.X86.Ext9.exec, Silmaril.X86.Ext8.exec, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire,
    Silmaril.X86.Ext.readNarrow, h, Silmaril.X86.Ext.Narrow.bytes, Silmaril.X86.Ext.Narrow.bits, testFlags8]

theorem eval_testFlags8 (v : Word) (imm : BitVec 8) (c : Silmaril.X86.Ext.Cond) (hc : c = .e ∨ c = .ne) :
    Silmaril.X86.Ext.Cond.eval (testFlags8 v imm) c =
      some (if c = .e then decide ((v.setWidth 8 &&& imm) = 0#8) else !decide ((v.setWidth 8 &&& imm) = 0#8)) := by
  rcases hc with rfl | rfl
  · by_cases h : (v.setWidth 8 &&& imm) = 0#8 <;>
      simp [testFlags8, Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.logicFlagsN, Silmaril.X86.Ext.isZeroN, h]
  · by_cases h : (v.setWidth 8 &&& imm) = 0#8 <;>
      simp [testFlags8, Silmaril.X86.Ext.Cond.eval, Silmaril.X86.Ext.logicFlagsN, Silmaril.X86.Ext.isZeroN, h,
        Silmaril.X86.Ext.kNot]

/-- The test of one bit of a byte. -/
theorem testbit_and {v : Word} {i : Nat} (hi : i < 8) :
    ((v.setWidth 8 &&& BitVec.ofNat 8 (2 ^ i)) = 0#8) ↔ v.getLsbD i = false := by
  constructor
  · intro h
    have := congrArg (fun x => x.getLsbD i) h
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat, Nat.testBit_two_pow] at this
    simpa [hi] using this
  · intro h
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofNat, Nat.testBit_two_pow]
    by_cases hij : i = j
    · subst hij; simp [h]
    · simp [hij]

theorem permitted_sub {m : Memory} {acc : Access} {a n a' n' : Nat} (h : m.Permitted acc a n)
    (h1 : a ≤ a') (h2 : a' + n' ≤ a + n) (h3 : a' < a + n) : m.Permitted acc a' n' := by
  unfold Memory.Permitted at h ⊢
  rw [Memory.checkSpan_iff] at h ⊢
  obtain ⟨ha, hb, hp⟩ := h
  refine ⟨by simp [Silmaril.Process.addressLimit] at hb ⊢; omega, by omega, fun k hk => ?_⟩
  have := hp (a' - a + k) (by omega)
  rwa [show a + (a' - a + k) = a' + k by omega] at this

theorem permitted_bound {m : Memory} {acc : Access} {a n : Nat} (h : m.Permitted acc a n) :
    a + n ≤ 2 ^ 64 := by
  unfold Memory.Permitted at h
  rw [Memory.checkSpan_iff] at h
  simpa [Silmaril.Process.addressLimit] using h.2.1

theorem contract_cond {c pre : Prop} {post : PState → Prop} {r : Silmaril.X86.RelIsa.Res PState}
    (h : c → Contract pre post r) : Contract (c ∧ pre) post r := fun hp => h hp.1 hp.2

end Silmaril.Elf.Link.Dyn.Proc
