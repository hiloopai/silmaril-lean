module

public import Silmaril.Machine.X86.Stencils.ByteLoop.Defs
public import Silmaril.Machine.X86.BlockCert.Store.Thms
public import Silmaril.Machine.X86.Sep.SysV.Thms
import Silmaril.Proofs.Machine.X86.Stencils.ByteLoop.Prefix
import Silmaril.Proofs.Machine.X86.Stencils.ByteLoop.Sat

/-!
# Byte-loop stencils: proofs

**The stencil theorems** (proved once, for every function and every load address):

* `copy_sat`: a function whose code satisfies the state-level `copyContract` meets the
  separation-logic `copySpec` under the System V ABI;
* `fill_sat`: the same for `fillContract` and `fillSpec`;
* `scan_sat`: the same for `scanContract` and `scanSpec`.

Each reads every entry fact of the state-level contract (permissions, backing, the
destination apart from the source, from the code and from the return slot) off the
separation-logic precondition, and rebuilds the postcondition's fragments from the final
memory; nothing else of the caller is touched (the frame is built into `Sat`).

**The loop algebra** used by stencil instances:

* `storeN_one`, `loadN_one`: one-byte stores and loads as explicit memories;
* `Prefix.init`, `Prefix.set1`, `Prefix.writesWithin`, `Prefix.permits`, `Prefix.loaded`,
  `Prefix.readBytes`, `Prefix.get_apart`: the written-prefix invariant;
* `LoopFrame.entry`, `LoopFrame.step`, `LoopFrame.pop`, `LoopFrame.result`: the System V frame
  of a leaf whose memory changes, and its exit;
* arithmetic of loop counters and pointers: `toNat_add_lt`, `ptr_eq_iff`, `subFlagsN_zero`
  (`cmp` sets ZF iff its operands are equal), `and_one_zero` (`and $1` sets ZF iff even);
* `cmpb_zero_run`: the raw block `cmpb $0, (r); je/jne`, which Bir does not lift, as one
  statement: it keeps memory and registers and branches on whether the byte at `r` is NUL.
-/

@[expose] public section

namespace Silmaril.Machine.X86.Stencils.ByteLoop

open Silmaril.X86 (State MState Word Byte Reg)
open Silmaril.X86.Ext (Loaded loadN storeN)
open Silmaril.Process (Memory addressLimit)
open Silmaril.Machine.X86.Sep

/-! ## One-byte accesses -/

theorem storeN_one {mem : Memory} {w v : Word} (hp : mem.permits .write w.toNat = true) :
    storeN mem w 1 v = some (set1 mem w.toNat (v.setWidth 8)) :=
  Silmaril.Proofs.Machine.X86.Stencils.ByteLoop.storeN_one hp

theorem loadN_one {mem : Memory} {w : Word} {b : Byte} (hp : mem.permits .read w.toNat = true)
    (hb : mem.bytes.get? w.toNat = some b) : loadN mem w 1 = some (BitVec.ofNat 64 b.toNat) :=
  Silmaril.Proofs.Machine.X86.Stencils.ByteLoop.loadN_one hp hb

/-- A byte zero-extended to a word and narrowed back. -/
@[simp] theorem byte_roundtrip (b : Byte) : (BitVec.ofNat 64 b.toNat).setWidth 8 = b := by
  apply BitVec.eq_of_toNat_eq
  have := b.isLt
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  omega

/-! ## Counters, pointers and flags -/

theorem toNat_add_lt {a b : Word} (h : a.toNat + b.toNat < 2 ^ 64) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt h]

/-- Two pointers into the same block are equal iff their offsets are. -/
theorem ptr_eq_iff {d n0 : Word} {k : Nat} (hk : k < 2 ^ 64) :
    d + BitVec.ofNat 64 k = d + n0 ↔ k = n0.toNat := by
  constructor
  · intro h
    have := congrArg BitVec.toNat (add_left_cancel h)
    simp only [BitVec.toNat_ofNat] at this
    rwa [Nat.mod_eq_of_lt hk] at this
  · intro h; subst h; simp

/-- `cmp` sets the zero flag iff its operands are equal. -/
theorem subFlagsN_zero {n : Nat} (x y : BitVec n) :
    (Silmaril.X86.Ext.subFlagsN x y).zero = some (decide (x = y)) := by
  simp only [Silmaril.X86.Ext.subFlagsN, Silmaril.X86.Ext.isZeroN, Option.some.injEq]
  by_cases h : x = y
  · simp [h]
  · simp only [h, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e; exact h (sub_eq_zero.mp e)

/-- `and $1, %e..` gives zero iff the register is even. -/
theorem and_one_zero (x : Word) :
    (BitVec.setWidth 32 x &&& BitVec.setWidth 32 (1 : Word) == 0#32) =
      decide (x.toNat % 2 = 0) := by
  have h : (BitVec.setWidth 32 x &&& BitVec.setWidth 32 (1 : Word)).toNat = x.toNat % 2 := by
    simp only [BitVec.toNat_and, BitVec.toNat_setWidth]
    rw [show (1 : Word).toNat % 2 ^ 32 = 1 by rfl, Nat.and_one_is_mod]
    omega
  by_cases e : x.toNat % 2 = 0
  · simp only [e, decide_true, beq_iff_eq]; apply BitVec.eq_of_toNat_eq; rw [h, e]; rfl
  · simp only [e, decide_false, beq_eq_false_iff_ne, ne_eq]
    intro e'; apply e; rw [← h, e']; rfl

theorem read_mk (W : State) (a : Word) (f : Silmaril.X86.Flags) (q : Reg) :
    ({ regs := W.regs, rip := a, flags := f, fsBase := W.fsBase } : State).read q = W.read q :=
  rfl

/-- **The raw `cmpb $0, (r); jcc` block** (`jcc` is `je` or `jne`), where `r` points at a
loadable byte `b`: it keeps memory and registers and branches on whether `b` is NUL. -/
theorem cmpb_zero_run {m : MState} {r : Reg} {c : Silmaril.X86.Ext.Cond} {rel : BitVec 8}
    {b : Byte} (hl : loadN m.memory (m.core.read r) 1 = some (BitVec.ofNat 64 b.toNat))
    (hc : c = .e ∨ c = .ne) :
    ∃ m', BlockCert.runL [(.ext (.cmpI8 (.mem (Silmaril.X86.Ext.Mem.ofReg r none 0x0)) 0x0), 3),
        (.ext (.jcc8 c rel), 2)] m = some m' ∧ m'.memory = m.memory ∧
      (∀ q, m'.core.read q = m.core.read q) ∧
      m'.core.rip = if (b = 0 ↔ c = .e) then m.core.rip + 5#64 + rel.signExtend 64
        else m.core.rip + 5#64 := by
  simp [BlockCert.runL, Silmaril.X86.Lift.Bir.execBlock, Silmaril.X86.Lift.Bir.LInstr.exec,
    Silmaril.X86.Lift.Bir.liftR, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.readNarrow,
    BlockCert.xs, BlockCert.ofX, Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Mem.ofReg, hl,
    Silmaril.X86.Ext.retire, Silmaril.X86.Ext.Narrow.bytes, Silmaril.X86.Ext.Narrow.bits,
    Silmaril.X86.Ext.Cond.eval, subFlagsN_zero, Silmaril.X86.Ext.kNot]
  rcases hc with rfl | rfl <;> by_cases hb : b = 0#8 <;> simp [hb, BitVec.add_assoc]

/-! ## The written prefix -/

namespace Prefix

variable {m0 mem : Memory} {d i : Nat} {val : Nat → Option Byte}

theorem init (m0 : Memory) (d : Nat) (val : Nat → Option Byte) : Prefix m0 m0 d 0 val :=
  Silmaril.Proofs.Machine.X86.Stencils.ByteLoop.prefix_init m0 d val

/-- **One more byte**: storing `val i` at `d + i`. -/
theorem set1 {b : Byte} (h : Prefix m0 mem d i val) (hv : val i = some b) :
    Prefix m0 (ByteLoop.set1 mem (d + i) b) d (i + 1) val :=
  Silmaril.Proofs.Machine.X86.Stencils.ByteLoop.prefix_set1 h hv

theorem writesWithin (h : Prefix m0 mem d i val) {n : Nat} (hi : i ≤ n) :
    m0.WritesWithin mem (fun a => d ≤ a ∧ a < d + n) :=
  Silmaril.Proofs.Machine.X86.Stencils.ByteLoop.prefix_writesWithin h hi

theorem permits (h : Prefix m0 mem d i val) (acc : Silmaril.Process.Access) (a : Nat) :
    mem.permits acc a = m0.permits acc a :=
  Silmaril.Proofs.Machine.X86.Stencils.ByteLoop.prefix_permits h acc a

/-- The code image stays loaded while the prefix stays apart from it. -/
theorem loaded {n : Nat} (h : Prefix m0 mem d i val) (hi : i ≤ n) {base : Word}
    {code : List Byte} (hap : Apart d n base.toNat code.length) (hl : Loaded m0 base code) :
    Loaded mem base code :=
  Silmaril.Proofs.Machine.X86.Stencils.ByteLoop.prefix_loaded h hi hap hl

theorem readBytes {n : Nat} (h : Prefix m0 mem d i val) (hi : i ≤ n) {a k : Nat}
    (hap : Apart d n a k) : mem.readBytes a k = m0.readBytes a k :=
  Silmaril.Proofs.Machine.X86.Stencils.ByteLoop.prefix_readBytes h hi hap

/-- A byte of a block apart from the destination reads as at entry. -/
theorem get_apart {n s k j : Nat} (h : Prefix m0 mem d i val) (hi : i ≤ n)
    (hap : Apart d n s k) (hj : j < k) : mem.bytes.get? (s + j) = m0.bytes.get? (s + j) :=
  h.outside _ (by unfold Apart at hap; omega)

end Prefix

/-! ## The frame of a leaf loop -/

namespace LoopFrame

variable {m0 m t : MState}

theorem entry (h : FnContract.AbiEntry m0.core m0.memory) : LoopFrame m0 m0 :=
  ⟨h, rfl, fun _ _ => rfl⟩

theorem step (h : LoopFrame m0 m) (hsp : t.core.read .rsp = m.core.read .rsp)
    (hcs : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, t.core.read r = m.core.read r) :
    LoopFrame m0 t :=
  ⟨h.abi, hsp.trans h.rsp, fun r hr => (hcs r hr).trans (h.saved r hr)⟩

/-- The return address at the current stack pointer, when the return slot was not written. -/
theorem pop (h : LoopFrame m0 m) (hrb : m.memory.readBytes (sp m0) 8 = m0.memory.readBytes (sp m0) 8) :
    (m.memory.readBytes (m.core.read .rsp).toNat 8).bind Silmaril.X86.wordOfBytes? =
      some (Silmaril.Machine.X86.Open.retOf m0.core m0.memory) := by
  rw [h.rsp]; unfold sp at hrb; rw [hrb]; exact BlockCert.pop_ret h.abi

/-- **The exit of a leaf loop**: back at the return address, `rsp` popped, callee-saved
registers restored, memory written only inside the footprint, and the postcondition. -/
theorem result {S : FnContract.Spec MState} (h : LoopFrame m0 m)
    (hpc : t.core.rip = Silmaril.Machine.X86.Open.retOf m0.core m0.memory)
    (hsp : t.core.read .rsp = m.core.read .rsp + 8#64)
    (hcs : ∀ r ∈ Silmaril.X86.sysv64.calleeSaved, t.core.read r = m.core.read r)
    (hmem : t.memory = m.memory) (hw : m0.memory.WritesWithin m.memory (S.footprint m0))
    (hpost : S.post m0 t) : S.Result Silmaril.Machine.X86.Open.isa m0 t :=
  ⟨rfl, ⟨hpc, hsp.trans (by rw [h.rsp]), fun r hr => (hcs r hr).trans (h.saved r hr)⟩,
    by show m0.memory.WritesWithin t.memory _; rw [hmem]; exact hw, hpost⟩

end LoopFrame

/-! ## The stencil theorems -/

/-- **`Copy`**: the state-level contract gives the separation-logic spec. -/
theorem copy_sat {code : List Byte} {entry : Word} (hne : code ≠ [])
    (hK : (copyContract code entry).Total Silmaril.Machine.X86.Open.isa) :
    copySpec.Sat (codePt entry.toNat code) entry :=
  Silmaril.Proofs.Machine.X86.Stencils.ByteLoop.copy_sat hne hK

/-- **`Fill`**: the state-level contract gives the separation-logic spec. -/
theorem fill_sat {code : List Byte} {entry : Word} (hne : code ≠ [])
    (hK : (fillContract code entry).Total Silmaril.Machine.X86.Open.isa) :
    fillSpec.Sat (codePt entry.toNat code) entry :=
  Silmaril.Proofs.Machine.X86.Stencils.ByteLoop.fill_sat hne hK

/-- **`Scan`**: the state-level contract gives the separation-logic spec. -/
theorem scan_sat {code : List Byte} {entry : Word} (hne : code ≠ [])
    (hK : (scanContract code entry).Total Silmaril.Machine.X86.Open.isa) :
    scanSpec.Sat (codePt entry.toNat code) entry :=
  Silmaril.Proofs.Machine.X86.Stencils.ByteLoop.scan_sat hne hK

end Silmaril.Machine.X86.Stencils.ByteLoop
