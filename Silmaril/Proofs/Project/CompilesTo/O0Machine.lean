module

public import Silmaril.Project.CompilesTo.Defs
public import Silmaril.X86.Open.Thms

/-!
# The machine side of gcc `-O0` leaf code, one instruction at a time

Step lemmas of the open machine (`Open.step`) for the instructions gcc `-O0` emits in the
body of a leaf function with a frame pointer: the prologue (`push %rbp; mov %rsp,%rbp`), 32-bit
loads and stores of frame slots `disp(%rbp)`, and register `add`. Each body lemma keeps
`Frame0` (code loaded, `rbp = rsp = entry rsp - 8`, the caller's `rbp` saved, callee-saved
registers unchanged, writes only in the frame); a store's new memory is left opaque and named by
`Ext.Stored`. `FnData.notCut` says that a machine state strictly inside a segment is not a cut
point. These are facts about the handwritten `X86.Ext` model only.
-/

@[expose] public section

namespace Silmaril.Project.CompilesTo

open Silmaril.Compiler.CompilesTo

open Silmaril.X86 (State Reg)
open Silmaril.X86.Ext (Mem Sz HoldsLE Stored loadN storeN leBytes)
open Silmaril.Process (Memory)
open Silmaril.Machine.LittleEndian (encodeWords)
open Silmaril.Cerberus.Core.Dynamics (Frame)

/-! ## Addresses -/

theorem ofReg_addr (r : Reg) (d : BitVec 32) (s : State) (next : BitVec 64) :
    (Mem.ofReg r none d).addr s next = s.read r + d.signExtend 64 := by
  simp [Mem.addr, Mem.ofReg]

/-- `disp(%rbp)` with `rbp = sp - 8` and `disp = -n`: the address `sp - 8 - n`. -/
theorem rbp_slot_toNat {sp : BitVec 64} {d : BitVec 32} {n : Nat}
    (hd : d.signExtend 64 = -(BitVec.ofNat 64 n)) (hn : n + 8 ≤ sp.toNat) :
    (sp - 8#64 + d.signExtend 64).toNat = sp.toNat - 8 - n := by
  rw [hd]
  have := sp.isLt
  bv_omega

/-- A span inside a permitted span is permitted. -/
theorem permitted_sub {mem : Memory} {acc : Silmaril.Process.Access} {a len b k : Nat}
    (h : mem.Permitted acc a len) (hlo : a ≤ b) (hhi : b + k ≤ a + len) (hk : 0 < k) :
    mem.Permitted acc b k := by
  unfold Memory.Permitted at h ⊢
  rw [Memory.checkSpan_iff] at h ⊢
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by omega, by omega, fun off hoff => ?_⟩
  have := h3 (b - a + off) (by omega)
  rwa [show a + (b - a + off) = b + off by omega] at this

/-! ## The frame invariant -/

section Frame

variable {addr : Nat} {code : List Byte} {frame : Nat} {m0 m : MState}

/-- The entry stack pointer is at least the frame size. -/
theorem Frame0.rsp0 (hf : Frame0 addr code frame m0 m) : frame ≤ (m0.core.read .rsp).toNat :=
  hf.room

/-- The frame's memory permissions are those of the entry state. -/
theorem Frame0.permitted (hf : Frame0 addr code frame m0 m) (acc : Silmaril.Process.Access)
    (a len : Nat) : m.memory.Permitted acc a len ↔ m0.memory.Permitted acc a len :=
  hf.writes.permitted_iff acc a len

/-- A span of the frame is readable. -/
theorem Frame0.readable (hf : Frame0 addr code frame m0 m) {b k : Nat}
    (hlo : (m0.core.read .rsp).toNat - frame ≤ b) (hhi : b + k ≤ (m0.core.read .rsp).toNat + 8)
    (hk : 0 < k) : m.memory.Permitted .read b k :=
  (hf.permitted .read b k).mpr (permitted_sub hf.rw.1 hlo (by have := hf.rsp0; omega) hk)

/-- A span of the frame is writable. -/
theorem Frame0.writable (hf : Frame0 addr code frame m0 m) {b k : Nat}
    (hlo : (m0.core.read .rsp).toNat - frame ≤ b) (hhi : b + k ≤ (m0.core.read .rsp).toNat + 8)
    (hk : 0 < k) : m.memory.Permitted .write b k :=
  (hf.permitted .write b k).mpr (permitted_sub hf.rw.2 hlo (by have := hf.rsp0; omega) hk)

/-- A register change that keeps `rbp`, `rsp` and the callee-saved registers keeps the frame. -/
theorem Frame0.core (hf : Frame0 addr code frame m0 m) {core : State}
    (hrbp : core.read .rbp = m.core.read .rbp) (hrsp : core.read .rsp = m.core.read .rsp)
    (hcs : ∀ r ∈ [Reg.rbx, .r12, .r13, .r14, .r15], core.read r = m.core.read r) :
    Frame0 addr code frame m0 ⟨core, m.memory⟩ where
  loaded := hf.loaded
  abi := hf.abi
  room := hf.room
  rw := hf.rw
  apart := hf.apart
  rbp := hrbp.trans hf.rbp
  rsp := hrsp.trans hf.rsp
  savedRbp := hf.savedRbp
  calleeSaved := fun r hr => (hcs r hr).trans (hf.calleeSaved r hr)
  writes := hf.writes

/-- A store into the frame below the saved `rbp` keeps the frame. -/
theorem Frame0.store (hf : Frame0 addr code frame m0 m) (haddr : addr + code.length < 2 ^ 64)
    {a : Nat} {bytes : List Byte} {after : Memory} (hs : Stored m.memory after a bytes)
    (hlo : (m0.core.read .rsp).toNat - frame ≤ a)
    (hhi : a + bytes.length ≤ (m0.core.read .rsp).toNat - 8) {core : State}
    (hrbp : core.read .rbp = m.core.read .rbp) (hrsp : core.read .rsp = m.core.read .rsp)
    (hcs : ∀ r ∈ [Reg.rbx, .r12, .r13, .r14, .r15], core.read r = m.core.read r) :
    Frame0 addr code frame m0 ⟨core, after⟩ where
  loaded := by
    refine Silmaril.X86.Ext.Loaded.of_stored hf.loaded hs ?_
    have ha : (BitVec.ofNat 64 addr).toNat = addr := by
      rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt (by omega)
    rw [ha]
    have := hf.rsp0
    have hap : addr + code.length ≤ (m0.core.read .rsp).toNat - frame ∨
        (m0.core.read .rsp).toNat + 8 ≤ addr := hf.apart
    rcases hap with h | h
    · left; omega
    · right; omega
  abi := hf.abi
  room := hf.room
  rw := hf.rw
  apart := hf.apart
  rbp := hrbp.trans hf.rbp
  rsp := hrsp.trans hf.rsp
  savedRbp := by
    show after.readWith .read _ 8 = _
    rw [hs.readWith_disjoint .read _ 8 (.inr (by omega))]
    exact hf.savedRbp
  calleeSaved := fun r hr => (hcs r hr).trans (hf.calleeSaved r hr)
  writes := hf.writes.step hs fun off hoff => ⟨by omega, by omega⟩

end Frame

/-! ## Steps of the frame body -/

section Steps

variable {addr : Nat} {code : List Byte} {frame : Nat} {m0 m : MState}

theorem rip_add {addr o : Nat} {rip : BitVec 64} (h : rip = BitVec.ofNat 64 (addr + o)) :
    rip = BitVec.ofNat 64 addr + BitVec.ofNat 64 o := by
  rw [h, BitVec.ofNat_add]

theorem rip_next {addr o l : Nat} {rip : BitVec 64} (h : rip = BitVec.ofNat 64 (addr + o)) :
    rip + BitVec.ofNat 64 l = BitVec.ofNat 64 (addr + o + l) := by
  rw [h, ← BitVec.ofNat_add]

/-- The address of the frame slot `disp(%rbp)`, `disp = -n`, in a frame state. -/
theorem Frame0.slot_toNat (hf : Frame0 addr code frame m0 m) {d : BitVec 32} {n : Nat}
    (hd : d.signExtend 64 = -(BitVec.ofNat 64 n)) (hn : n + 8 ≤ frame) (next : BitVec 64) :
    ((Mem.ofReg .rbp none d).addr m.core next).toNat = (m0.core.read .rsp).toNat - 8 - n := by
  rw [ofReg_addr, hf.rbp]
  exact rbp_slot_toNat hd (by have := hf.rsp0; omega)

/-- `mov %reg32, disp(%rbp)`: a 4-byte store of the register's low half into the frame. -/
theorem step_store32 (hf : Frame0 addr code frame m0 m) {o : Nat}
    (hrip : m.core.rip = BitVec.ofNat 64 (addr + o)) (hfit : o + 3 ≤ code.length)
    {d : BitVec 32} {src : Reg}
    (hdec : Silmaril.X86.Open.decode ((code.drop o).take 3) =
      some (.base (.mov .d (.mem (Mem.ofReg .rbp none d)) src), 3))
    {n : Nat} (hd : d.signExtend 64 = -(BitVec.ofNat 64 n)) (h4 : 4 ≤ n) (hn : n + 8 ≤ frame) :
    ∃ after, Silmaril.X86.Open.step m =
        some ⟨{ m.core with rip := BitVec.ofNat 64 (addr + o + 3) }, after⟩ ∧
      Stored m.memory after ((m0.core.read .rsp).toNat - 8 - n)
        (leBytes (((m.core.read src).setWidth 32).setWidth 64) 4) := by
  have hslot := hf.slot_toNat hd hn (m.core.rip + BitVec.ofNat 64 3)
  have hw : m.memory.Permitted .write
      ((Mem.ofReg .rbp none d).addr m.core (m.core.rip + BitVec.ofNat 64 3)).toNat 4 := by
    have := hf.rsp0
    rw [hslot]; exact hf.writable (by omega) (by omega) (by omega)
  obtain ⟨after, hst, hstored⟩ := Silmaril.X86.Ext.storeN_isSome
    (v := ((m.core.read src).setWidth 32).setWidth 64) hw
  refine ⟨after, ?_, by rw [← hslot]; exact hstored⟩
  refine Silmaril.X86.Open.step_of_listed hf.loaded (rip_add hrip) hfit hdec ?_
  simp only [Silmaril.X86.Ext8.exec_base, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.writeRM,
    Sz.read, Sz.bytes, Sz.bits]
  rw [hst]
  simp [Silmaril.X86.Ext.retire, rip_next hrip]

/-- `mov disp(%rbp), %reg32`: a 4-byte load of a frame slot, zero-extended. -/
theorem step_load32 (hf : Frame0 addr code frame m0 m) {o : Nat}
    (hrip : m.core.rip = BitVec.ofNat 64 (addr + o)) (hfit : o + 3 ≤ code.length)
    {d : BitVec 32} {dst : Reg}
    (hdec : Silmaril.X86.Open.decode ((code.drop o).take 3) =
      some (.base (.load .d dst (Mem.ofReg .rbp none d)), 3))
    {n : Nat} (hd : d.signExtend 64 = -(BitVec.ofNat 64 n)) (hn : n + 8 ≤ frame) {v : BitVec 64}
    (hv : HoldsLE m.memory ((m0.core.read .rsp).toNat - 8 - n) 4 v) :
    Silmaril.X86.Open.step m =
      some ⟨{ Sz.d.write m.core dst (v.setWidth 32) with rip := BitVec.ofNat 64 (addr + o + 3) },
        m.memory⟩ := by
  have hslot := hf.slot_toNat hd hn (m.core.rip + BitVec.ofNat 64 3)
  rw [← hslot] at hv
  have hl := Silmaril.X86.Ext.loadN_of_holdsLE hv
  have hval32 : (BitVec.setWidth 32 (BitVec.ofNat 64 (v.toNat % 2 ^ (8 * 4))) : BitVec 32) =
      v.setWidth 32 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have : v.toNat < 2 ^ 64 := v.isLt
    rw [show (2 : Nat) ^ (8 * 4) = 2 ^ 32 from rfl]
    omega
  have hval : (BitVec.setWidth Sz.d.bits (BitVec.ofNat 64 (v.toNat % 2 ^ (8 * 4))) :
      BitVec Sz.d.bits) = (v.setWidth 32 : BitVec 32) := hval32
  refine Silmaril.X86.Open.step_of_listed hf.loaded (rip_add hrip) hfit hdec ?_
  simp only [Silmaril.X86.Ext8.exec_base, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.readRM]
  rw [show Sz.d.bytes = 4 from rfl, hl]
  simp only [Option.map_some, Silmaril.X86.Ext.retire, rip_next hrip]
  rw [hval]

/-- `add %src32, %dst32`. -/
theorem step_add32 (hl : Silmaril.X86.Ext.Loaded m.memory (BitVec.ofNat 64 addr) code) {o : Nat}
    (hrip : m.core.rip = BitVec.ofNat 64 (addr + o)) (hfit : o + 2 ≤ code.length) {dst src : Reg}
    (hdec : Silmaril.X86.Open.decode ((code.drop o).take 2) =
      some (.base (.alu .d .add (.reg dst) src), 2)) :
    Silmaril.X86.Open.step m =
      some ⟨{ Sz.d.write m.core dst (Sz.d.read m.core dst + Sz.d.read m.core src) with
        flags := Silmaril.X86.Ext.AluOp.flagsN .add (Sz.d.read m.core dst) (Sz.d.read m.core src)
        rip := BitVec.ofNat 64 (addr + o + 2) }, m.memory⟩ := by
  refine Silmaril.X86.Open.step_of_listed hl (rip_add hrip) hfit hdec ?_
  simp [Silmaril.X86.Ext.exec, Silmaril.X86.Ext.retire, Silmaril.X86.Ext.aluStep,
    Silmaril.X86.Ext.readRM, Silmaril.X86.Ext.writeRM, Silmaril.X86.Ext.AluOp.resultN,
    rip_next hrip]

/-- `cmp disp(%rbp), %reg32`: the flags of the 32-bit difference of the register and the slot. -/
theorem step_cmp32_mem (hf : Frame0 addr code frame m0 m) {o : Nat}
    (hrip : m.core.rip = BitVec.ofNat 64 (addr + o)) (hfit : o + 3 ≤ code.length)
    {d : BitVec 32} {dst : Reg}
    (hdec : Silmaril.X86.Open.decode ((code.drop o).take 3) =
      some (.base (.aluR .d .cmp dst (.mem (Mem.ofReg .rbp none d))), 3))
    {n : Nat} (hd : d.signExtend 64 = -(BitVec.ofNat 64 n)) (hn : n + 8 ≤ frame) {v : BitVec 64}
    (hv : HoldsLE m.memory ((m0.core.read .rsp).toNat - 8 - n) 4 v) :
    Silmaril.X86.Open.step m =
      some ⟨{ m.core with
        flags := Silmaril.X86.Ext.subFlagsN (Sz.d.read m.core dst) (v.setWidth 32)
        rip := BitVec.ofNat 64 (addr + o + 3) }, m.memory⟩ := by
  have hslot := hf.slot_toNat hd hn (m.core.rip + BitVec.ofNat 64 3)
  rw [← hslot] at hv
  have hl := Silmaril.X86.Ext.loadN_of_holdsLE hv
  have hval32 : (BitVec.setWidth 32 (BitVec.ofNat 64 (v.toNat % 2 ^ (8 * 4))) : BitVec 32) =
      v.setWidth 32 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    have : v.toNat < 2 ^ 64 := v.isLt
    rw [show (2 : Nat) ^ (8 * 4) = 2 ^ 32 from rfl]
    omega
  have hval : (BitVec.setWidth Sz.d.bits (BitVec.ofNat 64 (v.toNat % 2 ^ (8 * 4))) :
      BitVec Sz.d.bits) = (v.setWidth 32 : BitVec 32) := hval32
  refine Silmaril.X86.Open.step_of_listed hf.loaded (rip_add hrip) hfit hdec ?_
  simp only [Silmaril.X86.Ext8.exec_base, Silmaril.X86.Ext.exec, Silmaril.X86.Ext.aluStepR,
    Silmaril.X86.Ext.readRM]
  rw [show Sz.d.bytes = 4 from rfl, hl]
  simp only [Option.map_some, Silmaril.X86.Ext.retire, rip_next hrip]
  rw [hval]
  rfl

/-- `jcc rel8` whose condition is decided. -/
theorem step_jcc8 (hl : Silmaril.X86.Ext.Loaded m.memory (BitVec.ofNat 64 addr) code) {o : Nat}
    (hrip : m.core.rip = BitVec.ofNat 64 (addr + o)) (hfit : o + 2 ≤ code.length)
    {c : Silmaril.X86.Ext.Cond} {rel : BitVec 8}
    (hdec : Silmaril.X86.Open.decode ((code.drop o).take 2) = some (.base (.jcc8 c rel), 2))
    {taken : Bool} (hc : c.eval m.core.flags = some taken) :
    Silmaril.X86.Open.step m =
      some ⟨{ m.core with rip := (if taken then BitVec.ofNat 64 (addr + o + 2) + rel.signExtend 64
        else BitVec.ofNat 64 (addr + o + 2)) }, m.memory⟩ := by
  refine Silmaril.X86.Open.step_of_listed hl (rip_add hrip) hfit hdec ?_
  simp only [Silmaril.X86.Ext8.exec_base, Silmaril.X86.Ext.exec, hc, rip_next hrip]
  cases taken <;> rfl

/-- `jmp rel8`. -/
theorem step_jmp8 (hl : Silmaril.X86.Ext.Loaded m.memory (BitVec.ofNat 64 addr) code) {o : Nat}
    (hrip : m.core.rip = BitVec.ofNat 64 (addr + o)) (hfit : o + 2 ≤ code.length) {rel : BitVec 8}
    (hdec : Silmaril.X86.Open.decode ((code.drop o).take 2) = some (.base (.jmp8 rel), 2)) :
    Silmaril.X86.Open.step m =
      some ⟨{ m.core with rip := BitVec.ofNat 64 (addr + o + 2) + rel.signExtend 64 }, m.memory⟩ := by
  refine Silmaril.X86.Open.step_of_listed hl (rip_add hrip) hfit hdec ?_
  simp [Silmaril.X86.Ext.exec, rip_next hrip]

end Steps

/-! ## Values in slots -/

/-- The low 32 bits of a word, widened, have the same four bytes. -/
theorem holdsLE_setWidth32 {mem : Memory} {a : Nat} {v : BitVec 64} :
    HoldsLE mem a 4 ((v.setWidth 32).setWidth 64) ↔ HoldsLE mem a 4 v := by
  unfold HoldsLE
  rw [← Silmaril.X86.Ext.leBytes_setWidth32 v]

/-- Two words with the same low 32 bits have the same four bytes. -/
theorem holdsLE_of_low {mem : Memory} {a : Nat} {v w : BitVec 64}
    (h : v.setWidth 32 = w.setWidth 32) (hv : HoldsLE mem a 4 v) : HoldsLE mem a 4 w := by
  rw [← holdsLE_setWidth32] at hv ⊢
  rwa [← h]

/-- What a 4-byte slot holds, read back after a store elsewhere. -/
theorem holdsLE_stored_other {before after : Memory} {a : Nat} {bytes : List Byte}
    (hs : Stored before after a bytes) {b : Nat} {v : BitVec 64} (hb : HoldsLE before b 4 v)
    (hapart : b + 4 ≤ a ∨ a + bytes.length ≤ b) : HoldsLE after b 4 v :=
  Silmaril.X86.Ext.HoldsLE.of_stored_disjoint hs hb hapart

/-! ## Cut points of the target -/

/-- A machine state at an offset that is no point, with the stack pointer below the entry one,
is no cut point of the target. -/
theorem FnData.notCut (F : FnData) {k0 : List Frame} {x0 m : MState} {o : Nat}
    (hrip : m.core.rip = BitVec.ofNat 64 (F.addr + o)) (ho : ∀ q ∈ F.points, q.off ≠ o)
    (hlt : o < F.code.length) (hpts : ∀ q ∈ F.points, q.off < F.code.length)
    (haddr : F.addr + F.code.length < 2 ^ 64)
    (hrsp : m.core.read .rsp = x0.core.read .rsp - 8#64) :
    ¬ (F.corr Silmaril.X86.Open.isa k0).tgtCut x0 m := by
  intro h
  simp only [Corr.tgtCut, FnData.corr, Returned] at h
  rcases h with ⟨j, q, hq, hqrip⟩ | ⟨_, hret⟩
  · have hmem : q ∈ F.points := List.mem_of_getElem? hq
    have hq' : m.core.rip = BitVec.ofNat 64 (F.addr + q.off) := hqrip
    have h1 := congrArg BitVec.toNat (hrip.symm.trans hq')
    rw [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by have := hpts q hmem; omega)] at h1
    exact ho q hmem (by omega)
  · rw [hrsp] at hret
    have h3 := congrArg BitVec.toNat hret
    have := (x0.core.read .rsp).isLt
    bv_omega

end Silmaril.Project.CompilesTo

end
