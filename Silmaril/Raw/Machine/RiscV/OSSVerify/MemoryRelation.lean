module

public import Silmaril.Machine.RiscV.LPS.Compare.Exec.Defs
public import Silmaril.RiscV.LPS.Machine

/-! Decoded byte-memory retirement through the independently ported LPS effect
interpreter and existing Ext machine. Source: LPS f1006fe8178338a499b5e5c41be83006c4edd058,
Riscv/Sem.v load/store and LinuxProcessSem/RiscvSemantics.v interp_eff_accesses.
This uses the full LPS port, not an ALU-only replacement for memory effects.
Ext read/write permissions remain explicit; no fault/fetch/provenance equivalence
is asserted. A byte access has no alignment restriction. -/
@[expose] public section
namespace Silmaril.RiscV.OSSVerify.MemoryRelation
open Silmaril.Process
open Silmaril.RiscV

/-- Relate every architectural address, including absent backing bytes. -/
def Rel (memory : Memory) (overlay : LPS.Word → Option LPS.Byte) : Prop :=
  ∀ address, overlay address = memory.bytes.get? address.toNat

/-- Every finite mapped Ext memory has a concrete LPS overlay witness. -/
def overlay (memory : Memory) : LPS.Word → Option LPS.Byte :=
  fun address => memory.bytes.get? address.toNat

theorem overlay_related (memory : Memory) : Rel memory (overlay memory) := fun _ => rfl

private theorem byte_value (byte : Byte) :
    Ext.LoadOp.lbu.value [byte] = byte.setWidth 64 := by
  simp [Ext.LoadOp.value, Ext.LoadOp.width, Ext.LoadOp.signed, Ext.leValue]

private theorem read_backing {memory : Memory} {address : Nat} {byte : Byte}
    (read : memory.readBytes address 1 = some [byte]) :
    memory.bytes.get? address = some byte := by
  simpa using Memory.readWith_get read 0 (by simp)

private theorem lps_read_byte (segs : List LPS.Segment) (mem : LPS.Word → Option LPS.Byte)
    (address : LPS.Word) (byte : LPS.Byte) (present : mem address = some byte) :
    LPS.ovReadBytes segs mem address 1 = some [byte] := by
  simp [LPS.ovReadBytes, present]

private theorem lps_byte_value (byte : Byte) :
    ((LPS.leBytesToWord [byte]).extractLsb' 0 8).setWidth 64 = byte.setWidth 64 := by
  simp [LPS.leBytesToWord, LPS.bytesLeToNat,
    BitVec.extractLsb'_setWidth_of_le (by decide : 0 + 8 ≤ 64)]

/-- A successful permission-checked Ext LBU retires through LPS's actual effect
interpreter with the same register/PC result and unchanged memory. All aliases,
x0 destinations and signed offsets are covered. -/
theorem lbu {s : RiscV.State} {c : LPS.Core} (agree : LPS.Agree s c)
    (memory : Memory) (mem : LPS.Word → Option LPS.Byte) (related : Rel memory mem)
    (segs : List LPS.Segment) (rd rs : Reg) (offset : BitVec 12) (byte : Byte)
    (read : memory.readBytes (Ext.effectiveAddress s rs offset).toNat 1 = some [byte]) :
    let address := Ext.effectiveAddress s rs offset
    let finalCore := LPS.Core.rset rd (byte.setWidth 64) {c with pc := c.pc + 4}
    LPS.interpEffAccesses segs (LPS.exec 4 (LPS.embed (.load .lbu rd rs offset)) c) mem =
        .ok ⟨(finalCore, mem), [(address, 1)]⟩ ∧
      Ext.Instr.exec (.load .lbu rd rs offset) ⟨s, memory⟩ =
        .retired ⟨{s.write rd (byte.setWidth 64) with pc := s.pc + 4}, memory⟩ ∧
      LPS.Agree {s.write rd (byte.setWidth 64) with pc := s.pc + 4} finalCore := by
  have present := (related (Ext.effectiveAddress s rs offset)).trans (read_backing read)
  refine ⟨?_, ?_, ?_⟩
  · rw [LPS.exec_embed_load agree]
    simp only [LPS.embedLoadOp, LPS.loadVal, LPS.interpEffAccesses,
      LPS.widthBytes, lps_read_byte segs mem _ byte present, LPS.zext, lps_byte_value,
      Bool.false_eq_true, ite_false]
  · simp [Ext.Instr.exec, Ext.LoadOp.width, read, byte_value, Nat.mod_one]
  · simpa only [agree.1] using agree.write rd (byte.setWidth 64) (s.pc + 4)

/-- A byte update agrees at every architectural address. -/
theorem write_related {memory final : Memory} {mem : LPS.Word → Option LPS.Byte}
    (related : Rel memory mem) (address : LPS.Word) (byte : Byte)
    (written : memory.writeBytes address.toNat [byte] = some final) :
    Rel final (LPS.writeToMem mem address [byte]) := by
  intro other
  simp only [LPS.writeToMem, LPS.eqB, beq_iff_eq]
  by_cases same : other = address
  · subst other
    rw [ite_eq_left rfl]
    symm
    simpa using Memory.writeBytes_get written 0 (by simp)
  · have different : other.toNat ≠ address.toNat := fun h => same (BitVec.eq_of_toNat_eq h)
    rw [ite_eq_right different]
    have outside := Memory.writeBytes_writesOnly written
    exact (related other).trans (outside.2 other.toNat (by simp only [List.length_singleton]; omega)).symm

private theorem invalidation_agrees {s : RiscV.State} {c : LPS.Core}
    (agree : LPS.Agree s c) (address : LPS.Word) :
    LPS.Agree s (LPS.invalResv address c) := by
  unfold LPS.invalResv
  split
  · split <;> exact agree
  · exact agree

private theorem invalidation_fields (c : LPS.Core) (address : LPS.Word) :
    (LPS.invalResv address c).fregs = c.fregs ∧
      (LPS.invalResv address c).fcsr = c.fcsr := by
  unfold LPS.invalResv
  split
  · split <;> exact ⟨rfl, rfl⟩
  · exact ⟨rfl, rfl⟩

/-- A successful backed, permission-checked Ext SB retires through the actual
LPS interpreter and preserves the pointwise memory relation at every address.
LPS reservation invalidation is retained, while floating registers/fcsr survive. -/
theorem sb {s : RiscV.State} {c : LPS.Core} (agree : LPS.Agree s c)
    (memory final : Memory) (mem : LPS.Word → Option LPS.Byte) (related : Rel memory mem)
    (segs : List LPS.Segment) (rs1 rs2 : Reg) (offset : BitVec 12) (old : Byte)
    (backed : memory.bytes.get? (Ext.effectiveAddress s rs1 offset).toNat = some old)
    (written : memory.writeBytes (Ext.effectiveAddress s rs1 offset).toNat
      [(s.read rs2).setWidth 8] = some final) :
    let address := Ext.effectiveAddress s rs1 offset
    let updated := LPS.writeToMem mem address [(s.read rs2).setWidth 8]
    ∃ finalCore,
      LPS.interpEffAccesses segs (LPS.exec 4 (LPS.embed (.store .sb rs1 rs2 offset)) c) mem =
        .ok ⟨(finalCore, updated), [(address, 1)]⟩ ∧
      Ext.Instr.exec (.store .sb rs1 rs2 offset) ⟨s, memory⟩ =
        .retired ⟨{s with pc := s.pc + 4}, final⟩ ∧
      LPS.Agree {s with pc := s.pc + 4} finalCore ∧ Rel final updated ∧
      Memory.WritesOnly memory final address.toNat 1 ∧
      finalCore.fregs = c.fregs ∧ finalCore.fcsr = c.fcsr := by
  let address := Ext.effectiveAddress s rs1 offset
  have present : mem address = some old := (related address).trans backed
  have storeOk : LPS.storeOk segs mem address 1 = true := by
    simp [LPS.storeOk, LPS.wview, present]
  refine ⟨LPS.invalResv address {c with pc := c.pc + 4}, ?_, ?_, ?_,
    write_related related address _ written, Memory.writeBytes_writesOnly written,
    (invalidation_fields _ address).1, (invalidation_fields _ address).2⟩
  · rw [LPS.exec_embed_store agree]
    have truncation : (s.read rs2).extractLsb' 0 8 = (s.read rs2).setWidth 8 :=
      (BitVec.setWidth_eq_extractLsb' (by decide : 8 ≤ 64)).symm
    have serialized : BitVec.ofNat 8 ((s.read rs2).toNat % 256) = (s.read rs2).setWidth 8 := by
      apply BitVec.eq_of_toNat_eq
      simp
    simp only [address] at storeOk ⊢
    simp [LPS.embedStoreOp, LPS.storeVal, LPS.interpEffAccesses, LPS.widthBytes,
      storeOk, LPS.natToLeBytes, truncation, serialized]
  · simp [Ext.Instr.exec, Ext.StoreOp.width, Ext.leBytes, Nat.mod_one, written]

  · apply invalidation_agrees
    exact ⟨congrArg (fun pc => pc + 4) agree.1, agree.2⟩

end Silmaril.RiscV.OSSVerify.MemoryRelation
