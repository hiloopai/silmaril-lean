module

public import Silmaril.Machine.RiscV.OSSVerify.MemorySequence.Defs
public import Silmaril.Compiler.C.Sem.RefinedCOwnedByte.Defs
/-! An independently executed decoded LBU/ADDI/SB increment. Its access
certificate follows actual evolving Ext states. The mathematical byte successor
is the same as the owned RefinedC example. This is not a fetch or compiler theorem. -/
@[expose] public section
namespace Silmaril.Compile.C.Sem.RefinedCOwnedLPS
open Silmaril.Process
open Silmaril.RiscV
open Silmaril.RiscV.OSSVerify
open MemorySequence

def addOne : Ext.Compute := .base (.imm .add 5 5 1)
def code : List Ext.Instr := [.load .lbu 5 10 0, .compute addOne, .store .sb 10 5 0]
def word (v : UInt8) : Word := v.toBitVec.setWidth 64

def loaded (state : State) (v : UInt8) : State :=
  {state.write 5 (word v) with pc := state.pc + 4}
def added (state : State) (v : UInt8) : State := addOne.step (loaded state v)
def finished (state : State) (v : UInt8) : State :=
  {added state v with pc := (added state v).pc + 4}

private theorem successor_word (v : UInt8) (safe : v.toNat < 255) :
    word v + 1#64 = word (RefinedCOwnedByte.successor v) := by
  have h := RefinedCOwnedByte.successor_value v safe
  apply BitVec.eq_of_toNat_eq
  simp only [word, BitVec.toNat_add, BitVec.toNat_setWidth, UInt8.toNat_toBitVec]
  change (v.toNat % 2 ^ 64 + 1) % 2 ^ 64 =
    (RefinedCOwnedByte.successor v).toNat % 2 ^ 64
  have hv : (RefinedCOwnedByte.successor v).toNat = v.toNat + 1 := by omega
  rw [hv]
  omega

private theorem loaded_address (state : State) (v : UInt8) :
    Ext.effectiveAddress (loaded state v) 10 0 = state.read 10 := by
  simp [Ext.effectiveAddress, loaded, State.read, State.write, Silmaril.Machine.RegisterFile.write]

private theorem added_address (state : State) (v : UInt8) :
    Ext.effectiveAddress (added state v) 10 0 = state.read 10 := by
  simp [added, addOne, Ext.Compute.step, Ext.Compute.dest, Instr.dest, Ext.effectiveAddress,
    loaded, State.read, State.write, Silmaril.Machine.RegisterFile.write]

private theorem added_value (state : State) (v : UInt8) (safe : v.toNat < 255) :
    (added state v).read 5 = word (RefinedCOwnedByte.successor v) := by
  simp [added, addOne, Ext.Compute.step, Ext.Compute.dest, Ext.Compute.value,
    Instr.dest, Instr.value, ImmOp.eval, loaded, State.read, State.write,
    Silmaril.Machine.RegisterFile.write, successor_word v safe]

/-- Actual finite source execution is derived from primitive success witnesses;
no equality to the desired complete execution is assumed. -/
theorem trace (state : State) (memory final : Memory) (v : UInt8)
    (safe : v.toNat < 255)
    (read : memory.readBytes (state.read 10).toNat 1 = some [v.toBitVec])
    (written : memory.writeBytes (state.read 10).toNat
      [(RefinedCOwnedByte.successor v).toBitVec] = some final) :
    Trace code ⟨state, memory⟩ ⟨finished state v, final⟩ := by
  apply Trace.lbu 5 10 0 v.toBitVec
  · simpa [Ext.effectiveAddress] using read
  change Trace [.compute addOne, .store .sb 10 5 0] ⟨loaded state v, memory⟩ _
  apply Trace.compute addOne
  change Trace [.store .sb 10 5 0] ⟨added state v, memory⟩ _
  apply Trace.sb 10 5 0 v.toBitVec (nextMemory := final)
  · have backed : memory.bytes.get? (state.read 10).toNat = some v.toBitVec := by
      simpa using Memory.readWith_get read 0 (by simp)
    simpa only [added_address] using backed
  · change memory.writeBytes (Ext.effectiveAddress (added state v) 10 0).toNat
      [((added state v).read 5).setWidth 8] = some final
    rw [added_address, added_value state v safe]
    simpa only [word, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
      BitVec.setWidth_eq] using written
  exact Trace.nil _

/-- The independent effect interpreter reaches the exact successor byte while
retaining complete architectural register/memory agreement with Ext. -/
theorem increment (state : State) (memory final : Memory) (v : UInt8)
    (safe : v.toNat < 255)
    (read : memory.readBytes (state.read 10).toNat 1 = some [v.toBitVec])
    (written : memory.writeBytes (state.read 10).toNat
      [(RefinedCOwnedByte.successor v).toBitVec] = some final)
    (core : LPS.Core) (mem : LPS.Word → Option LPS.Byte)
    (agree : LPS.Agree state core) (related : MemoryRelation.Rel memory mem)
    (segs : List LPS.Segment) :
    ∃ finalCore finalMem,
      run segs code core mem = .ok (finalCore, finalMem) ∧
      finalCore.rget 5 = word (RefinedCOwnedByte.successor v) ∧
      finalCore.pc = state.pc + 12 ∧
      finalMem (state.read 10) = some (RefinedCOwnedByte.successor v).toBitVec ∧
      MemoryRelation.Rel final finalMem ∧ Memory.WritesOnly memory final (state.read 10).toNat 1 := by
  obtain ⟨fc, fm, executed, same, relatedFinal⟩ :=
    (trace state memory final v safe read written).simulate segs agree related
  have changed : final.bytes.get? (state.read 10).toNat =
      some (RefinedCOwnedByte.successor v).toBitVec := by
    simpa using Memory.writeBytes_get written 0 (by simp)
  refine ⟨fc, fm, executed, ?_, ?_, (relatedFinal _).trans changed, relatedFinal,
    Memory.writeBytes_writesOnly written⟩
  · exact (same.2 5).trans (added_value state v safe)
  · exact same.1.trans (by simp [finished, added, loaded, Ext.Compute.step, BitVec.add_assoc])

end Silmaril.Compile.C.Sem.RefinedCOwnedLPS
