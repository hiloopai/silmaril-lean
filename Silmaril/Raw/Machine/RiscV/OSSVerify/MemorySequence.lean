module

public import Silmaril.Machine.RiscV.OSSVerify.MemoryRelation.Defs
/-! Finite decoded compute/LBU/SB sequences. Source certificates are indexed by
actual evolving Ext machine states and checked primitive-access witnesses. The
independent runner executes full LPS effect trees; no source oracle is consulted.
The theorem transfers all register reads/PC and every architectural memory byte.
Fetch, code layout and equality of fault behavior are separate obligations. -/
@[expose] public section
namespace Silmaril.RiscV.OSSVerify.MemorySequence
open Silmaril.Process
open Silmaril.RiscV
open MemoryRelation

/-- Actual independent execution of each decoded instruction's effect tree. -/
def run (segs : List LPS.Segment) : List Ext.Instr → LPS.Core →
    (LPS.Word → Option LPS.Byte) → LPS.MachineResult (LPS.Core × (LPS.Word → Option LPS.Byte))
  | [], core, mem => .ok (core, mem)
  | i :: rest, core, mem =>
    match LPS.interpEff segs (LPS.exec 4 (LPS.embed i) core) mem with
    | .ok (nextCore, nextMem) => run segs rest nextCore nextMem
    | .fault => .fault
    | .unmodeled => .unmodeled

/-- Actual Ext decoded execution, stopping on any non-retirement outcome. -/
def sourceRun : List Ext.Instr → Ext.MState → Option Ext.MState
  | [], state => some state
  | i :: rest, state => match i.exec state with
    | .retired next => sourceRun rest next
    | _ => none

/-- A compositional success certificate: every access is checked in the memory
that exists at that point. SB backing is explicit because Ext can create backing
whereas the independent overlay interpreter requires a writable existing byte. -/
inductive Trace : List Ext.Instr → Ext.MState → Ext.MState → Prop
  | nil (state) : Trace [] state state
  | compute (instruction : Ext.Compute) (rest) (state final : Ext.MState)
      (tail : Trace rest ⟨instruction.step state.core, state.memory⟩ final) :
      Trace (.compute instruction :: rest) state final
  | lbu (rd rs : Reg) (offset : BitVec 12) (byte : Byte) (rest) (state final : Ext.MState)
      (read : state.memory.readBytes (Ext.effectiveAddress state.core rs offset).toNat 1 = some [byte])
      (tail : Trace rest ⟨{state.core.write rd (byte.setWidth 64) with pc := state.core.pc + 4},
        state.memory⟩ final) :
      Trace (.load .lbu rd rs offset :: rest) state final
  | sb (rs1 rs2 : Reg) (offset : BitVec 12) (old : Byte) (rest)
      (state final : Ext.MState) (nextMemory : Memory)
      (backed : state.memory.bytes.get? (Ext.effectiveAddress state.core rs1 offset).toNat = some old)
      (written : state.memory.writeBytes (Ext.effectiveAddress state.core rs1 offset).toNat
        [(state.core.read rs2).setWidth 8] = some nextMemory)
      (tail : Trace rest ⟨{state.core with pc := state.core.pc + 4}, nextMemory⟩ final) :
      Trace (.store .sb rs1 rs2 offset :: rest) state final

/-- Certificates imply execution of the existing Ext instruction semantics. -/
theorem Trace.source {code : List Ext.Instr} {initial final : Ext.MState}
    (trace : Trace code initial final) : sourceRun code initial = some final := by
  induction trace with
  | nil => rfl
  | compute instruction rest state final tail ih => exact ih
  | lbu rd rs offset byte rest state final read tail ih =>
    simpa [sourceRun, Ext.Instr.exec, Ext.LoadOp.width, Nat.mod_one, read,
      Ext.LoadOp.value, Ext.LoadOp.signed, Ext.leValue] using ih
  | sb rs1 rs2 offset old rest state final nextMemory backed written tail ih =>
    simpa [sourceRun, Ext.Instr.exec, Ext.StoreOp.width, Nat.mod_one, Ext.leBytes, written] using ih

/-- Actual independent execution preserves the full state/memory relation through
any finite mixture of computations, unsigned byte loads and byte stores. -/
theorem Trace.simulate {code : List Ext.Instr} {initial final : Ext.MState}
    (trace : Trace code initial final) (segs : List LPS.Segment)
    {core : LPS.Core} {mem : LPS.Word → Option LPS.Byte}
    (agree : LPS.Agree initial.core core) (related : Rel initial.memory mem) :
    ∃ finalCore finalMem, run segs code core mem = .ok (finalCore, finalMem) ∧
      LPS.Agree final.core finalCore ∧ Rel final.memory finalMem := by
  induction trace generalizing core mem with
  | nil state => exact ⟨core, mem, rfl, agree, related⟩
  | compute instruction rest state final tail ih =>
    obtain ⟨nextCore, execution, nextAgree⟩ := agree.compute instruction
    have step : LPS.interpEff segs (LPS.exec 4 (LPS.embed (.compute instruction)) core) mem =
        .ok (nextCore, mem) := by
      rw [show LPS.embed (.compute instruction) = LPS.embedCompute instruction from rfl, execution]
      rfl
    obtain ⟨fc, fm, executed, same, memory⟩ := ih nextAgree related
    exact ⟨fc, fm, by simpa only [run, step] using executed, same, memory⟩
  | lbu rd rs offset byte rest state final read tail ih =>
    have result := MemoryRelation.lbu agree state.memory mem related segs rd rs offset byte read
    have step := congrArg LPS.MachineResult.dropAccessReport result.1
    change LPS.interpEff segs (LPS.exec 4 (LPS.embed (.load .lbu rd rs offset)) core) mem =
      .ok (LPS.Core.rset rd (byte.setWidth 64) {core with pc := core.pc + 4}, mem) at step
    obtain ⟨fc, fm, executed, same, memory⟩ := ih result.2.2 related
    exact ⟨fc, fm, by simpa only [run, step] using executed, same, memory⟩
  | sb rs1 rs2 offset old rest state final nextMemory backed written tail ih =>
    obtain ⟨nextCore, execution, _, nextAgree, nextRelated, _⟩ :=
      MemoryRelation.sb agree state.memory nextMemory mem related segs rs1 rs2 offset old backed written
    have step := congrArg LPS.MachineResult.dropAccessReport execution
    change LPS.interpEff segs (LPS.exec 4 (LPS.embed (.store .sb rs1 rs2 offset)) core) mem =
      .ok (nextCore, _) at step
    obtain ⟨fc, fm, executed, same, memory⟩ := ih nextAgree nextRelated
    exact ⟨fc, fm, by simpa only [run, step] using executed, same, memory⟩

/-- Any final-state assertion proved on the Ext execution transfers to the
independently executed result under an explicit relational assertion reading. -/
theorem Trace.post {code : List Ext.Instr} {initial final : Ext.MState}
    (trace : Trace code initial final) (segs : List LPS.Segment)
    {core : LPS.Core} {mem : LPS.Word → Option LPS.Byte}
    (agree : LPS.Agree initial.core core) (related : Rel initial.memory mem)
    (post : LPS.Core → (LPS.Word → Option LPS.Byte) → Prop)
    (proved : ∀ fc fm, LPS.Agree final.core fc → Rel final.memory fm → post fc fm) :
    ∃ fc fm, run segs code core mem = .ok (fc, fm) ∧ post fc fm := by
  obtain ⟨fc, fm, executed, same, memory⟩ := trace.simulate segs agree related
  exact ⟨fc, fm, executed, proved fc fm same memory⟩

end Silmaril.RiscV.OSSVerify.MemorySequence
