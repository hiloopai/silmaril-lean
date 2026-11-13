module

public import Silmaril.Compiler.C.Sem.RefinedCOwnedLPS.Defs
public import Silmaril.Machine.RiscV.OSSVerify.MemoryRelationChecks.Defs
@[expose] public section
namespace Silmaril.Compile.C.Sem.RefinedCOwnedLPS.Checks
open Silmaril.Process
open Silmaril.RiscV
open Silmaril.RiscV.OSSVerify
open Silmaril.Cerberus.Assertion.ConcreteResources

def pair (v w : UInt8) : Memory :=
  ⟨[⟨4096, 2, ⟨true, true, false⟩⟩],
    (({} : ByteMemory).insert 4096 v.toBitVec).insert 4097 w.toBitVec⟩

theorem pair_read (v w : UInt8) : (pair v w).readBytes 4096 1 = some [v.toBitVec] := by
  simp [pair, Memory.readBytes, Memory.readWith, Memory.checkSpan, Memory.permits,
    Region.Contains, Permissions.allows, addressLimit, Memory.readBacking,
    Std.ExtHashMap.getElem_insert]

theorem pair_write (v w new : UInt8) :
    (pair v w).writeBytes 4096 [new.toBitVec] = some (pair new w) := by
  simp [pair, Memory.writeBytes, Memory.checkSpan, Memory.permits,
    Region.Contains, Permissions.allows, addressLimit, Memory.install]
  apply Std.ExtHashMap.ext_getElem?
  intro a
  by_cases first : a = 4096
  · subst a; simp [Std.ExtHashMap.getElem_insert]
  · by_cases second : a = 4097
    · subst a; simp [Std.ExtHashMap.getElem_insert]
    · simp only [Std.ExtHashMap.getElem?_insert, beq_iff_eq,
        ite_eq_right (Ne.symm first), ite_eq_right (Ne.symm second)]

/-- Every safe owned input and arbitrary frame byte has an actual independent
load/update/store execution. The physical frame byte is observed after execution. -/
theorem independent_pair (v w : UInt8) (safe : v.toNat < 255) :
    ∃ initialCore finalCore : LPS.Core, ∃ finalMem,
      MemorySequence.run [] code initialCore (MemoryRelation.overlay (pair v w)) =
        .ok (finalCore, finalMem) ∧
      finalCore.rget 5 = word (RefinedCOwnedByte.successor v) ∧
      finalMem 4096 = some (RefinedCOwnedByte.successor v).toBitVec ∧
      finalMem 4097 = some w.toBitVec := by
  obtain ⟨state, core, agree, address⟩ := MemoryRelation.Checks.core_witness
  have pointer : state.read 10 = 4096 := by simpa [Ext.effectiveAddress] using address
  have read : (pair v w).readBytes (state.read 10).toNat 1 = some [v.toBitVec] := by
    rw [pointer]; exact pair_read v w
  have written : (pair v w).writeBytes (state.read 10).toNat
      [(RefinedCOwnedByte.successor v).toBitVec] = some (pair (RefinedCOwnedByte.successor v) w) := by
    rw [pointer]; exact pair_write _ _ _
  obtain ⟨fc, fm, executed, returned, _, changed, related, _⟩ :=
    increment state (pair v w) (pair (RefinedCOwnedByte.successor v) w) v safe read written
      core (MemoryRelation.overlay (pair v w)) agree (MemoryRelation.overlay_related _) []
  refine ⟨core, fc, fm, executed, returned, ?_, ?_⟩
  · simpa only [pointer] using changed
  · simpa [pair] using related 4097

/-- The actual C1 call and independently interpreted memory sequence agree on
the owned successor and on the arbitrary frame byte, for all safe byte inputs. -/
theorem source_and_independent (v w : UInt8) (safe : v.toNat < 255) :
    C1.callFn RefinedCOwnedByte.program 8 RefinedCOwnedByte.fSym [C1.base]
      ⟨{}, {}, pairMemory v w, .empty⟩ =
      .ok (0, ⟨{}, {}, writeByte (pairMemory v w) C1.base (RefinedCOwnedByte.successor v), .empty⟩) ∧
    C1.load (writeByte (pairMemory v w) C1.base (RefinedCOwnedByte.successor v))
      (.int 1 false) (C1.base + 1) = .ok w.toNat ∧
    ∃ initialCore finalCore : LPS.Core, ∃ finalMem,
      MemorySequence.run [] code initialCore (MemoryRelation.overlay (pair v w)) =
        .ok (finalCore, finalMem) ∧
      finalCore.rget 5 = word (RefinedCOwnedByte.successor v) ∧
      finalMem 4096 = some (RefinedCOwnedByte.successor v).toBitVec ∧
      finalMem 4097 = some w.toBitVec :=
  ⟨(RefinedCOwnedByte.pair_call v w safe).1,
    (RefinedCOwnedByte.pair_call v w safe).2, independent_pair v w safe⟩

end Silmaril.Compile.C.Sem.RefinedCOwnedLPS.Checks
