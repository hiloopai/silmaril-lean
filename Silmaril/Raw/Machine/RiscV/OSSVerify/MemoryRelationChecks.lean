module

public import Silmaril.Machine.RiscV.OSSVerify.MemoryRelation.Defs
@[expose] public section
namespace Silmaril.RiscV.OSSVerify.MemoryRelation.Checks
open Silmaril.Process
open Silmaril.RiscV

/-- A physically backed writable byte at the owned-cell examples' address. -/
def mapped (byte : Byte) : Memory :=
  ⟨[⟨4096, 1, ⟨true, true, false⟩⟩], ({} : ByteMemory).insert 4096 byte⟩

theorem mapped_read (byte : Byte) : (mapped byte).readBytes 4096 1 = some [byte] := by
  simp [mapped, Memory.readBytes, Memory.readWith, Memory.checkSpan, Memory.permits,
    Region.Contains, Permissions.allows, addressLimit, Memory.readBacking]

theorem mapped_store (old byte : Byte) :
    (mapped old).writeBytes 4096 [byte] = some (mapped byte) := by
  simp [mapped, Memory.writeBytes, Memory.checkSpan, Memory.permits,
    Region.Contains, Permissions.allows, addressLimit, Memory.install]
  apply Std.ExtHashMap.ext_getElem?
  intro address
  simp only [Std.ExtHashMap.getElem?_insert]
  split <;> rfl

/-- Every pair of old/new byte values has admitted source accesses and a related
independent memory witness. These are not implication-only examples. -/
theorem admitted (old byte : Byte) :
    Rel (mapped old) (overlay (mapped old)) ∧
      (mapped old).readBytes 4096 1 = some [old] ∧
      (mapped old).writeBytes 4096 [byte] = some (mapped byte) :=
  ⟨overlay_related _, mapped_read _, mapped_store _ _⟩

/-- Register-agreement premises also have explicit concrete witnesses. -/
theorem core_witness : ∃ s : RiscV.State, ∃ c : LPS.Core,
    LPS.Agree s c ∧ Ext.effectiveAddress s 10 0 = 4096 := by
  let s : RiscV.State := ⟨fun _ => 0, 0⟩
  let c : LPS.Core := ⟨.empty, .empty, 0, 0, none⟩
  have agree : LPS.Agree s c := by
    refine ⟨rfl, ?_⟩
    intro r
    simp [s, c, LPS.Core.rget, LPS.isX0, LPS.regGet, LPS.BvMap.empty,
      LPS.BvMap.get, LPS.w0, State.read]
  refine ⟨{s.write 10 4096 with pc := 0}, LPS.Core.rset 10 4096 {c with pc := 0},
    agree.write 10 4096 0, ?_⟩
  simp [Ext.effectiveAddress, State.read, State.write, Silmaril.Machine.RegisterFile.write]

/-- For every possible byte there are concrete agreeing register states and
actual independent decoded LBU retirement, with an exact accessed-byte report. -/
theorem actual_lbu (byte : Byte) : ∃ s : RiscV.State, ∃ c finalCore : LPS.Core,
    LPS.Agree s c ∧
      LPS.interpEffAccesses [] (LPS.exec 4 (LPS.embed (.load .lbu 5 10 0)) c)
        (overlay (mapped byte)) =
        .ok ⟨(finalCore, overlay (mapped byte)), [(4096, 1)]⟩ := by
  obtain ⟨s, c, agree, address⟩ := core_witness
  have read : (mapped byte).readBytes (Ext.effectiveAddress s 10 0).toNat 1 = some [byte] := by
    rw [address]
    exact mapped_read byte
  refine ⟨s, c, LPS.Core.rset 5 (byte.setWidth 64) {c with pc := c.pc + 4}, agree, ?_⟩
  simpa only [address] using
    (lbu agree (mapped byte) (overlay (mapped byte)) (overlay_related _) [] 5 10 0 byte read).1

/-- Both independent and local decoders identify the actual standard words. -/
example : LPS.decode 0x00054283#32 = some (LPS.embed (.load .lbu 5 10 0)) := by decide
example : Ext.decode 0x00054283#32 = some (.load .lbu 5 10 0) := by decide
example : LPS.decode 0x00550023#32 = some (LPS.embed (.store .sb 10 5 0)) := by decide
example : Ext.decode 0x00550023#32 = some (.store .sb 10 5 0) := by decide

/-- Empty backing faults in the actual independent effect interpreter. -/
example : LPS.interpEffAccesses []
    (.load 8 4096 (fun _ => .done ⟨.empty, .empty, 0, 0, none⟩))
    (fun _ => none) = .fault := rfl

/-- Ext permissions are a necessary bridge premise: backing alone is insufficient. -/
example (byte : Byte) :
    ({mapped byte with regions := []} : Memory).readBytes 4096 1 = none := rfl

/-- Same-address stores clear the upstream reservation; other-address stores keep it. -/
example (c : LPS.Core) : (LPS.invalResv 4096 {c with resv := some 4096}).resv = none := by
  simp [LPS.invalResv]
example (c : LPS.Core) : (LPS.invalResv 4096 {c with resv := some 8192}).resv = some 8192 := by
  simp [LPS.invalResv]

end Silmaril.RiscV.OSSVerify.MemoryRelation.Checks
