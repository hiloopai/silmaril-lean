module

public import Silmaril.Process.LPS.Machines.X86RepStosq

/-! Concrete fetched-byte controls for the optional DF=0 REP STOSQ profile. -/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 4096

namespace Silmaril.Process.LPS.Machines.X86RepStosqControls

open Silmaril.X86
open Silmaril.Process (Memory)
open X86RepStosq

def value : Word := 0x0807060504030201

def memory (writable : Bool) : Memory :=
  ⟨[⟨0x1000, 3, ⟨true, false, true⟩⟩,
     ⟨0x4000, 8, ⟨true, writable, false⟩⟩], Memory.install {} 0x1000 bytes⟩

def core (count address : Word) : Silmaril.X86.State where
  regs register := match register with
    | .rcx => count
    | .rdi => address
    | .rax => value
    | _ => 0
  rip := 0x1000
  flags := ⟨some false, some true, none, some false, some false, some false⟩

def state (count address : Word) (writable : Bool := true) : X86State :=
  ⟨⟨core count address, memory writable⟩, none⟩

theorem fetched (writable : Bool) :
    (memory writable).fetchBytes 0x1000 3 = some bytes := by
  apply Memory.readWith_eq (memory writable) .execute 0x1000 bytes
    (by cases writable <;> decide +kernel)
  intro index bound
  exact Memory.install_get _ _ _ index bound

def afterStore : Memory :=
  { memory true with bytes := Memory.install (memory true).bytes 0x4000 (Ext.leBytes value 8) }

theorem stored : Ext.storeN (memory true) 0x4000 8 value = some afterStore := by
  rfl

def next (count : Word) : X86State :=
  ⟨⟨{ ((core count 0x4000).write .rcx (count - 1)).write .rdi 0x4008 with
    rip := if count = 1 then 0x1003 else 0x1000 }, afterStore⟩, none⟩

/-- A real UserIsa step fetches the bytes, writes one word and advances RIP. -/
theorem one_element (platform : Ext.Wire.Platform) :
    (x86WireDf0RepStosq platform).step [] (state 1 0x4000) =
      .ok ⟨next 1, [(0x1000, 3), (0x4000, 8)]⟩ := by
  change step platform (state 1 0x4000) = _
  rw [step_rep platform (state 1 0x4000) (fetched true),
    iterate_store (state 1 0x4000) afterStore (by decide) stored]
  rfl

/-- A nonvacuous strict gain: the same fetched state was previously unmodeled. -/
theorem original_declines (platform : Ext.Wire.Platform) :
    x86WireStep platform (state 1 0x4000) = .unmodeled :=
  wire_rep_unmodeled platform (state 1 0x4000) (fetched true)

/-- Zero count succeeds even when the destination is an invalid unmapped address. -/
theorem zero_count_no_data_access (platform : Ext.Wire.Platform) :
    (x86WireDf0RepStosq platform).step [] (state 0 0) =
      .ok ⟨⟨⟨{ core 0 0 with rip := 0x1003 }, memory true⟩, none⟩, [(0x1000, 3)]⟩ := by
  change step platform (state 0 0) = _
  rw [step_rep platform (state 0 0) (fetched true), iterate_zero (state 0 0) (by rfl)]
  rfl

theorem unmapped_destination_faults (platform : Ext.Wire.Platform) :
    (x86WireDf0RepStosq platform).step [] (state 1 0) = .fault := by
  change step platform (state 1 0) = _
  rw [step_rep platform (state 1 0) (fetched true)]
  exact iterate_fault _ (by decide) (by rfl)

theorem readonly_destination_faults (platform : Ext.Wire.Platform) :
    (x86WireDf0RepStosq platform).step [] (state 1 0x4000 false) = .fault := by
  change step platform (state 1 0x4000 false) = _
  rw [step_rep platform (state 1 0x4000 false) (fetched false)]
  exact iterate_fault _ (by decide) (by rfl)

/-- The full eight-byte span must be writable; no partial element is committed. -/
theorem crossing_destination_faults (platform : Ext.Wire.Platform) :
    (x86WireDf0RepStosq platform).step [] (state 1 0x4004) = .fault := by
  change step platform (state 1 0x4004) = _
  rw [step_rep platform (state 1 0x4004) (fetched true)]
  exact iterate_fault _ (by decide) (by rfl)

/-- For multiple elements, the first store commits but RIP remains unchanged. -/
theorem first_of_two (platform : Ext.Wire.Platform) :
    (x86WireDf0RepStosq platform).step [] (state 2 0x4000) =
      .ok ⟨next 2, [(0x1000, 3), (0x4000, 8)]⟩ := by
  change step platform (state 2 0x4000) = _
  rw [step_rep platform (state 2 0x4000) (fetched true),
    iterate_store (state 2 0x4000) afterStore (by decide) stored]
  rfl

theorem afterStore_fetch : afterStore.fetchBytes 0x1000 3 = some bytes := by
  have frame := (Memory.writesOnly_iff_writesWithin (memory true) afterStore 0x4000 8).mp
    (Ext.storeN_writesOnly stored)
  have unchanged := frame.fetchBytes (address := 0x1000) (length := 3) (by
    intro offset bound
    omega)
  exact unchanged.trans (fetched true)

/-- Earlier completed elements persist if the following element faults. -/
theorem second_of_two_faults (platform : Ext.Wire.Platform) :
    (x86WireDf0RepStosq platform).step [] (next 2) = .fault := by
  change step platform (next 2) = _
  rw [step_rep platform (next 2) afterStore_fetch]
  exact iterate_fault _ (by decide) (by rfl)

theorem stored_bytes : afterStore.readBytes 0x4000 8 = some [1, 2, 3, 4, 5, 6, 7, 8] := by
  apply Memory.readWith_eq afterStore .read 0x4000 [1, 2, 3, 4, 5, 6, 7, 8] (by decide +kernel)
  intro index bound
  exact Memory.install_get _ _ _ index bound

theorem flags_preserved : (next 1).m.core.flags = (state 1 0x4000).m.core.flags := rfl

theorem progress : (next 2).m.core.read .rcx = 1 ∧ (next 2).m.core.read .rdi = 0x4008 ∧
    (next 2).m.core.rip = 0x1000 := by decide +kernel

end Silmaril.Process.LPS.Machines.X86RepStosqControls
