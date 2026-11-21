module

import Silmaril.Elf.Corpus.SqliteMutex.Thms
public meta import Silmaril.Elf.Corpus.SqliteMutex.Defs
public meta import Silmaril.Machine.SqliteMutex.Defs

namespace Silmaril.Elf.Corpus.SqliteMutex

open Silmaril.X86 (MState Word)
open Silmaril.X86.Ext (loadN undefinedFlags)
open Silmaril.X86.Ext.Wire (Platform)
open Silmaril.Process (Memory Region Permissions)
open Silmaril.Machine SqliteMutex Behaviour Observable LittleEndian

private def caller : Word := 0x300000
private def target : Word := 0x400000
private def stack : Word := 0x200008
private def mutex : Handle := 0x500000
private def platform : Platform := ⟨fun _ _ => ⟨0, 0, 0, 0⟩⟩

private def fixtureMemory (installed : Bool) : Memory :=
  let code := region.load
  let stackRegion : Region := ⟨stack.toNat, 8, ⟨true, true, false⟩⟩
  let slotRegion : Region := ⟨slot.toNat, 8, ⟨true, false, false⟩⟩
  let backing := Memory.install code.bytes stack.toNat (encodeWords [caller])
  if installed then
    ⟨stackRegion :: slotRegion :: code.regions, Memory.install backing slot.toNat (encodeWords [target])⟩
  else ⟨stackRegion :: code.regions, backing⟩

private def fixture (argument : Handle) (installed : Bool) : MState :=
  ⟨⟨fun reg => if reg = .rsp then stack else if reg = .rdi then argument else 0,
    0xff70, undefinedFlags, 0⟩, fixtureMemory installed⟩

private def owned : Context := ⟨(· = mutex), (· = mutex), True⟩
private def unowned : Context := { owned with ownedByCaller := fun _ => False }

private theorem fixture_code : region.LoadedIn (fixtureMemory true) := by
  intro offset length bound
  rw [← region.loadedIn_load (by decide) offset length bound]
  have fits : offset + length ≤ 17 := bound
  have permissions (address : Nat) :
      (fixtureMemory true).permits .execute address = region.load.permits .execute address := by
    simp [fixtureMemory, Memory.permits, Permissions.allows]
  have checkSpan : (fixtureMemory true).checkSpan .execute (region.base + offset) length =
      region.load.checkSpan .execute (region.base + offset) length := by
    simp [Memory.checkSpan, permissions]
  simp only [Memory.fetchBytes, Memory.readWith, checkSpan]
  congr 1
  apply Memory.readBacking_congr
  intro index within
  change (Memory.install (Memory.install region.load.bytes stack.toNat (encodeWords [caller]))
    slot.toNat (encodeWords [target])).get? (region.base + offset + index) = _
  have address (base : Nat) (large : 0xff81 ≤ base) : region.base + offset + index < base := by
    change 0xff70 + offset + index < base
    omega
  rw [Memory.install_outside _ _ _ _ (.inl (address slot.toNat (by decide))),
    Memory.install_outside _ _ _ _ (.inl (address stack.toNat (by decide)))]

private theorem fixture_stack : (fixtureMemory true).readBytes stack.toNat 8 =
    some (encodeWords [caller]) := by
  rw [Memory.readBytes, Memory.readWith, ite_eq_left (by decide +kernel)]
  change Memory.readBacking (fixtureMemory true).bytes stack.toNat (encodeWords [caller]).length = _
  apply Memory.readBacking_eq
  intro index bound
  have aboveSlot : slot.toNat + (encodeWords [target]).length ≤ stack.toNat + index := by
    have : slot.toNat + (encodeWords [target]).length ≤ stack.toNat := by decide
    omega
  change (Memory.install (Memory.install region.load.bytes stack.toNat (encodeWords [caller]))
    slot.toNat (encodeWords [target])).get? (stack.toNat + index) = _
  rw [Memory.install_outside _ _ _ _ (.inr aboveSlot)]
  exact Memory.install_get _ _ _ _ bound

private theorem fixture_slot : loadN (fixtureMemory true) slot 8 = some target := by
  have loaded : (fixtureMemory true).readBytes slot.toNat 8 = some (encodeWords [target]) := by
    rw [Memory.readBytes, Memory.readWith, ite_eq_left (by decide +kernel)]
    change Memory.readBacking (fixtureMemory true).bytes slot.toNat (encodeWords [target]).length = _
    apply Memory.readBacking_eq
    exact Memory.install_get _ _ _
  rw [loadN, loaded]
  decide +kernel

private theorem fixture_entry : Entry (fixture mutex true) caller target :=
  ⟨rfl, fixture_code, fixture_stack, fun _ => ⟨by decide, fixture_slot⟩⟩

private theorem fixture_safe : Safe ((contract owned).spec ((fixture mutex true).core.read .rdi)) :=
  (safe_iff_admitted _ _).mpr (.inr ⟨rfl, rfl, trivial⟩)

example : observe (run platform caller 3 (fixture mutex true)) ∈ (contract owned).spec mutex :=
  sound (env := owned) fixture_entry fixture_safe

#guard observe (run platform caller 3 (fixture mutex true)) == ⟨[.leave mutex], .returned .handlerEntry⟩

#guard observe (run platform caller 3 (fixture 0 false)) == ⟨[], .returned .callerReturn⟩

#guard observe (run platform caller 3 (fixture mutex false)) == ⟨[], .faulted .data⟩

#guard observe (run platform caller 2 (fixture mutex true)) == ⟨[], .faulted .validation⟩

example : close .forbidden ((contract unowned).spec mutex) = Set.univ :=
  ub_is_top (fun admitted => admitted.elim (by decide) (·.2.1))

end Silmaril.Elf.Corpus.SqliteMutex
