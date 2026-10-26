module

public import Silmaril.Process.CLI.Sha256Cli.EmptySupport

/-! # The compiled driver's hexadecimal stores

The actual driver stores its low digit before its high digit. This local
instruction theorem exposes their exact two-byte result and memory footprint.
The digit/register and loop-index premises are separate data-flow obligations;
this theorem does not assume that an abstract hex formatter executed.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.Hex

open Silmaril.Process (Byte Memory)
open Silmaril.Process.CLI
open Silmaril.Process.CLI.X86Linux
open Silmaril.Process.Syscall
open Silmaril.X86 (Word)
open Silmaril.X86.Ext (Stored)
open Silmaril.X86.Lift (ix)

private theorem oneByte (byte : Byte) :
    Silmaril.X86.Ext.leBytes (byte.setWidth 64) 1 = [byte] := by
  have all : ∀ b : Byte, Silmaril.X86.Ext.leBytes (b.setWidth 64) 1 = [b] := by decide
  exact all byte

private theorem effective_address (c : Core) (index : Fin 32) (displacement : BitVec 32)
    (rax : c.read .rax = BitVec.ofNat 64 index.val) (next : Word) :
    (Silmaril.X86.Ext.Mem.ofReg .rax (some (ix .rax 0)) displacement).addr c next =
      BitVec.ofNat 64 index.val + BitVec.ofNat 64 index.val + displacement.signExtend 64 := by
  simp [Silmaril.X86.Ext.Mem.addr, Silmaril.X86.Ext.Mem.ofReg,
    Silmaril.X86.Ext.Base.value, Silmaril.X86.Ext.Index.value, ix, rax]

private theorem address_low (index : Fin 32) :
    BitVec.ofNat 64 index.val + BitVec.ofNat 64 index.val +
        (0x4015c1 : BitVec 32).signExtend 64 =
      BitVec.ofNat 64 (0x4015c0 + 2 * index.val + 1) := by
  have all : ∀ i : Fin 32,
      BitVec.ofNat 64 i.val + BitVec.ofNat 64 i.val +
          (0x4015c1 : BitVec 32).signExtend 64 =
        BitVec.ofNat 64 (0x4015c0 + 2 * i.val + 1) := by decide
  exact all index

private theorem address_high (index : Fin 32) :
    BitVec.ofNat 64 index.val + BitVec.ofNat 64 index.val +
        (0x4015c0 : BitVec 32).signExtend 64 =
      BitVec.ofNat 64 (0x4015c0 + 2 * index.val) := by
  have all : ∀ i : Fin 32,
      BitVec.ofNat 64 i.val + BitVec.ofNat 64 i.val +
          (0x4015c0 : BitVec 32).signExtend 64 =
        BitVec.ofNat 64 (0x4015c0 + 2 * i.val) := by decide
  exact all index

set_option maxRecDepth 10000 in
/-- The two transcribed byte stores really write `[high, low]`, in that
order in memory, while emitting no process events. No scratch-register or
whole-driver execution hypothesis is hidden in this local statement. -/
theorem store_pair (c : Core) (s : Syscall.State) (index : Fin 32) (high low : Byte)
    (running : s.exited = none) (pc : c.rip = 0x400259)
    (rax : c.read .rax = BitVec.ofNat 64 index.val)
    (rdx : (c.read .rdx).setWidth 8 = low) (rcx : (c.read .rcx).setWidth 8 = high)
    (firstCode : s.memory.fetchBytes 0x400259 Binary.i_400259.bytes.length =
      some Binary.i_400259.bytes)
    (secondCode : s.memory.fetchBytes 0x400260 Binary.i_400260.bytes.length =
      some Binary.i_400260.bytes)
    (writable : s.memory.Permitted .write (0x4015c0 + 2 * index.val) 2)
    (readable : s.memory.Permitted .read (0x4015c0 + 2 * index.val) 2) :
    ∃ after : Memory,
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ []
        ⟨{ c with rip := 0x400267 }, { s with memory := after }⟩ ∧
      after.readBytes (0x4015c0 + 2 * index.val) 2 = some [high, low] ∧
      Memory.WritesWithin s.memory after
        (fun a => 0x4015c0 + 2 * index.val ≤ a ∧ a < 0x4015c0 + 2 * index.val + 2) := by
  let address := 0x4015c0 + 2 * index.val
  have bound : index.val < 32 := index.isLt
  have addressNat : (BitVec.ofNat 64 address).toNat = address := by
    exact Nat.mod_eq_of_lt (by dsimp [address]; omega)
  have lowAddressNat : (BitVec.ofNat 64 (address + 1)).toNat = address + 1 := by
    exact Nat.mod_eq_of_lt (by dsimp [address]; omega)
  have lowWrite : s.memory.Permitted .write (address + 1) 1 :=
    Silmaril.X86.Ext.Memory.Permitted.sub writable (by decide) (by omega) (by omega)
  have lowWrite' : s.memory.Permitted .write
      (BitVec.ofNat 64 (address + 1)).toNat 1 := by rw [lowAddressNat]; exact lowWrite
  obtain ⟨middle, lowStored, lowFrame⟩ := Silmaril.X86.Ext.storeN_isSome
    (v := low.setWidth 64) lowWrite'
  rw [lowAddressNat, oneByte] at lowFrame
  have firstEffect : Binary.i_400259.denote c s.memory =
      .retired { c with rip := 0x400260 } middle := by
    have shape : Binary.i_400259.denote c s.memory =
      X86Linux.execResult (Silmaril.X86.Ext.retire (c.rip + 7)
      ((Silmaril.X86.Ext.storeN s.memory
        ((Silmaril.X86.Ext.Mem.ofReg .rax (some (ix .rax 0)) 0x4015c1).addr c (c.rip + 7))
        1 (((c.read .rdx).setWidth 8).setWidth 64)).map fun a => (c, a))) := rfl
    have addressEq := (effective_address c index 0x4015c1 rax (c.rip + 7)).trans
      (address_low index)
    have actualStored : Silmaril.X86.Ext.storeN s.memory
        ((Silmaril.X86.Ext.Mem.ofReg .rax (some (ix .rax 0)) 0x4015c1).addr c (c.rip + 7))
        1 (((c.read .rdx).setWidth 8).setWidth 64) = some middle := by
      simpa only [addressEq, rdx] using lowStored
    have mapped := congrArg (fun result : Option Memory =>
      X86Linux.execResult (Silmaril.X86.Ext.retire (c.rip + 7)
        (result.map fun a => (c, a)))) actualStored
    refine shape.trans (mapped.trans ?_)
    rw [pc]
    rfl
  have firstStep : Proc.Step X86Linux.isa Env.linux ⟨c, s⟩ []
      ⟨{ c with rip := 0x400260 }, { s with memory := middle }⟩ :=
    .retire running
      ((step_of_entry Binary.ok_400259.1 (by simp [pc, Binary.i_400259]) firstCode).trans firstEffect).symm
  have highWrite : middle.Permitted .write address 1 :=
    lowFrame.permitted (Silmaril.X86.Ext.Memory.Permitted.sub writable
      (by decide) (by omega) (by omega))
  have highWrite' : middle.Permitted .write (BitVec.ofNat 64 address).toNat 1 :=
    by rw [addressNat]; exact highWrite
  obtain ⟨after, highStored, highFrame⟩ := Silmaril.X86.Ext.storeN_isSome
    (v := high.setWidth 64) highWrite'
  rw [addressNat, oneByte] at highFrame
  have secondFetch : middle.fetchBytes 0x400260 Binary.i_400260.bytes.length =
      some Binary.i_400260.bytes := by
    exact (lowFrame.readWith_disjoint .execute 0x400260 Binary.i_400260.bytes.length
      (Or.inl (by dsimp [address]; simp [Binary.i_400260]; omega))).trans secondCode
  have secondEffect : Binary.i_400260.denote { c with rip := 0x400260 } middle =
      .retired { c with rip := 0x400267 } after := by
    have shape : Binary.i_400260.denote { c with rip := 0x400260 } middle =
      X86Linux.execResult (Silmaril.X86.Ext.retire 0x400267
      (Option.map (fun a => (({ c with rip := 0x400260 } : Core), a))
        (Silmaril.X86.Ext.storeN middle
          ((Silmaril.X86.Ext.Mem.ofReg .rax (some (ix .rax 0)) 0x4015c0).addr
            ({ c with rip := 0x400260 } : Core) 0x400267)
          1 (((c.read .rcx).setWidth 8).setWidth 64)))) := rfl
    have addressEq := effective_address ({ c with rip := 0x400260 } : Core) index
      0x4015c0 rax (0x400267 : Word)
    rw [address_high] at addressEq
    have actualStored : Silmaril.X86.Ext.storeN middle
        ((Silmaril.X86.Ext.Mem.ofReg .rax (some (ix .rax 0)) 0x4015c0).addr
          ({ c with rip := 0x400260 } : Core) 0x400267)
        1 (((c.read .rcx).setWidth 8).setWidth 64) = some after := by
      simpa only [addressEq, rcx] using highStored
    have mapped := congrArg (fun result : Option Memory =>
      X86Linux.execResult (Silmaril.X86.Ext.retire 0x400267
        (result.map fun a => (({ c with rip := 0x400260 } : Core), a)))) actualStored
    exact shape.trans mapped
  have secondStep : Proc.Step X86Linux.isa Env.linux
      ⟨{ c with rip := 0x400260 }, { s with memory := middle }⟩ []
      ⟨{ c with rip := 0x400267 }, { s with memory := after }⟩ :=
    .retire running
      ((step_of_entry Binary.ok_400260.1 rfl secondFetch).trans secondEffect).symm
  have highReadable : middle.Permitted .read address 1 :=
    lowFrame.permitted (Silmaril.X86.Ext.Memory.Permitted.sub readable
      (by decide) (by omega) (by omega))
  have highRead : after.readBytes address 1 = some [high] :=
    highFrame.readWith_self (access := .read) highReadable
  have lowRead : after.readBytes (address + 1) 1 = some [low] := by
    have lowReadable : s.memory.Permitted .read (address + 1) 1 :=
      Silmaril.X86.Ext.Memory.Permitted.sub readable (by decide) (by omega) (by omega)
    exact (highFrame.readWith_disjoint .read (address + 1) 1 (Or.inr (by simp))).trans
      (lowFrame.readWith_self (access := .read) lowReadable)
  refine ⟨after, .cons firstStep (.single secondStep), ?_, ?_⟩
  · have joined := Memory.readBytes_append highRead lowRead
    simpa using joined
  · exact (lowFrame.writesWithin (by intro a ha; simp only [List.length_singleton] at ha; omega)).trans
      (highFrame.writesWithin (by intro a ha; simp only [List.length_singleton] at ha; omega))

end Silmaril.Process.CLI.Sha256Cli.Hex
