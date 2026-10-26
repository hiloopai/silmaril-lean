module

public import Silmaril.Process.CLI.Sha256Cli.CompressionSite
public import Silmaril.Process.CLI.X86Linux.Call
public import Silmaril.Crypto.X86.Sha256O2.Reference

/-! # Dynamic source and stack for the actual compression CALL and RET

Every original SysVEntry clause is derived from the source frame, actual buffer
reads, and explicit stack geometry/mapping. The existing callee liveness,
reference and silent process bridges are reused unchanged.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.CompressionCallFrame

open Silmaril.Process.Syscall Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word MState sysv64)
open Silmaril.Crypto Silmaril.Crypto.X86.Sha256O2

abbrev returnAddress : Word := Compress.returnAddress
def entryCore (c : Core) : Core := directCallCore c 0xb2

set_option maxRecDepth 100000 in
/-- Execute any of the three actual driver CALL sites and the checked compression body/RET
for arbitrary actual state/block bytes. Every SysVEntry clause is derived.
The returned reference equation is one compression step, not a hash theorem. -/
theorem invoke_site (site : CompressionSite) {initial : Memory} {top : Nat} (c : Core) (s : Syscall.State)
    (stateBytes blockBytes : List Byte)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = site.address) (rsp : c.read .rsp = BitVec.ofNat 64 (top - 32))
    (argState : c.read .rdi = 0x401660) (argBlock : c.read .rsi = 0x401620)
    (stateRead : s.memory.readBytes 0x401660 32 = some stateBytes)
    (blockRead : s.memory.readBytes 0x401620 64 = some blockBytes)
    (frame : DriverMemory.Frame initial s.memory)
    (geometry : CompressionStack.Geometry top) (stack : CompressionStack.Mapping initial top) :
    ∃ (entryMemory : Memory) (final : MState),
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ []
        ⟨final.core, { s with memory := final.memory }⟩ ∧
      X86.Ext.Stored s.memory entryMemory (CompressionStack.entryStack top).toNat
        (Machine.LittleEndian.encodeWords [(site.returnAddress)]) ∧
      SysVEntry (Compress.layout (site.returnAddress)) 0x401660 0x401620 (CompressionStack.entryStack top) frameSize
        ⟨site.entryCore c, entryMemory⟩ ∧
      Post (Compress.layout (site.returnAddress)) 0x401660 0x401620 (CompressionStack.entryStack top) frameSize
        ⟨site.entryCore c, entryMemory⟩ final ∧
      final.core.rip = (site.returnAddress) ∧
      entryMemory.readBytes 0x401660 32 = some stateBytes ∧
      entryMemory.readBytes 0x401620 64 = some blockBytes ∧
      final.core.read .rsp = BitVec.ofNat 64 (top - 32) ∧
      DriverMemory.Frame initial final.memory ∧
      ∃ bytes, final.memory.readBytes 0x401660 32 = some bytes ∧
        (stateOf bytes).toState = SHA256.processBlock (stateOf stateBytes).toState
          (SHA256.parseBlock (blockBytes.map UInt8.ofBitVec)) := by
  have address : c.read .rsp - (8 : Word) = CompressionStack.entryStack top := by
    rw [rsp]
    exact geometry.call_sub
  have returnEq : c.rip + (5 : Word) = (site.returnAddress) := by rw [pc]; rfl
  have callFetch := site.fetch intact pc
  have currentStack := stack.transport frame.changes
  have pushPermission : s.memory.Permitted .write (c.read .rsp - (8 : Word)).toNat 8 := by
    erw [address]
    exact (currentStack.return_slot geometry).2
  obtain ⟨entryMemory, pushed, _, stored⟩ := direct_call_entry
    (initial := ⟨c, s.memory⟩) (rel := site.displacement) callFetch pushPermission
  have normalizedStored : X86.Ext.Stored s.memory entryMemory (CompressionStack.entryStack top).toNat
      (Machine.LittleEndian.encodeWords [(site.returnAddress)]) := by
    change X86.Ext.Stored s.memory entryMemory (c.read .rsp - (8 : Word)).toNat
      (Machine.LittleEndian.encodeWords [c.rip + (5 : Word)]) at stored
    erw [address, returnEq] at stored
    exact stored
  obtain ⟨code, table⟩ := frame.constants (site.returnAddress)
  have stackAbove : 0x401680 ≤ (CompressionStack.entryStack top).toNat := by
    rw [geometry.entry_toNat]
    have := geometry.aboveGlobals
    omega
  have code' : entryMemory.fetchBytes 0x4002e0 size =
      some (Silmaril.Crypto.X86.Sha256O2.image 0x4002e0 0x4004c0) :=
    (normalizedStored.readWith_disjoint .execute 0x4002e0 size
      (Or.inl (by dsimp [size]; omega))).trans code
  have table' : entryMemory.readBytes 0x4004c0 kSize = some kBytes :=
    (normalizedStored.readWith_disjoint .read 0x4004c0 kSize
      (Or.inl (by dsimp [kSize]; omega))).trans table
  have state' : entryMemory.readBytes 0x401660 32 = some stateBytes :=
    (normalizedStored.readWith_disjoint .read 0x401660 32 (Or.inl (by omega))).trans stateRead
  have block' : entryMemory.readBytes 0x401620 64 = some blockBytes :=
    (normalizedStored.readWith_disjoint .read 0x401620 64 (Or.inl (by omega))).trans blockRead
  have writable : entryMemory.Permitted .write 0x401660 32 :=
    normalizedStored.permitted (frame.bss_permitted .write rfl _ _ (by decide) (by decide))
  have entry : SysVEntry (Compress.layout (site.returnAddress)) 0x401660 0x401620
      (CompressionStack.entryStack top) frameSize
      ⟨site.entryCore c, entryMemory⟩ := by
    refine ⟨?_, code', Compress.layout_relocFits _, ?_, ?_, ?_, ?_,
      geometry.entry_aligned, ?_, ⟨_, state'⟩, writable,
      ⟨_, block'⟩, ?_, geometry.frame_fits, geometry.noWrap (site.returnAddress),
      geometry.disjoint (site.returnAddress), by decide⟩
    · change c.rip + 5 + site.displacement.signExtend 64 = 0x4002e0
      rw [pc]
      exact site.target
    · exact table'
    · exact (directCallCore_read c site.displacement .rdi (by decide)).trans argState
    · exact (directCallCore_read c site.displacement .rsi (by decide)).trans argBlock
    · exact (directCallCore_rsp c site.displacement).trans address
    · change entryMemory.readBytes (CompressionStack.entryStack top).toNat 8 =
        some (X86.Ext.leBytes site.returnAddress 8)
      rw [X86.Ext.leBytes_eight]
      have readable : s.memory.Permitted .read (CompressionStack.entryStack top).toNat
          (Machine.LittleEndian.encodeWords [site.returnAddress]).length := by
        simpa only [Machine.LittleEndian.encodeWords_length, List.length_singleton, Nat.mul_one]
          using (currentStack.return_slot geometry).1
      simpa only [Memory.readBytes, Machine.LittleEndian.encodeWords_length,
        List.length_singleton, Nat.mul_one] using normalizedStored.readWith_self readable
    · exact ⟨normalizedStored.permitted (currentStack.frame geometry).1,
        normalizedStored.permitted (currentStack.frame geometry).2⟩
  obtain ⟨final, returned⟩ := sha256_compress_O2_live (Compress.layout (site.returnAddress))
    0x401660 0x401620 (CompressionStack.entryStack top) ⟨site.entryCore c, entryMemory⟩ entry
  have post := Compress.compress_contract (site.returnAddress) 0x401660 0x401620
    (CompressionStack.entryStack top) ⟨site.entryCore c, entryMemory⟩ final entry returned
  have returned' : X86.Ext.Returns (c.rip + (5 : Word))
      (directCallState ⟨c, s.memory⟩ site.displacement entryMemory) final := by
    erw [returnEq]
    exact returned
  have live := runs_of_direct_call_returns Env.linux_memoryLens
    (initial := ⟨c, s.memory⟩) running rfl callFetch pushed returned'
  have reference := post.compressed_reference state' block' (Memory.readWith_length blockRead)
  have restored : final.core.read .rsp = BitVec.ofNat 64 (top - 32) := by
    rw [post.rsp, ← geometry.call_sub]
    exact BitVec.sub_add_cancel _ _
  have pushedFrame : Memory.WritesWithin s.memory entryMemory DriverMemory.Above :=
    normalizedStored.writesWithin (by
      intro offset bound
      dsimp [DriverMemory.Above]
      omega)
  have calleeFrame : Memory.WritesWithin entryMemory final.memory DriverMemory.Above :=
    post.untouched.mono (by
      intro address inside
      rcases inside with state | stack
      · dsimp [Footprint, stateRegion, Region.Contains] at state
        dsimp [DriverMemory.Above]
        omega
      · change (frameRegion (CompressionStack.entryStack top) frameSize).Contains address at stack
        simp only [frameRegion, Region.Contains, geometry.frame_floor] at stack
        dsimp [DriverMemory.Above]
        have := geometry.aboveGlobals
        omega)
  exact ⟨entryMemory, final, by simpa only [Env.linux] using live, normalizedStored, entry, post,
    ext_returns_target returned, state', block', restored,
    frame.trans (pushedFrame.trans calleeFrame), reference⟩

/-- Source-compatible final-block specialization of the shared actual-site proof. -/
theorem invoke {initial : Memory} {top : Nat} (c : Core) (s : Syscall.State)
    (stateBytes blockBytes : List Byte)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x400229) (rsp : c.read .rsp = BitVec.ofNat 64 (top - 32))
    (argState : c.read .rdi = 0x401660) (argBlock : c.read .rsi = 0x401620)
    (stateRead : s.memory.readBytes 0x401660 32 = some stateBytes)
    (blockRead : s.memory.readBytes 0x401620 64 = some blockBytes)
    (frame : DriverMemory.Frame initial s.memory)
    (geometry : CompressionStack.Geometry top) (stack : CompressionStack.Mapping initial top) :
    ∃ (entryMemory : Memory) (final : MState),
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ []
        ⟨final.core, { s with memory := final.memory }⟩ ∧
      X86.Ext.Stored s.memory entryMemory (CompressionStack.entryStack top).toNat
        (Machine.LittleEndian.encodeWords [returnAddress]) ∧
      SysVEntry (Compress.layout returnAddress) 0x401660 0x401620 (CompressionStack.entryStack top) frameSize
        ⟨entryCore c, entryMemory⟩ ∧
      Post (Compress.layout returnAddress) 0x401660 0x401620 (CompressionStack.entryStack top) frameSize
        ⟨entryCore c, entryMemory⟩ final ∧
      final.core.rip = returnAddress ∧
      entryMemory.readBytes 0x401660 32 = some stateBytes ∧
      entryMemory.readBytes 0x401620 64 = some blockBytes ∧
      final.core.read .rsp = BitVec.ofNat 64 (top - 32) ∧
      DriverMemory.Frame initial final.memory ∧
      ∃ bytes, final.memory.readBytes 0x401660 32 = some bytes ∧
        (stateOf bytes).toState = SHA256.processBlock (stateOf stateBytes).toState
          (SHA256.parseBlock (blockBytes.map UInt8.ofBitVec)) :=
  invoke_site .finalBlock c s stateBytes blockBytes running intact pc rsp argState argBlock
    stateRead blockRead frame geometry stack

end Silmaril.Process.CLI.Sha256Cli.CompressionCallFrame
