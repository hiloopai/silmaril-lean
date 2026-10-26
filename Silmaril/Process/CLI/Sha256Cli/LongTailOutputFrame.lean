module

public import Silmaril.Process.CLI.Sha256Cli.LongTailPaddingReference
public import Silmaril.Process.CLI.Sha256Cli.HexOutputFrame

/-! # Actual long-tail final compression and canonical output setup

The second actual CALL/body/RET advances the accumulated H32 by one more
compression. Canonical formatting additionally requires the caller's prefix
fold and whole-message modular total. Earlier startup/read/EOF reachability
is an explicit separate obligation; no digest or compressor entry is installed.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.LongTailOutputFrame

open Silmaril.Process.Syscall Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word)
open Silmaril.Crypto.X86.Sha256O2 (stateOf)

/-- The returned H32 is observed in actual successor memory. The original total
is ghosted because the real length serialization has already destroyed RBX. -/
structure Returned (initial : Memory) (stack : Word) (c : Core) (s : Syscall.State)
    (tail priorH : List Byte) (total : Word) : Prop where
  long : 56 ≤ tail.length
  room : tail.length < 64
  running : s.exited = none
  pc : c.rip = CompressionSite.finalBlock.returnAddress
  rsp : c.read .rsp = stack
  serialized : c.read .rbx = LengthStore.swapped total
  frame : DriverMemory.Frame initial s.memory
  hash : ∃ bytes, s.memory.readBytes 0x401660 32 = some bytes ∧
    (stateOf bytes).toState = Driver.compressBlock
      (Driver.compressBlock (stateOf priorH).toState (PaddingExtra.block tail))
      (SecondPaddingFrame.block total)

set_option maxRecDepth 100000 in
/-- Execute the real final CALL, checked body and RET. The accumulated state is
arbitrary and the only writes are H32 and the actual call/callee stack span. -/
theorem advance {initial : Memory} {top : Nat} {c : Core} {s : Syscall.State}
    {tail priorH : List Byte} {total : Word}
    (ready : SecondPaddingFrame.CallReady initial (BitVec.ofNat 64 (top - 32)) c s
      tail priorH total)
    (geometry : CompressionStack.Geometry top) (stack : CompressionStack.Mapping initial top) :
    ∃ (next : Core) (after : Memory),
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ [] ⟨next, { s with memory := after }⟩ ∧
      Memory.WritesWithin s.memory after (ExtraPaddingContinuation.Changes top) ∧
      Returned initial (BitVec.ofNat 64 (top - 32)) next { s with memory := after }
        tail priorH total := by
  obtain ⟨stateBytes, stateRead, priorHash⟩ := ready.hash
  obtain ⟨entryMemory, final, compressed, pushed, _, post, returned, _, _,
      restored, frame, bytes, state, hash⟩ := CompressionCallFrame.invoke_site .finalBlock c s
    stateBytes (SecondPaddingFrame.block total) ready.running ready.frame.code ready.pc ready.rsp
      ready.stateArg ready.blockArg stateRead ready.block ready.frame geometry stack
  have serialized : final.core.read .rbx = LengthStore.swapped total := by
    simpa [CompressionSite.entryCore, directCallCore, X86.State.read, X86.State.write,
      Machine.RegisterFile.write] using (post.saved .rbx (by decide)).trans ready.serialized
  have pushChanges : Memory.WritesWithin s.memory entryMemory (ExtraPaddingContinuation.Changes top) :=
    pushed.writesWithin (by
      intro offset bound
      apply Or.inr
      rw [geometry.entry_toNat]
      simp only [Machine.LittleEndian.encodeWords_length, List.length_singleton, Nat.mul_one] at bound
      have := geometry.aboveGlobals
      omega)
  have calleeChanges : Memory.WritesWithin entryMemory final.memory
      (ExtraPaddingContinuation.Changes top) := post.untouched.mono (by
    intro address inside
    rcases inside with state | stack
    · apply Or.inl
      exact state
    · apply Or.inr
      change (Silmaril.Crypto.X86.Sha256O2.frameRegion
        (CompressionStack.entryStack top) Silmaril.Crypto.X86.Sha256O2.frameSize).Contains address at stack
      simp only [Silmaril.Crypto.X86.Sha256O2.frameRegion, Region.Contains, geometry.frame_floor] at stack
      change top - 384 ≤ address ∧ address < top - 384 + 344 at stack
      have := geometry.aboveGlobals
      omega)
  change (stateOf bytes).toState = Driver.compressBlock (stateOf stateBytes).toState
    (SecondPaddingFrame.block total) at hash
  rw [priorHash] at hash
  exact ⟨final.core, final.memory, compressed, pushChanges.trans calleeChanges,
    ready.long, ready.room, ready.running, returned, restored, serialized, frame,
    bytes, state, hash⟩

/-- Canonical output requires the actual accumulated-state fold and total;
neither follows merely from reaching the padding cut. All formatting and the
newline store execute, ending at the original write request. -/
theorem Returned.canonical_output {initial : Memory} {stack : Word} {c : Core} {s : Syscall.State}
    {tail priorH : List Byte} {total : Word}
    (ready : Returned initial stack c s tail priorH total)
    (prefixBlocks : List (List Byte)) (full : ∀ block ∈ prefixBlocks, block.length = 64)
    (hash : (stateOf priorH).toState =
      prefixBlocks.foldl Driver.compressBlock Silmaril.Crypto.SHA256.H0)
    (count : total = BitVec.ofNat 64 (prefixBlocks.flatten ++ tail).length) :
    ∃ (outCore : Core) (memory : Memory),
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ []
        ⟨outCore, { s with memory := memory }⟩ ∧
      HexOutputFrame.Ready initial outCore { s with memory := memory }
        (prefixBlocks.flatten ++ tail) := by
  obtain ⟨bytes, observed, compression⟩ := ready.hash
  rw [hash, count] at compression
  have value := compression.trans
    (LongTailPaddingReference.fold_long prefixBlocks tail full ready.long ready.room)
  exact HexOutputFrame.prepare c s bytes (prefixBlocks.flatten ++ tail)
    ready.running ready.frame ready.pc observed value

/-- Final CALL through output setup at an established second-block cut.
No successful write, syscall progress or earlier read run is assumed. -/
theorem prepare {initial : Memory} {top : Nat} {c : Core} {s : Syscall.State}
    {tail priorH : List Byte} {total : Word}
    (ready : SecondPaddingFrame.CallReady initial (BitVec.ofNat 64 (top - 32)) c s
      tail priorH total)
    (prefixBlocks : List (List Byte)) (full : ∀ block ∈ prefixBlocks, block.length = 64)
    (hash : (stateOf priorH).toState =
      prefixBlocks.foldl Driver.compressBlock Silmaril.Crypto.SHA256.H0)
    (count : total = BitVec.ofNat 64 (prefixBlocks.flatten ++ tail).length)
    (geometry : CompressionStack.Geometry top) (stack : CompressionStack.Mapping initial top) :
    ∃ (outCore : Core) (memory : Memory),
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ []
        ⟨outCore, { s with memory := memory }⟩ ∧
      HexOutputFrame.Ready initial outCore { s with memory := memory }
        (prefixBlocks.flatten ++ tail) := by
  obtain ⟨next, middle, compressed, _, returned⟩ := advance ready geometry stack
  obtain ⟨outCore, memory, formatted, answer⟩ := returned.canonical_output prefixBlocks full hash count
  exact ⟨outCore, memory, by simpa only [List.nil_append] using compressed.append formatted, answer⟩

end Silmaril.Process.CLI.Sha256Cli.LongTailOutputFrame
