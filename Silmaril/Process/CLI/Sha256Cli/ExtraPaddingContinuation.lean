module

public import Silmaril.Process.CLI.Sha256Cli.ExtraPaddingFrame
public import Silmaril.Process.CLI.Sha256Cli.CompressionCallFrame

/-! # First long-tail compression to the original second-block loop entry

The actual extra-padding CALL/body/RET is followed by the original XOR and
JMP. The resulting PC is 0x400200 with RAX zero, before any second-block zero
store. Arbitrary accumulated H32 is advanced by exactly one compression of
the block actually prepared by the original marker/zero path. The modular
total, source descriptors and symbolic caller stack are retained.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.ExtraPaddingContinuation

open Silmaril.Process.Syscall Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word)
open Silmaril.Crypto.X86.Sha256O2 (stateOf)

/-- Original two-instruction post-extra-padding continuation. -/
def loopCore (c : Core) : Core :=
  { c.write .rax 0 with rip := 0x400200, flags := X86.Ext.logicFlagsN (0 : BitVec 32) }

@[simp] theorem loopCore_registers (c : Core) :
    (loopCore c).read .rax = 0 ∧ (loopCore c).read .rbx = c.read .rbx ∧
      (loopCore c).read .rsp = c.read .rsp := by
  simp [loopCore, X86.State.read, X86.State.write, Machine.RegisterFile.write]

set_option maxRecDepth 10000 in
/-- XOR EAX,EAX and JMP execute after the real extra-padding return. -/
theorem enter_loop (c : Core) (s : Syscall.State)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = CompressionSite.extraPadding.returnAddress) :
    Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ [] ⟨loopCore c, s⟩ := by
  let cleared : Core := { c.write .rax 0 with
    rip := 0x4001fa, flags := X86.Ext.logicFlagsN (0 : BitVec 32) }
  have first : Proc.Step X86Linux.isa Env.linux (⟨c, s⟩ : Output.PS) [] ⟨cleared, s⟩ := by
    apply Output.retire (entry := Binary.i_4001f8) (by simp [Binary.transcript]) intact running
      (by rw [pc]; rfl)
    simp [Entry.denote, X86Linux.execResult, Binary.i_4001f8, X86.Ext.exec,
      X86.Ext.aluStep, X86.Ext.readRM, X86.Ext.writeRM, X86.Ext.Sz.read,
      X86.Ext.Sz.write, X86.Ext.retire, X86.Ext.AluOp.resultN, X86.Ext.AluOp.flagsN,
      cleared, pc, CompressionSite.returnAddress, CompressionSite.address]
    dsimp +instances only [X86.Ext.Sz.bits]
    simp only [BitVec.xor_self, BitVec.setWidth_zero, and_self]
  have second : Proc.Step X86Linux.isa Env.linux (⟨cleared, s⟩ : Output.PS) []
      ⟨loopCore c, s⟩ := by
    apply Output.retire (entry := Binary.i_4001fa) (by simp [Binary.transcript]) intact running rfl
    rfl
  exact .cons first (.single second)

/-- The compressor writes only H32 and its stack/return-slot span. -/
def Changes (top address : Nat) : Prop :=
  (0x401660 ≤ address ∧ address < 0x401680) ∨
    (top - 384 ≤ address ∧ address < top - 32)

/-- A cut before the second block's first zero store. The buffer still holds
exactly the first padded block; its second-block overwrite has not begun. -/
structure Ready (initial : Memory) (stack : Word) (c : Core) (s : Syscall.State)
    (tail stateBytes : List Byte) (total : Word) : Prop where
  long : 56 ≤ tail.length
  room : tail.length < 64
  running : s.exited = none
  pc : c.rip = 0x400200
  index : c.read .rax = 0
  totalRetained : c.read .rbx = total
  rsp : c.read .rsp = stack
  frame : DriverMemory.Frame initial s.memory
  firstBlock : s.memory.readBytes 0x401620 64 = some (PaddingExtra.block tail)
  hash : ∃ bytes, s.memory.readBytes 0x401660 32 = some bytes ∧
    (stateOf bytes).toState = Driver.compressBlock (stateOf stateBytes).toState
      (PaddingExtra.block tail)

set_option maxRecDepth 100000 in
/-- Consume the actual CALL-ready cut, execute one real compression and its
RET, then the real XOR/JMP. No second block, digest or driver progress is assumed. -/
theorem advance {initial : Memory} {top : Nat} {c : Core} {s : Syscall.State}
    {tail stateBytes : List Byte} {total : Word}
    (ready : ExtraPaddingFrame.CallReady initial (BitVec.ofNat 64 (top - 32)) c s
      tail stateBytes total)
    (geometry : CompressionStack.Geometry top) (stack : CompressionStack.Mapping initial top) :
    ∃ (next : Core) (after : Memory),
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ [] ⟨next, { s with memory := after }⟩ ∧
      Memory.WritesWithin s.memory after (Changes top) ∧
      Ready initial (BitVec.ofNat 64 (top - 32)) next { s with memory := after }
        tail stateBytes total := by
  obtain ⟨entryMemory, final, compressed, pushed, _, post, returned, _, entryBlock,
      restored, frame, hash⟩ := CompressionCallFrame.invoke_site .extraPadding c s
    stateBytes (PaddingExtra.block tail) ready.running ready.frame.code ready.pc ready.rsp
      ready.stateArg ready.blockArg ready.state ready.block ready.frame geometry stack
  have savedTotal : final.core.read .rbx = total := by
    simpa [CompressionSite.entryCore, directCallCore, X86.State.read, X86.State.write,
      Machine.RegisterFile.write] using (post.saved .rbx (by decide)).trans ready.totalRetained
  have pushChanges : Memory.WritesWithin s.memory entryMemory (Changes top) :=
    pushed.writesWithin (by
      intro offset bound
      apply Or.inr
      rw [geometry.entry_toNat]
      simp only [Machine.LittleEndian.encodeWords_length, List.length_singleton, Nat.mul_one] at bound
      have := geometry.aboveGlobals
      omega)
  have calleeChanges : Memory.WritesWithin entryMemory final.memory (Changes top) :=
    post.untouched.mono (by
      intro address inside
      rcases inside with state | stack
      · apply Or.inl
        change 0x401660 ≤ address ∧ address < 0x401680 at state
        exact state
      · apply Or.inr
        change (Silmaril.Crypto.X86.Sha256O2.frameRegion
          (CompressionStack.entryStack top) Silmaril.Crypto.X86.Sha256O2.frameSize).Contains address at stack
        simp only [Silmaril.Crypto.X86.Sha256O2.frameRegion,
          Region.Contains, geometry.frame_floor] at stack
        change top - 384 ≤ address ∧ address < top - 384 + 344 at stack
        have := geometry.aboveGlobals
        omega)
  have firstBlock : final.memory.readBytes 0x401620 64 = some (PaddingExtra.block tail) := by
    rw [calleeChanges.readBytes (by
      intro offset bound inside
      rcases inside with state | stack
      · omega
      · have := geometry.aboveGlobals
        omega)]
    exact entryBlock
  have args := loopCore_registers final.core
  refine ⟨loopCore final.core, final.memory, ?_, pushChanges.trans calleeChanges,
    ready.long, ready.room, ready.running, rfl, args.1, args.2.1.trans savedTotal,
    args.2.2.trans restored, frame, firstBlock, hash⟩
  simpa only [List.nil_append] using compressed.append
    (enter_loop final.core { s with memory := final.memory } ready.running frame.code returned)

end Silmaril.Process.CLI.Sha256Cli.ExtraPaddingContinuation
