module

public import Silmaril.Process.CLI.Sha256Cli.ExtraPaddingContinuation
public import Silmaril.Process.CLI.Sha256Cli.LengthStore

/-! # The original long-tail second-block preparation

Starting at the real post-extra-compression loop entry with RAX zero, the
first ADD/store/CMP/JNE writes byte zero. The existing positive-count loop
then supplies the remaining 55 zeros, and the existing modular length store
reaches the actual final compression CALL. H32 remains the observed result
of the first compression. No final compression, digest or output is assumed.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.SecondPaddingFrame

open Silmaril.Process.Syscall Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word)
open Silmaril.X86.Ext (Stored)
open Silmaril.Crypto.X86.Sha256O2 (stateOf)
open Padding (blockAddress)

/-- After the first second-block zero store the loop count is exactly one. -/
def firstCore (c : Core) : Core :=
  { c.write .rax 1 with
    rip := 0x400200, flags := X86.Ext.subFlagsN (1 : Word) 56 }

set_option maxRecDepth 10000 in
/-- The actual first loop iteration, absent from the positive-count helper,
writes the buffer's first byte and branches back with RAX one. -/
theorem zero_first (c : Core) (s : Syscall.State)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x400200) (index : c.read .rax = 0)
    (writable : s.memory.Permitted .write blockAddress 1) :
    ∃ after : Memory,
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ []
        ⟨firstCore c, { s with memory := after }⟩ ∧
      Stored s.memory after blockAddress [0] ∧ Output.Intact after := by
  let added : Core := { c.write .rax 1 with
    rip := 0x400204, flags := X86.Ext.addFlagsN (0 : Word) 1 }
  have first : Proc.Step X86Linux.isa Env.linux (⟨c, s⟩ : Output.PS) [] ⟨added, s⟩ := by
    apply Output.retire (entry := Binary.i_400200) (by simp [Binary.transcript]) intact running
      (by simp [pc, Binary.i_400200])
    simp [Entry.denote, X86Linux.execResult, Binary.i_400200, X86.Ext.exec,
      X86.Ext.aluStep, X86.Ext.readRM, X86.Ext.writeRM, X86.Ext.Sz.read,
      X86.Ext.Sz.write, X86.Ext.retire, X86.Ext.AluOp.resultN, X86.Ext.AluOp.flagsN,
      added, pc, index, X86.State.write]
  obtain ⟨after, written, stored⟩ := X86.Ext.storeN_isSome
    (address := (0x401620 : Word)) (v := (0 : Word)) writable
  have address : (X86.Ext.Mem.ofReg .rax none 0x40161f).addr added 0x40020b =
      (0x401620 : Word) := by
    simp [X86.Ext.Mem.addr, X86.Ext.Mem.ofReg, X86.Ext.Base.value,
      added, X86.State.read, X86.State.write]
  have storeEffect : Binary.i_400204.denote added s.memory =
      .retired { added with rip := 0x40020b } after := by
    change X86Linux.execResult (X86.Ext.retire 0x40020b
      ((X86.Ext.storeN s.memory
        ((X86.Ext.Mem.ofReg .rax none 0x40161f).addr added 0x40020b)
        1 ((0 : BitVec 8).setWidth 64)).map fun a => (added, a))) = _
    rw [address, show (0 : BitVec 8).setWidth 64 = (0 : Word) from rfl, written]
    rfl
  have second : Proc.Step X86Linux.isa Env.linux (⟨added, s⟩ : Output.PS) []
      ⟨{ added with rip := 0x40020b }, { s with memory := after }⟩ :=
    .retire running ((step_of_entry Binary.ok_400204.1 rfl
      (intact _ (by simp [Binary.transcript]))).trans storeEffect).symm
  have bytes : X86.Ext.leBytes (0 : Word) 1 = [0] := by decide
  rw [bytes] at stored
  have code : Output.Intact after := Output.intact_of_store intact stored (by decide)
  let compared : Core := { added with
    rip := 0x40020f, flags := X86.Ext.subFlagsN (1 : Word) 56 }
  have third : Proc.Step X86Linux.isa Env.linux
      (⟨{ added with rip := 0x40020b }, { s with memory := after }⟩ : Output.PS) []
        ⟨compared, { s with memory := after }⟩ := by
    apply Output.retire (entry := Binary.i_40020b) (s := { s with memory := after })
      (by simp [Binary.transcript]) code running rfl
    simp [Entry.denote, X86Linux.execResult, Binary.i_40020b, X86.Ext.exec,
      X86.Ext.aluStep, X86.Ext.readRM, X86.Ext.Sz.read, X86.Ext.retire,
      X86.Ext.AluOp.flagsN, compared, added, X86.State.read, X86.State.write]
  have fourth : Proc.Step X86Linux.isa Env.linux
      (⟨compared, { s with memory := after }⟩ : Output.PS) []
        ⟨firstCore c, { s with memory := after }⟩ := by
    apply Output.retire (entry := Binary.i_40020f) (s := { s with memory := after })
      (by simp [Binary.transcript]) code running rfl
    have taken : X86.Ext.Cond.eval (X86.Ext.subFlagsN (1 : Word) 56) .ne = some true := by decide
    simp [Entry.denote, X86Linux.execResult, Binary.i_40020f, X86.Ext.exec,
      compared, added, firstCore, X86.State.write]
    erw [taken]
  exact ⟨after, .cons first (.cons second (.cons third (.single fourth))), stored, code⟩

/-- Reuse the real positive-count loop after its distinct first iteration.
All 56 prefix zeros come from actual stores; no buffer bytes are assumed. -/
theorem zero_prefix (c : Core) (s : Syscall.State)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x400200) (index : c.read .rax = 0)
    (writable : s.memory.Permitted .write blockAddress 64)
    (readable : s.memory.Permitted .read blockAddress 64) :
    ∃ after : Memory,
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ []
        ⟨Padding.zeroFinished c, { s with memory := after }⟩ ∧
      after.readBytes blockAddress 56 = some (List.replicate 56 0) ∧
      Memory.WritesWithin s.memory after
        (fun address => blockAddress ≤ address ∧ address < blockAddress + 56) ∧
      Output.Intact after := by
  obtain ⟨middle, first, stored, code⟩ := zero_first c s running intact pc index
    (X86.Ext.Memory.Permitted.sub writable (by decide) (by omega) (by omega))
  have readOne : s.memory.Permitted .read blockAddress 1 :=
    X86.Ext.Memory.Permitted.sub readable (by decide) (by omega) (by omega)
  have firstRead : middle.readBytes blockAddress 1 = some [0] :=
    stored.readWith_self readOne
  obtain ⟨after, loop, zeros, writes, finalCode⟩ := PaddingStream.fill_to_length
    (firstCore c) { s with memory := middle } 1 [0] (by decide) (by decide)
      running code rfl (by simp [firstCore, X86.State.read, X86.State.write])
      (stored.permitted writable) (stored.permitted readable) firstRead
  refine ⟨after, ?_, ?_, ?_, finalCode⟩
  · simpa only [List.nil_append, Padding.zeroFinished, firstCore,
      X86.State.write, Machine.RegisterFile.write_shadow] using first.append loop
  · exact zeros
  · exact (stored.writesWithin (by
      intro offset bound
      simp only [List.length_singleton] at bound
      omega)).trans (writes.mono (by intro address inside; omega))

/-- The second block has no marker; the marker belongs to the first block. -/
def block (total : Word) : List Byte := List.replicate 56 0 ++ LengthStore.encoded total

theorem block_length (total : Word) : (block total).length = 64 := by
  simp [block, LengthStore.encoded_length]

def Footprint (address : Nat) : Prop := blockAddress ≤ address ∧ address < blockAddress + 64

/-- The original total remains a ghost parameter after SHL/BSWAP destructively
serialize RBX. H32 still holds exactly the first compression's observed result. -/
structure CallReady (initial : Memory) (stack : Word) (c : Core) (s : Syscall.State)
    (tail priorH : List Byte) (total : Word) : Prop where
  long : 56 ≤ tail.length
  room : tail.length < 64
  running : s.exited = none
  pc : c.rip = CompressionSite.finalBlock.address
  stateArg : c.read .rdi = 0x401660
  blockArg : c.read .rsi = 0x401620
  serialized : c.read .rbx = LengthStore.swapped total
  block : s.memory.readBytes blockAddress 64 = some (block total)
  rsp : c.read .rsp = stack
  frame : DriverMemory.Frame initial s.memory
  hash : ∃ bytes, s.memory.readBytes 0x401660 32 = some bytes ∧
    (stateOf bytes).toState = Driver.compressBlock (stateOf priorH).toState (PaddingExtra.block tail)

def callCore (c : Core) (total : Word) : Core := LengthStore.callCore (Padding.zeroFinished c) total

/-- Execute only second-block zero and length stores, retaining H32 and the
original source/stack. The endpoint is the actual final compression CALL. -/
theorem prepare {initial : Memory} {stack : Word} {c : Core} {s : Syscall.State}
    {tail priorH : List Byte} {total : Word}
    (ready : ExtraPaddingContinuation.Ready initial stack c s tail priorH total) :
    ∃ after : Memory,
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ []
        ⟨callCore c total, { s with memory := after }⟩ ∧
      Memory.WritesWithin s.memory after Footprint ∧
      CallReady initial stack (callCore c total) { s with memory := after } tail priorH total := by
  have permission (access : Access) (allowed : Binary.seg1.permissions.allows access = true) :
      s.memory.Permitted access blockAddress 64 :=
    ready.frame.bss_permitted access allowed _ _ (by decide) (by decide)
  obtain ⟨zeroMemory, zeroRun, zeros, zeroWrites, code⟩ := zero_prefix c s ready.running
    ready.frame.code ready.pc ready.index (permission .write rfl) (permission .read rfl)
  have count : (Padding.zeroFinished c).read .rbx = total := by
    simpa [Padding.zeroFinished, X86.State.read, X86.State.write, Machine.RegisterFile.write]
      using ready.totalRetained
  obtain ⟨after, lengthRun, bytes, lengthWrites, _⟩ := LengthStore.store
    (Padding.zeroFinished c) { s with memory := zeroMemory } total (List.replicate 56 0)
      ready.running code rfl count zeros
      ((zeroWrites.permitted_iff _ _ _).mpr (permission .write rfl))
      ((zeroWrites.permitted_iff _ _ _).mpr (permission .read rfl))
  have writes : Memory.WritesWithin s.memory after Footprint :=
    (zeroWrites.mono (by intro address inside; dsimp [Footprint]; omega)).trans
      (lengthWrites.mono (by intro address inside; dsimp [Footprint]; omega))
  have frame : DriverMemory.Frame initial after := ready.frame.trans (writes.mono (by
    intro address inside
    dsimp [Footprint, blockAddress, DriverMemory.Above] at *
    omega))
  obtain ⟨stateBytes, observed, equation⟩ := ready.hash
  have observed' : after.readBytes 0x401660 32 = some stateBytes := by
    rw [writes.readBytes (by intro offset bound; dsimp [Footprint, blockAddress]; omega)]
    exact observed
  have arguments := LengthStore.arguments (Padding.zeroFinished c) total
  refine ⟨after, by simpa only [List.nil_append, callCore] using zeroRun.append lengthRun,
    writes, ready.long, ready.room, ready.running, rfl, arguments.2.1, arguments.1,
    ?_, bytes, ?_, frame, stateBytes, observed', equation⟩
  · simp [callCore, LengthStore.callCore, X86.State.read, X86.State.write,
      Machine.RegisterFile.write]
  · simpa [callCore, Padding.zeroFinished, X86.State.read, X86.State.write,
      Machine.RegisterFile.write] using arguments.2.2.trans ready.rsp

end Silmaril.Process.CLI.Sha256Cli.SecondPaddingFrame
