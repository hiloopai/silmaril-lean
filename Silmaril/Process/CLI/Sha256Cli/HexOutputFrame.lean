module

public import Silmaril.Process.CLI.Sha256Cli.DriverMemory
public import Silmaril.Process.CLI.Sha256Cli.HexReference
public import Silmaril.Process.CLI.Sha256Cli.EmptyPrepared
public import Silmaril.Process.CLI.Sha256Cli.OutputPrefix
public import Silmaril.Process.CLI.Sha256Cli.OutputUniversal

/-! # Dynamic hash-state formatting and output transport

The actual hexadecimal loop and newline/setup instructions operate over any
mapped source frame. The output interface retains that source, the canonical
65 bytes and the actual request state. Its safety theorems preserve the caller's
original finite execution and stop; no successful syscall or progress is assumed.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.HexOutputFrame

open Silmaril.Process.Syscall Silmaril.Process.CLI.X86Linux
open Silmaril.Crypto.X86.Sha256O2

structure Ready (initial : Memory) (c : Core) (s : Syscall.State)
    (message : List Byte) : Prop where
  running : s.exited = none
  frame : DriverMemory.Frame initial s.memory
  answer : s.memory.readBytes 0x4015c0 65 = some (Sha256.expected message)
  request : OutputTransfer.requestCore c 0 = c

/-- Actual hash return through all hex instructions and the real newline store.
No fixed source memory or fixed launch stack is used. -/
theorem prepare {initial : Memory} (c : Core) (s : Syscall.State)
    (bytes message : List Byte) (running : s.exited = none)
    (frame : DriverMemory.Frame initial s.memory) (pc : c.rip = 0x40022e)
    (stateRead : s.memory.readBytes 0x401660 32 = some bytes)
    (value : (stateOf bytes).toState = Silmaril.Crypto.SHA256.hash (message.map UInt8.ofBitVec)) :
    ∃ (outCore : Core) (memory : Memory),
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ []
        ⟨outCore, { s with memory := memory }⟩ ∧
      Ready initial outCore { s with memory := memory } message := by
  obtain ⟨hexCore, hexMemory, hexRun, hexPc, _, digits, hexWrites⟩ :=
    HexReference.run c s bytes message running frame.code pc stateRead value frame.hexTable
      (frame.bss_permitted .write rfl _ _ (by decide) (by decide))
      (frame.bss_permitted .read rfl _ _ (by decide) (by decide))
  have hexFrame : DriverMemory.Frame initial hexMemory := frame.trans (hexWrites.mono (by
    intro address inside
    dsimp [HexLoop.Footprint, DriverMemory.Above] at *
    omega))
  obtain ⟨memory, setup, answer, _, newlineWrites⟩ := OutputSetup.setup
    hexCore { s with memory := hexMemory } message running hexFrame.code hexPc digits
      (hexFrame.bss_permitted .write rfl _ _ (by decide) (by decide))
      (hexFrame.bss_permitted .read rfl _ _ (by decide) (by decide))
  exact ⟨OutputSetup.prepared hexCore, memory, by
    simpa only [List.nil_append] using hexRun.append setup,
    running, hexFrame.trans (newlineWrites.mono (by
      intro address equal
      dsimp [DriverMemory.Above]
      omega)), answer, EmptyPrepared.request_prepared hexCore⟩

/-- Prefix safety includes short writes, zero replies, errors and arbitrary R11. -/
theorem Ready.prefix {initial : Memory} {c : Core} {s : Syscall.State}
    {message : List Byte} (ready : Ready initial c s message)
    {input : ProcInput} {prior events : List Event} {final : Output.PS}
    (accounted : Driver.OutputInv message prior 0) (finite : input.stdin = .ofList message)
    (run : Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ events final) :
    Sha256.PrefixOk input (prior ++ events) := by
  apply OutputPrefix.prefix_request c s 0 ready.frame.code ready.running ready.answer accounted finite
  simpa only [ready.request] using run

/-- Successful completion is a condition on the original run and endpoint. -/
theorem Ready.completed {initial : Memory} {c : Core} {s : Syscall.State}
    {message : List Byte} (ready : Ready initial c s message)
    {input : ProcInput} {prior events : List Event} {final : Output.PS}
    (accounted : Driver.OutputInv message prior 0) (finite : input.stdin = .ofList message)
    (run : Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ events final)
    (stop : Proc.Stop X86Linux.isa Env.linux final (.exited 0)) :
    Sha256.Success input (prior ++ events) := by
  apply OutputUniversal.completed_request c s 0 ready.frame.code ready.running ready.answer
    accounted finite (stop := stop)
  simpa only [ready.request] using run

/-- One admitted full write/exit schedule, conditional on an open writable stdout.
This witness is separate from universal safety and promises no progress. -/
theorem Ready.full_write {initial : Memory} {c : Core} {s : Syscall.State}
    {message : List Byte} (ready : Ready initial c s message) {descriptor : Descriptor}
    (opened : s.descriptors 1 = some descriptor) (writable : descriptor.writable = true) :
    ∃ final : Output.PS,
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩
        [.write 1 (Sha256.expected message), .exit 0] final ∧
      Proc.Stop X86Linux.isa Env.linux final (.exited 0) := by
  have normalized : Output.writeCore (OutputTransfer.requestCore c 0) =
      OutputTransfer.requestCore c 0 := by
    apply Eq.mpr (X86.State.mk.injEq _ _ _ _ _ _ _ _)
    refine ⟨?_, rfl, rfl, rfl⟩
    funext register
    cases register <;> rfl
  rw [ready.request] at normalized
  obtain ⟨final, run, stopped⟩ := Output.full_write c s message ready.frame.code ready.running
    opened writable ready.answer
  exact ⟨final, by simpa only [normalized] using run, stopped⟩

end Silmaril.Process.CLI.Sha256Cli.HexOutputFrame
