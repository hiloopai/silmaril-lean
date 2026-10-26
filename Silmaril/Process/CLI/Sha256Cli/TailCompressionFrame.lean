module

public import Silmaril.Process.CLI.Sha256Cli.TailPaddingFrame
public import Silmaril.Process.CLI.Sha256Cli.CompressionCallFrame

/-! # Actual final-tail compression from accumulated hash bytes

The callee's one-step reference equation is retained, without resetting H0
or identifying a modular machine total with a natural message length.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.TailPaddingFrame

open Silmaril.Process.Syscall Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word MState)
open Silmaril.Crypto.X86.Sha256O2

theorem CallReady.compress {initial : Memory} {top : Nat} {c : Core} {s : Syscall.State}
    {tail stateBytes : List Byte} {total : Word}
    (ready : CallReady initial (BitVec.ofNat 64 (top - 32)) c s tail stateBytes total)
    (geometry : CompressionStack.Geometry top) (stack : CompressionStack.Mapping initial top) :
    ∃ final : MState,
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ []
        ⟨final.core, { s with memory := final.memory }⟩ ∧
      final.core.rip = CompressionCallFrame.returnAddress ∧
      final.core.read .rsp = BitVec.ofNat 64 (top - 32) ∧
      DriverMemory.Frame initial final.memory ∧
      ∃ bytes, final.memory.readBytes 0x401660 32 = some bytes ∧
        (stateOf bytes).toState = Driver.compressBlock (stateOf stateBytes).toState
          (TailPaddingFrame.block tail total) := by
  obtain ⟨_, final, run, _, _, _, returned, _, _, restored, frame, reference⟩ :=
    CompressionCallFrame.invoke c s stateBytes (TailPaddingFrame.block tail total)
      ready.running ready.frame.code ready.pc ready.rsp ready.stateArg ready.blockArg
      ready.state ready.block ready.frame geometry stack
  exact ⟨final, run, returned, restored, frame, reference⟩

end Silmaril.Process.CLI.Sha256Cli.TailPaddingFrame
