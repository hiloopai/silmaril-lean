module

public import Silmaril.Process.CLI.Sha256Cli.HexOutputFrame
public import Silmaril.Process.CLI.LinuxDescriptors

/-! # Finish an actual SHA output-ready prefix

The source is the caller's original process state. Descriptor availability is
transported through its actual run; a full-write schedule is then chosen
independently of the universal prefix and successful-completion theorems.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.HexOutputFrame

open Silmaril.Process.Syscall Silmaril.Process.CLI.X86Linux

/-- Extend the supplied original run with an admitted full write and the real
exit. This witnesses one successful schedule, without a progress assertion. -/
theorem Ready.finish {initial : Memory} {c : Core} {s : Syscall.State}
    {message : List Byte} (ready : Ready initial c s message)
    {source : Output.PS} {input : ProcInput} {prior : List Event}
    (prepared : Proc.Runs X86Linux.isa Env.linux source prior ⟨c, s⟩)
    (accounted : Driver.OutputInv message prior 0)
    (finite : input.stdin = .ofList message) {descriptor : Descriptor}
    (opened : source.env.descriptors 1 = some descriptor)
    (writable : descriptor.writable = true) :
    ∃ final : Output.PS,
      Proc.Runs X86Linux.isa Env.linux source
        (prior ++ [.write 1 (Sha256.expected message), .exit 0]) final ∧
      Proc.Stop X86Linux.isa Env.linux final (.exited 0) ∧
      Sha256.Success input (prior ++ [.write 1 (Sha256.expected message), .exit 0]) := by
  obtain ⟨descriptor, finalOpen, finalWritable⟩ := Proc.runs_linux_writable prepared opened writable
  obtain ⟨final, output, stopped⟩ := ready.full_write finalOpen finalWritable
  exact ⟨final, prepared.append output, stopped, ready.completed accounted finite output stopped⟩

end Silmaril.Process.CLI.Sha256Cli.HexOutputFrame
