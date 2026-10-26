module

public import Silmaril.Process.CLI.Sha256Cli.Startup
public import Silmaril.Process.CLI.Sha256Cli.OutputFrame

/-! # The actual cmain prologue, up to SHA initialization stores -/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.Startup

open Silmaril.Process.Syscall
open Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word)

def pushedRbp : Core :=
  { mainCore.write .rsp (BitVec.ofNat 64 (sp - 16)) with rip := 0x400101 }
def countCore : Core := { pushedRbp.write .rdx 64 with rip := 0x400106 }
def bufferCore : Core := { countCore.write .rsi 0x401620 with rip := 0x40010b }
def valueCore : Core := { bufferCore.write .rax 0xbb67ae856a09e667 with rip := 0x400115 }
def pushedRbx : Core :=
  { valueCore.write .rsp (BitVec.ofNat 64 (sp - 24)) with rip := 0x400116 }
def initCore : Core :=
  { pushedRbx.write .rsp (BitVec.ofNat 64 (sp - 32)) with rip := 0x40011a, flags := X86.Ext.subFlagsN (BitVec.ofNat 64 (sp - 24)) (8 : Word) }

set_option maxRecDepth 10000 in
theorem prologue (s : Syscall.State) (intact : Output.Intact s.memory)
    (running : s.exited = none) (stack : s.memory.Permitted .write (sp - 32) 32) :
    ∃ after : Memory,
      Proc.Runs X86Linux.isa Env.linux ⟨mainCore, s⟩ []
        ⟨initCore, { s with memory := after }⟩ ∧
      Memory.WritesWithin s.memory after (fun a => sp - 32 ≤ a ∧ a < sp) ∧
      Output.Intact after := by
  have writable : s.memory.Permitted .write (sp - 24) 24 :=
    X86.Ext.Memory.Permitted.sub stack (by decide) (by decide) (by decide)
  obtain ⟨after, run, frame, code⟩ := LoadedStartup.prologue core₀ sp s
    (by decide) (by decide) (by decide) intact running writable
  exact ⟨after, run, frame.mono (by intro a inside; dsimp [sp] at inside ⊢; omega), code⟩

/-- The real loader state reaches the initialization cut point in seven
silent instructions. Only the separated stack span may have changed. -/
theorem launch_to_init (s : Syscall.State) (memory : s.memory = memory₀)
    (running : s.exited = none) :
    ∃ after : Memory,
      Proc.Runs X86Linux.isa Env.linux ⟨core₀, s⟩ []
        ⟨initCore, { s with memory := after }⟩ ∧
      Memory.WritesWithin memory₀ after (fun a => sp - 32 ≤ a ∧ a < sp) ∧
      Output.Intact after := by
  have original : Output.Intact memory₀ := by
    intro entry member
    exact Transcript.fetch image_faithful image_wf (loaded []) member
  have stack : memory₀.Permitted .write (sp - 32) 32 := by
    apply X86.EntryState.permitted placements_wf
      (placement := ⟨⟨sp - stackRoom, stackRoom, ⟨true, true, false⟩⟩, none⟩)
      (by simp [placements]) rfl
    all_goals decide
  obtain ⟨first, callRun, stored⟩ := call_main s memory running
  have intactFirst : Output.Intact first :=
    Output.intact_of_store original stored (by decide)
  have frameFirst := stored.writesWithin (inside := fun a => sp - 32 ≤ a ∧ a < sp) (by
    intro offset bound
    change offset < 8 at bound
    dsimp [sp]
    omega)
  obtain ⟨after, prefixRun, frameAfter, intactAfter⟩ :=
    prologue { s with memory := first } intactFirst running (stored.permitted stack)
  exact ⟨after, callRun.append prefixRun, frameFirst.trans frameAfter, intactAfter⟩

end Silmaril.Process.CLI.Sha256Cli.Startup
