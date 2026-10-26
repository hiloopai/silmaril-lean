module

public import Silmaril.Process.CLI.Sha256Cli.LoadedStartup
public import Silmaril.X86.Ext.Store

/-! # A real initial CALL from the inhabited minimal-filter launch

The entry instruction writes its return address to the mapped stack and
branches to `cmain`. This structural proof uses the existing opaque-store
lemmas; it does not evaluate the hash-map implementation or assume a complete
driver run. The remaining 15 retirements to the first read are separate.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.Startup

set_option maxRecDepth 10000

open Silmaril.Process.Syscall
open Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word)

def mainCore : Core :=
  { core₀.write .rsp (BitVec.ofNat 64 (sp - 8)) with rip := 0x400100 }

theorem stack_permission : memory₀.Permitted .write (sp - 8) 8 := by
  apply X86.EntryState.permitted placements_wf
    (placement := ⟨⟨sp - stackRoom, stackRoom, ⟨true, true, false⟩⟩, none⟩)
    (by simp [placements]) rfl
  all_goals decide

/-- A genuine entry execution with its exact stack write and no observation.
Every admitted environment state with `memory₀` and no exit has this step. -/
theorem call_main (s : Syscall.State) (memory : s.memory = memory₀)
    (running : s.exited = none) :
    ∃ after : Memory,
      Proc.Runs X86Linux.isa Env.linux ⟨core₀, s⟩ []
        ⟨mainCore, { s with memory := after }⟩ ∧
      X86.Ext.Stored memory₀ after (sp - 8)
        (Silmaril.Machine.LittleEndian.encodeWords [(0x4000f5 : Word)]) := by
  have intact : Output.Intact s.memory := by
    rw [memory]
    intro entry member
    exact Transcript.fetch image_faithful image_wf (loaded []) member
  have stack : s.memory.Permitted .write (sp - 8) 8 := by
    rw [memory]
    exact stack_permission
  obtain ⟨after, run, stored⟩ := LoadedStartup.call_main core₀ sp s
    (by decide) (by decide) rfl rfl intact running stack
  exact ⟨after, run, by simpa only [memory] using stored⟩

end Silmaril.Process.CLI.Sha256Cli.Startup
