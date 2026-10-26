module

public import Silmaril.Process.CLI.Sha256Cli.StartupPrefix
public import Silmaril.Process.CLI.Sha256Cli.InitStores
public import Silmaril.Process.CLI.Sha256Cli.Eof

/-! # From the inhabited launch to the real positive-count read

The sixteen actual instructions initialize H and reach read(0,blk,64).
Combining with the admitted empty read then reaches the empty padding branch.
No theorem here assumes a complete driver execution or rules out other
environment choices. Compression/padding/hex/output remain separate segments.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.ReadPrefix

open Silmaril.Process.Syscall
open Silmaril.Process.CLI.X86Linux

def readyCore : Core := InitStores.readCore Startup.initCore

def Footprint (address : Nat) : Prop :=
  (sp - 32 ≤ address ∧ address < sp) ∨ (0x401660 ≤ address ∧ address < 0x401680)

theorem launch_read (s : Syscall.State) (memory : s.memory = memory₀)
    (running : s.exited = none) :
    ∃ after : Memory,
      Proc.Runs X86Linux.isa Env.linux ⟨core₀, s⟩ []
        ⟨readyCore, { s with memory := after }⟩ ∧
      after.readBytes 0x401660 32 = some EmptySupport.initialStateBytes ∧
      Memory.WritesWithin memory₀ after Footprint ∧ Output.Intact after := by
  obtain ⟨middle, prefixRun, prefixFrame, prefixCode⟩ := Startup.launch_to_init s memory running
  have writeH : middle.Permitted .write InitStores.stateAddress 32 :=
    (prefixFrame.permitted_iff .write InitStores.stateAddress 32).mpr InitStores.initial_permissions.1
  have readH : middle.Permitted .read InitStores.stateAddress 32 :=
    (prefixFrame.permitted_iff .read InitStores.stateAddress 32).mpr InitStores.initial_permissions.2
  obtain ⟨after, initRun, initialized, initFrame, code⟩ :=
    InitStores.initialize_read Startup.initCore { s with memory := middle }
      running prefixCode rfl rfl writeH readH
  refine ⟨after, ?_, initialized, ?_, code⟩
  · simpa only [List.nil_append, readyCore] using prefixRun.append initRun
  · exact (prefixFrame.mono (fun _ h => Or.inl h)).trans
      (initFrame.mono (fun _ h => Or.inr h))

theorem block_writable : memory₀.Permitted .write 0x401620 64 := by
  apply X86.EntryState.permitted placements_wf
    (placement := ⟨Binary.seg1.region, some (List.replicate 0xc0 0)⟩)
    (by simp [placements]) rfl
  all_goals decide

/-- Only redundant assignments distinguish the concrete startup endpoint
from the EOF segment's general register-entry normal form. -/
theorem ready_eq : Eof.readCore readyCore = readyCore := by
  apply Eq.mpr (X86.State.mk.injEq _ _ _ _ _ _ _ _)
  refine ⟨?_, rfl, rfl, rfl⟩
  funext register
  cases register <;> rfl

/-- A concrete standard-descriptor environment, with the actual initial
memory. Its loader/environment relation is inhabited on every byte input. -/
def environment (message : List Byte) : Syscall.State :=
  ⟨memory₀, fun fd =>
    if fd = 0 then some ⟨true, false, .ofList message, 0, []⟩
    else if fd = 1 ∨ fd = 2 then some ⟨false, true, .ofList [], 0, []⟩ else none, none⟩

theorem initial (message : List Byte) :
    X86Linux.linux.Init image (inputOf message) ⟨core₀, environment message⟩ :=
  ⟨memory₀, loaded message, rfl, rfl, by simp [StdDescriptors, environment, inputOf]⟩

/-- A real launch, sixteen retired instructions, genuine 64-byte EOF request,
TEST and JE reach the empty padding path, retaining exact initial H bytes.
This proves a bounded successful prefix, not successful whole-program exit. -/
theorem empty_to_padding :
    ∃ after : Memory,
      Proc.Runs X86Linux.isa Env.linux ⟨core₀, environment []⟩ [.read 0 []]
        ⟨Eof.paddingCore readyCore, { environment [] with memory := after }⟩ ∧
      after.readBytes 0x401660 32 = some EmptySupport.initialStateBytes ∧
      Memory.WritesWithin memory₀ after Footprint ∧ Output.Intact after := by
  obtain ⟨after, start, bytes, frame, code⟩ := launch_read (environment []) rfl rfl
  have writable : after.Permitted .write 0x401620 64 :=
    (frame.permitted_iff .write 0x401620 64).mpr block_writable
  have eof := Eof.read_to_padding readyCore { environment [] with memory := after }
    (descriptor := ⟨true, false, .ofList [], 0, []⟩)
    rfl code (by simp [environment]) rfl rfl writable
  rw [ready_eq] at eof
  exact ⟨after, start.append eof, bytes, frame, code⟩

end Silmaril.Process.CLI.Sha256Cli.ReadPrefix
