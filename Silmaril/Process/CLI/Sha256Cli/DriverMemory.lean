module

public import Silmaril.Process.CLI.Sha256Cli.LoadedStartup

/-! # Driver memory facts independent of a fixed launch

A frame keeps its original mapped image explicit. It supplies code integrity,
static-buffer permissions and constant backing for arbitrary initial memory;
it says nothing about stack readability or stack/global disjointness.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.DriverMemory

open Silmaril.Process.CLI.X86Linux

def Above (address : Nat) : Prop := 0x4005c0 ≤ address

structure Frame (initial current : Memory) : Prop where
  mapped : image.Mapped initial
  changes : Memory.WritesWithin initial current Above

theorem Frame.refl {memory : Memory} (mapped : image.Mapped memory) : Frame memory memory :=
  ⟨mapped, Memory.WritesWithin.refl memory Above⟩

theorem Frame.trans {initial before after : Memory} (frame : Frame initial before)
    (step : Memory.WritesWithin before after Above) : Frame initial after :=
  ⟨frame.mapped, frame.changes.trans step⟩

/-- The source mapping supplies permissions; the frame transports them.
Neither zeroed memory nor any fixed address for the caller's stack is used. -/
theorem Frame.bss_permitted {initial current : Memory} (frame : Frame initial current)
    (access : Access) (allowed : Binary.seg1.permissions.allows access = true)
    (address length : Nat) (lower : 0x4015c0 ≤ address)
    (upper : address + length ≤ 0x401680) : current.Permitted access address length := by
  apply (frame.changes.permitted_iff _ _ _).mpr
  have member : Binary.seg1 ∈ image.segments := by simp [image, Binary.image]
  apply Memory.permitted_of_region initial access address length Binary.seg1.region
    (frame.mapped Binary.seg1 member).1 allowed
  · dsimp [addressLimit]; omega
  · dsimp [addressLimit]; omega
  · exact lower
  · exact upper

/-- Writes above the executable segment preserve every checked instruction. -/
theorem Frame.code {initial current : Memory} (frame : Frame initial current) :
    Output.Intact current := by
  intro entry member
  rw [frame.changes.fetchBytes (by
    intro offset bound outside
    have endOfCode := Output.code_end entry member
    dsimp [Above] at outside
    omega)]
  exact fetch_of_codeAt image_wf frame.mapped (image_faithful entry member).2
    (image_faithful entry member).1.length_pos

theorem Frame.hexTable {initial current : Memory} (frame : Frame initial current) :
    current.readBytes 0x4004b0 16 = some EmptySupport.hexDigits := by
  rw [frame.changes.readBytes (by intro offset bound outside; dsimp [Above] at outside; omega)]
  exact EmptySupport.loaded_hexTable frame.mapped

theorem Frame.constants {initial current : Memory} (frame : Frame initial current)
    (exit : X86.Word) :
    current.fetchBytes (EmptySupport.layout exit).textBase.toNat
        Silmaril.Crypto.X86.Sha256O2.size =
      some (Silmaril.Crypto.X86.Sha256O2.image 0x4002e0 0x4004c0) ∧
    current.readBytes (EmptySupport.layout exit).rodataBase.toNat
        Silmaril.Crypto.X86.Sha256O2.kSize = some Silmaril.Crypto.X86.Sha256O2.kBytes :=
  EmptySupport.constants_of_frame frame.mapped frame.changes
    (by intro offset bound outside; dsimp [Above] at outside; change offset < 459 at bound; omega)
    (by intro offset bound outside; dsimp [Above] at outside; change offset < 256 at bound; omega) exit


/-- Startup turns its exact symbolic write footprint into the reusable frame.
The loader alone supplies no separation; the same explicit geometry as the
startup theorem remains a premise. -/
theorem launch_read (input : ProcInput) (initial : Core) (s : Syscall.State)
    (loaded : Loaded image input initial s.memory)
    (apart : 0x4005c0 ≤ (initial.read .rsp).toNat - 24)
    (running : s.exited = none) :
    ∃ after : Memory,
      Proc.Runs X86Linux.isa Env.linux ⟨initial, s⟩ []
        ⟨LoadedStartup.readCore initial (initial.read .rsp).toNat, { s with memory := after }⟩ ∧
      after.readBytes InitStores.stateAddress 32 = some EmptySupport.initialStateBytes ∧
      Frame s.memory after := by
  obtain ⟨after, run, bytes, changes, _⟩ := LoadedStartup.of_loaded input initial s loaded apart running
  refine ⟨after, run, bytes, loaded.1, changes.mono ?_⟩
  intro address member
  rcases member with stack | state
  · dsimp [Above]
    omega
  · dsimp [Above, InitStores.stateAddress] at *
    omega

end Silmaril.Process.CLI.Sha256Cli.DriverMemory
