module

public import Silmaril.Process.CLI.Sha256Cli.DriverMemory
public import Silmaril.Process.CLI.Sha256Cli.Padding
public import Silmaril.Process.CLI.Sha256Cli.ReadPrefix
public import Silmaril.Process.CLI.Sha256Cli.CompressionFrame
public import Silmaril.Process.CLI.Sha256Cli.HexLoop
public import Silmaril.Process.CLI.Sha256Cli.OutputSetup
public import Silmaril.Process.CLI.Sha256Cli.OutputTransfer

/-! # The empty hash's silent segment for every caller register state

The actual padding/compression/hex/output preparation is independent of the
kernel's unspecified R11 return. These local segment theorems retain arbitrary
caller/environment fields, derive the full compression entry, and reach the
canonical write request. Completion transport can therefore consume them for
every admitted syscall reply, without requiring termination of other runs.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.EmptyPrepared

open Silmaril.Process.Syscall
open Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word)

theorem bss_permitted (access : Access)
    (allowed : Binary.seg1.permissions.allows access = true)
    (address length : Nat) (lower : 0x4015c0 ≤ address)
    (upper : address + length ≤ 0x401680) : memory₀.Permitted access address length :=
  (DriverMemory.Frame.refl (loaded []).1).bss_permitted access allowed address length lower upper

theorem request_prepared (c : Core) :
    OutputTransfer.requestCore (OutputSetup.prepared c) 0 = OutputSetup.prepared c := by
  apply Eq.mpr (X86.State.mk.injEq _ _ _ _ _ _ _ _)
  refine ⟨?_, rfl, rfl, rfl⟩
  funext register
  cases register <;> rfl

/-- From the actual final CALL, for every caller state satisfying its derived
buffer/frame premises, construct the silent execution to the canonical write
cut point. No particular syscall resume value is selected. -/
theorem from_call (c : Core) (s : Syscall.State)
    (running : s.exited = none) (code : Output.Intact s.memory)
    (pc : c.rip = 0x400229) (rsp : c.read .rsp = BitVec.ofNat 64 (sp - 32))
    (argState : c.read .rdi = 0x401660) (argBlock : c.read .rsi = 0x401620)
    (initialH : s.memory.readBytes 0x401660 32 = some EmptySupport.initialStateBytes)
    (block : s.memory.readBytes 0x401620 64 = some EmptySupport.emptyBlock)
    {inside : Nat → Prop} (frame : Memory.WritesWithin memory₀ s.memory inside)
    (above : ∀ address, inside address → 0x4005c0 ≤ address) :
    ∃ (outCore : Core) (answerMemory : Memory),
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ []
        ⟨outCore, { s with memory := answerMemory }⟩ ∧
      answerMemory.readBytes 0x4015c0 65 = some (Sha256.expected []) ∧
      Output.Intact answerMemory ∧ OutputTransfer.requestCore outCore 0 = outCore := by
  obtain ⟨entryMemory, final, compressionRun, callStored, _, post, returned, digest⟩ :=
    CompressionEntry.empty_call c s running code pc rsp argState argBlock initialH block frame
      (by intro offset bound member; have := above _ member; change offset < 459 at bound; omega)
      (by intro offset bound member; have := above _ member; change offset < 256 at bound; omega)
  have entryCode : Output.Intact entryMemory :=
    Output.intact_of_store code callStored (by decide)
  have finalCode : Output.Intact final.memory := CompressionEntry.post_intact post entryCode
  have tableBefore : s.memory.readBytes 0x4004b0 16 = some EmptySupport.hexDigits := by
    rw [frame.readBytes (by intro offset bound member; have := above _ member; omega)]
    exact EmptySupport.loaded_hexTable (loaded []).1
  have tableEntry : entryMemory.readBytes 0x4004b0 16 = some EmptySupport.hexDigits :=
    (callStored.readWith_disjoint .read _ _ (Or.inl (by decide))).trans tableBefore
  have tableFinal : final.memory.readBytes 0x4004b0 16 = some EmptySupport.hexDigits :=
    (CompressionEntry.post_hexTable post).trans tableEntry
  have finalPermission (access : Access) (address length : Nat)
      (initial : memory₀.Permitted access address length) :
      final.memory.Permitted access address length :=
    (post.untouched.permitted_iff _ _ _).mpr
      (callStored.permitted ((frame.permitted_iff _ _ _).mpr initial))
  obtain ⟨hexCore, hexMemory, hexRun, hexPc, _, digits, hexFrame⟩ :=
    HexLoop.empty final.core { s with memory := final.memory }
      running finalCode returned digest tableFinal
      (finalPermission .write _ _ (bss_permitted .write rfl _ _ (by decide) (by decide)))
      (finalPermission .read _ _ (bss_permitted .read rfl _ _ (by decide) (by decide)))
  have hexCode : Output.Intact hexMemory := HexLoop.intact_after_output finalCode hexFrame
  obtain ⟨answerMemory, setupRun, answer, answerCode, _⟩ :=
    OutputSetup.setup hexCore { s with memory := hexMemory } []
      running hexCode hexPc digits
      ((hexFrame.permitted_iff _ _ _).mpr
        (finalPermission .write _ _ (bss_permitted .write rfl _ _ (by decide) (by decide))))
      ((hexFrame.permitted_iff _ _ _).mpr
        (finalPermission .read _ _ (bss_permitted .read rfl _ _ (by decide) (by decide))))
  exact ⟨OutputSetup.prepared hexCore, answerMemory, by
    simpa only [List.nil_append] using (compressionRun.append hexRun).append setupRun,
    answer, answerCode, request_prepared hexCore⟩

/-- An arbitrary register state at the empty EOF branch reaches the exact
write cut point; memory effects are accounted for by the actual padding stores.
The previously initialized H/frame/stack facts remain explicit premises. -/
theorem from_padding (c : Core) (s : Syscall.State)
    (running : s.exited = none) (code : Output.Intact s.memory)
    (pc : c.rip = 0x4002b7) (rsp : c.read .rsp = BitVec.ofNat 64 (sp - 32))
    (initialH : s.memory.readBytes 0x401660 32 = some EmptySupport.initialStateBytes)
    {inside : Nat → Prop} (frame : Memory.WritesWithin memory₀ s.memory inside)
    (above : ∀ address, inside address → 0x4005c0 ≤ address) :
    ∃ (outCore : Core) (answerMemory : Memory),
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ []
        ⟨outCore, { s with memory := answerMemory }⟩ ∧
      answerMemory.readBytes 0x4015c0 65 = some (Sha256.expected []) ∧
      Output.Intact answerMemory ∧ OutputTransfer.requestCore outCore 0 = outCore := by
  have writable : s.memory.Permitted .write Padding.blockAddress 64 :=
    (frame.permitted_iff _ _ _).mpr ReadPrefix.block_writable
  have readable : s.memory.Permitted .read Padding.blockAddress 64 :=
    (frame.permitted_iff _ _ _).mpr (bss_permitted .read rfl _ _ (by decide) (by decide))
  obtain ⟨middle, padRun, padded, padFrame, padCode⟩ :=
    Padding.empty_block c s running code pc writable readable
  have state : middle.readBytes 0x401660 32 = some EmptySupport.initialStateBytes := by
    rw [padFrame.readBytes (by intro offset bound; dsimp [Padding.blockAddress]; omega)]
    exact initialH
  let wider := fun a => inside a ∨ (Padding.blockAddress ≤ a ∧ a < Padding.blockAddress + 64)
  have totalFrame : Memory.WritesWithin memory₀ middle wider :=
    (frame.mono (fun _ h => Or.inl h)).trans (padFrame.mono (fun _ h => Or.inr h))
  obtain ⟨outCore, answerMemory, rest, answer, intact, normal⟩ := from_call
    (Padding.lengthCore (Padding.zeroFinished (Padding.loopCore c))) { s with memory := middle }
    running padCode rfl (by simpa [Padding.lengthCore, Padding.zeroFinished, Padding.loopCore,
      X86.State.read, X86.State.write, Machine.RegisterFile.write] using rsp)
    (Padding.lengthCore_args _).2.1 (Padding.lengthCore_args _).1 state padded totalFrame
    (by intro a member; rcases member with h | h; exact above a h; dsimp [Padding.blockAddress] at h; omega)
  exact ⟨outCore, answerMemory, by simpa only [List.nil_append] using padRun.append rest,
    answer, intact, normal⟩

end Silmaril.Process.CLI.Sha256Cli.EmptyPrepared
