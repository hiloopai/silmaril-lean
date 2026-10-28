module

public import Silmaril.Process.CLI.Sha256Cli.EmptySupport
public import Silmaril.Process.CLI.Sha256Cli.OutputFrame

/-! # The actual final compression CALL, with its ABI entry discharged

The caller still owes its padded block, initial H bytes and preceding frame.
This theorem proves the real CALL pushes its return address, establishes the
full unweakened System V callee entry at the CLI's layout, and consumes #3040's
generic silent-process bridge. No driver totality or heap model is assumed.
-/

@[expose] public section

namespace Silmaril.Process.CLI.Sha256Cli.CompressionEntry

open Silmaril.Process.Syscall
open Silmaril.Process.CLI.X86Linux
open Silmaril.X86 (Word MState sysv64)
open Silmaril.Crypto.X86.Sha256O2

def entryStack : Word := BitVec.ofNat 64 (sp - 40)
def returnAddress : Word := 0x40022e
def callCore (c : Core) : Core := { c.write .rsp entryStack with rip := 0x4002e0 }

private theorem initial_stack (access : Silmaril.Process.Access) :
    access = .read ∨ access = .write →
      memory₀.Permitted access (sysv64.frameFloor entryStack.toNat frameSize)
        (sysv64.frameExtent frameSize) := by
  rintro (rfl | rfl) <;>
    apply X86.EntryState.permitted placements_wf
      (placement := ⟨⟨sp - stackRoom, stackRoom, ⟨true, true, false⟩⟩, none⟩)
      (by simp [placements]) rfl
  all_goals decide

set_option maxRecDepth 100000 in
theorem empty_call (c : Core) (s : Syscall.State)
    (running : s.exited = none) (intact : Output.Intact s.memory)
    (pc : c.rip = 0x400229) (rsp : c.read .rsp = BitVec.ofNat 64 (sp - 32))
    (argState : c.read .rdi = 0x401660) (argBlock : c.read .rsi = 0x401620)
    (initialBytes : s.memory.readBytes 0x401660 32 = some EmptySupport.initialStateBytes)
    (paddedBytes : s.memory.readBytes 0x401620 64 = some EmptySupport.emptyBlock)
    {inside : Nat → Prop} (frame : Memory.WritesWithin memory₀ s.memory inside)
    (codeOutside : ∀ offset < size, ¬ inside (0x4002e0 + offset))
    (tableOutside : ∀ offset < kSize, ¬ inside (0x4004c0 + offset)) :
    ∃ (entryMemory : Memory) (final : MState),
      Proc.Runs X86Linux.isa Env.linux ⟨c, s⟩ []
        ⟨final.core, { s with memory := final.memory }⟩ ∧
      X86.Ext.Stored s.memory entryMemory entryStack.toNat
        (Silmaril.Machine.LittleEndian.encodeWords [returnAddress]) ∧
      SysVEntry (EmptySupport.layout returnAddress) 0x401660 0x401620 entryStack frameSize
        ⟨callCore c, entryMemory⟩ ∧
      Post (EmptySupport.layout returnAddress) 0x401660 0x401620 entryStack frameSize
        ⟨callCore c, entryMemory⟩ final ∧
      final.core.rip = returnAddress ∧
      final.memory.readBytes 0x401660 32 = some EmptySupport.emptyStateBytes := by
  have address : c.read .rsp - (8 : Word) = entryStack := by rw [rsp]; rfl
  have writeReturn : s.memory.Permitted .write entryStack.toNat 8 := by
    apply (frame.permitted_iff _ _ _).mpr
    apply X86.EntryState.permitted placements_wf
      (placement := ⟨⟨sp - stackRoom, stackRoom, ⟨true, true, false⟩⟩, none⟩)
      (by simp [placements]) rfl
    all_goals decide
  have pushPermitted : s.memory.Permitted .write (c.read .rsp - (8 : Word)).toNat 8 := by
    erw [address]
    exact writeReturn
  obtain ⟨entryMemory, pushed, stored⟩ := X86.Ext.pushWord_isSome
    (s := c) (v := returnAddress) pushPermitted
  erw [address] at stored
  have effect : Binary.i_400229.denote c s.memory = .retired (callCore c) entryMemory := by
    change X86Linux.execResult
      (match X86.pushWord c s.memory (c.rip + 5) with
       | none => .dataFault
       | some (t, m) => .ok { t with rip := c.rip + 5 + (0xb2 : BitVec 32).signExtend 64 } m) = _
    rw [pc]
    change X86Linux.execResult
      (match X86.pushWord c s.memory returnAddress with
       | none => .dataFault
       | some (t, m) => .ok { t with rip := 0x4002e0 } m) = _
    rw [pushed]
    erw [address]
    rfl
  have call : Proc.Step X86Linux.isa Env.linux (⟨c, s⟩ : Output.PS) []
      ⟨callCore c, { s with memory := entryMemory }⟩ :=
    .retire running ((step_of_entry Binary.ok_400229.1
      (by simp [pc, Binary.i_400229]) (intact _ (by simp [Binary.transcript]))).trans effect).symm
  obtain ⟨code, table⟩ := EmptySupport.constants_of_frame (loaded []).1 frame codeOutside tableOutside returnAddress
  have code' : entryMemory.fetchBytes 0x4002e0 size =
      some (Silmaril.Crypto.X86.Sha256O2.image 0x4002e0 0x4004c0) :=
    (stored.readWith_disjoint .execute 0x4002e0 size (Or.inl (by decide))).trans code
  have table' : entryMemory.readBytes 0x4004c0 kSize = some kBytes :=
    (stored.readWith_disjoint .read 0x4004c0 kSize (Or.inl (by decide))).trans table
  have state' : entryMemory.readBytes 0x401660 32 = some EmptySupport.initialStateBytes :=
    (stored.readWith_disjoint .read 0x401660 32 (Or.inl (by decide))).trans initialBytes
  have block' : entryMemory.readBytes 0x401620 64 = some EmptySupport.emptyBlock :=
    (stored.readWith_disjoint .read 0x401620 64 (Or.inl (by decide))).trans paddedBytes
  have writable : entryMemory.Permitted .write 0x401660 32 :=
    stored.permitted ((frame.permitted_iff _ _ _).mpr (by
      apply X86.EntryState.permitted placements_wf
        (placement := ⟨Binary.seg1.region, some (List.replicate 0xc0 0)⟩)
        (by simp [placements]) rfl
      all_goals decide))
  have entry : SysVEntry (EmptySupport.layout returnAddress) 0x401660 0x401620 entryStack frameSize
      ⟨callCore c, entryMemory⟩ := by
    refine ⟨rfl, code', EmptySupport.layout_relocFits _, table', ?_, ?_, ?_,
      (by change entryStack.toNat % 16 = 8; decide),
      ?_, ⟨_, state'⟩, writable, ⟨_, block'⟩, ?_, by decide, ?_, by decide, by decide⟩
    · simpa [callCore, X86.State.read, X86.State.write] using argState
    · simpa [callCore, X86.State.read, X86.State.write] using argBlock
    · simp [callCore, X86.State.read, X86.State.write]
    · change entryMemory.readWith .read entryStack.toNat
        (Machine.LittleEndian.encodeWords [returnAddress]).length =
          some (Machine.LittleEndian.encodeWords [returnAddress])
      apply stored.readWith_self
      change s.memory.Permitted .read entryStack.toNat 8
      apply (frame.permitted_iff .read entryStack.toNat 8).mpr
      apply X86.EntryState.permitted placements_wf
        (placement := ⟨⟨sp - stackRoom, stackRoom, ⟨true, true, false⟩⟩, none⟩)
        (by simp [placements]) rfl
      all_goals decide
    · exact ⟨stored.permitted ((frame.permitted_iff _ _ _).mpr (initial_stack .read (.inl rfl))),
        stored.permitted ((frame.permitted_iff _ _ _).mpr (initial_stack .write (.inr rfl)))⟩
    · intro region member
      simp only [regions, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨final, _, body, post, returned⟩ := EmptySupport.compress_cli_live Env.linux_memoryLens
    (s := { s with memory := entryMemory }) running entry
  have digest := EmptySupport.post_empty_bytes
    (exit := returnAddress) (state := 0x401660) (block := 0x401620)
    (rspEntry := entryStack) (initial := ⟨callCore c, entryMemory⟩) (final := final)
    post state' block'
  exact ⟨entryMemory, final, by
    simpa only [Env.linux, List.nil_append] using (Machine.Trace.Runs.single call).append body,
    stored, entry, post, returned, digest⟩

end Silmaril.Process.CLI.Sha256Cli.CompressionEntry
