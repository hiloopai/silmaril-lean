module

public import Silmaril.Process.CLI.X86Linux
public import Silmaril.Process.Memory.RegionExtension

/-! # The loader relation does not impose memory-region isolation

Adding permissions while retaining backing preserves Loaded. This deliberately
does not strengthen Loaded with a global disjointness assumption.
-/

@[expose] public section

namespace Silmaril.Process.CLI.X86Linux

open Silmaril.Process.Syscall

theorem StackLayout.region_extension {input : ProcInput} {before after : Memory} {top : Nat}
    (extension : before.RegionExtension after) (layout : StackLayout input before top) :
    StackLayout input after top := by
  obtain ⟨aligned, argv, envp, auxv, argvLength, envpLength, vectors, args, envs, null, random⟩ := layout
  refine ⟨aligned, argv, envp, auxv, argvLength, envpLength, extension.readWith vectors,
    ?_, ?_, null, ?_⟩
  · intro index hi hs
    exact extension.readWith (args index hi hs)
  · intro index hi hs
    exact extension.readWith (envs index hi hs)
  · intro value member
    obtain ⟨bytes, length, read⟩ := random value member
    exact ⟨bytes, length, extension.readWith read⟩

/-- Current Loaded is monotone under arbitrary added mapping permissions.
Thus executable-byte immutability and stack/global separation require their
own geometric or well-formedness obligations. -/
theorem Loaded.region_extension {image : Image} {input : ProcInput} {core : Core}
    {before after : Memory} (extension : before.RegionExtension after)
    (loaded : Loaded image input core before) : Loaded image input core after := by
  obtain ⟨mapped, pc, layout, room, writable, rdx⟩ := loaded
  refine ⟨?_, pc, layout.region_extension extension, room, extension.permitted writable, rdx⟩
  intro segment member
  obtain ⟨region, backing⟩ := mapped segment member
  exact ⟨extension.regions region, by simpa only [extension.bytes] using backing⟩


/-- Only the entry PC, initial stack pointer and RDX occur in Loaded.
Changing every other register or flag preserves the loader relation. -/
theorem Loaded.congr_core {image : Image} {input : ProcInput} {before after : Core}
    {memory : Memory} (loaded : Loaded image input before memory)
    (pc : after.rip = before.rip) (rsp : after.read .rsp = before.read .rsp)
    (rdx : after.read .rdx = before.read .rdx) : Loaded image input after memory := by
  simpa only [Loaded, pc, rsp, rdx] using loaded

end Silmaril.Process.CLI.X86Linux

