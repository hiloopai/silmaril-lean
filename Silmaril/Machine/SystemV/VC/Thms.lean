module

public import Silmaril.Machine.SystemV.VC.Defs

@[expose] public section
namespace Silmaril.Machine.SystemV.VC

open Silmaril.X86 (MState)
open Silmaril.C.Api (Signature Arguments ReturnValue)

/-- Every byte slice outside the summary's write footprint remains available
to the caller. The postcondition identifies which argument/call witness owns
that footprint, so a summary cannot silently change the domain metadata. -/
theorem Post.readBytes {signature : Signature}
    {result : Arguments signature.arguments → ReturnValue signature.result}
    {writes : Arguments signature.arguments → Footprint}
    {domain : Arguments signature.arguments → Call → Prop} {initial final : MState}
    (specified : Post signature result writes domain initial final)
    {address length : Nat}
    (disjoint : ∀ arguments call, call.initial = initial →
      Silmaril.C.Api.SysV.Entry signature arguments call → domain arguments call →
      ∀ offset < length, ¬ writes arguments (address + offset)) :
    final.memory.readBytes address length = initial.memory.readBytes address length := by
  obtain ⟨arguments, call, same, entry, inDomain, certificate⟩ := specified
  rw [← same]
  exact Result.readBytes certificate (disjoint arguments call same entry inDomain)

end Silmaril.Machine.SystemV.VC
