module

public import Silmaril.Machine.SystemV.Thms
public import Silmaril.X86.SegVC

@[expose] public section
namespace Silmaril.Machine.SystemV.VC

open Silmaril.X86 (MState)
open Silmaril.C.Api (Signature Arguments ReturnValue)

/-- A native call-site precondition carries the logical arguments and call
metadata, together with the actual ABI-entry and source-domain proofs. -/
def Pre (signature : Signature)
    (domain : Arguments signature.arguments → Call → Prop) (initial : MState) : Prop :=
  ∃ arguments call, call.initial = initial ∧
    Silmaril.C.Api.SysV.Entry signature arguments call ∧ domain arguments call

/-- Call summaries retain their entry witness and the full ABI result, including
the write footprint. A continuation can therefore recover arguments, return
value, callee-saved registers and memory framing. -/
def Post (signature : Signature)
    (result : Arguments signature.arguments → ReturnValue signature.result)
    (writes : Arguments signature.arguments → Footprint)
    (domain : Arguments signature.arguments → Call → Prop)
    (initial final : MState) : Prop :=
  ∃ arguments call, call.initial = initial ∧
    Silmaril.C.Api.SysV.Entry signature arguments call ∧ domain arguments call ∧
    Result signature.result (result arguments) (writes arguments) call final

/-- Package a proved System V implementation as a contracted call for the
generic segment VC generator. Execution must be proved in this very `Isa`;
a callee-return certificate for a different designated exit is insufficient. -/
def ofRealizes (machine : Silmaril.X86.SegVC.Isa MState)
    (signature : Signature)
    (result : Arguments signature.arguments → ReturnValue signature.result)
    (writes : Arguments signature.arguments → Footprint)
    (domain : Arguments signature.arguments → Call → Prop)
    (implementation : Realizes signature result writes domain
      (fun call final => Silmaril.Machine.Execution.Reaches machine.step call.initial final)) :
    Silmaril.X86.SegVC.Call machine where
  pre := Pre signature domain
  post := Post signature result writes domain
  runs := by
    intro initial _ admitted
    obtain ⟨arguments, call, same, entry, inDomain⟩ := admitted
    obtain ⟨final, execution, specified⟩ := implementation arguments call entry inDomain
    exact ⟨final, same ▸ execution, arguments, call, same, entry, inDomain, specified⟩

end Silmaril.Machine.SystemV.VC
