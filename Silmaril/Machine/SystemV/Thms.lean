module

public import Silmaril.Machine.SystemV.Defs

@[expose] public section
namespace Silmaril.Machine.SystemV

/-- The shared convention is checked independently of any compiler or binary. -/
theorem convention_wellFormed : convention.WellFormed :=
  Silmaril.X86.sysv64_wellFormed

/-- A native call certificate preserves any caller slice outside its write set. -/
theorem Result.readBytes {kind : Option Silmaril.C.Api.Scalar}
    {value : Silmaril.C.Api.ReturnValue kind} {writes : Footprint}
    {call : Call} {final : Silmaril.X86.MState}
    (certificate : Result kind value writes call final) {address length : Nat}
    (disjoint : ∀ offset < length, ¬ writes (address + offset)) :
    final.memory.readBytes address length = call.initial.memory.readBytes address length :=
  Silmaril.C.Api.SysV.Frame.readBytes certificate.frame disjoint

end Silmaril.Machine.SystemV
