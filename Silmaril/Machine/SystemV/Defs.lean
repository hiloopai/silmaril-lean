module

public import Silmaril.Machine.X86.CallingConvention.Defs
public import Silmaril.Machine.X86.Spec.EnsuresSysV.Defs
public import Silmaril.Machine.C.Api.SysV.Defs

/-! Stable interface for the imported INTEGER-class System V AMD64 contracts.
The convention and machine state are `Silmaril.X86`'s; the
C boundary (`Silmaril.C.Api`) adds scalar encodings, stack arguments and memory frames.
`Result` assembles the independent return obligations needed by a future native
compiler stage. No compiler-correctness claim follows from this definition.
-/

@[expose] public section
namespace Silmaril.Machine.SystemV

abbrev convention := Silmaril.X86.sysv64
abbrev Call := Silmaril.C.Api.SysV.Call
abbrev Footprint := Silmaril.C.Api.SysV.Footprint

/-- The observable result and frame of one native scalar call. The argument
representation and entry alignment are stated separately by `SysV.Entry`. -/
structure Result (kind : Option Silmaril.C.Api.Scalar)
    (value : Silmaril.C.Api.ReturnValue kind) (writes : Footprint)
    (call : Call) (final : Silmaril.X86.MState) : Prop where
  returned : Silmaril.C.Api.SysV.Return call final
  valueAt : Silmaril.C.Api.SysV.ResultAt final kind value
  frame : Silmaril.C.Api.SysV.Frame writes call final

/-- A native implementation of a scalar C API operation. This is a specification:
a compiler or decompilation certificate must separately prove it for its code.
The domain records code loading and source preconditions beyond the ABI. The
implementation receives logical call metadata and must execute to its exit.
-/
def Realizes (signature : Silmaril.C.Api.Signature)
    (result : Silmaril.C.Api.Arguments signature.arguments →
      Silmaril.C.Api.ReturnValue signature.result)
    (writes : Silmaril.C.Api.Arguments signature.arguments → Footprint)
    (domain : Silmaril.C.Api.Arguments signature.arguments → Call → Prop)
    (execute : Call → Silmaril.X86.MState → Prop) : Prop :=
  ∀ arguments call, Silmaril.C.Api.SysV.Entry signature arguments call →
    domain arguments call → ∃ final, execute call final ∧
      Result signature.result (result arguments) (writes arguments) call final

end Silmaril.Machine.SystemV
