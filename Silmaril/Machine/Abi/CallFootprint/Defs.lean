module

public import Silmaril.Machine.SystemV.Defs
public import Silmaril.Machine.SystemV.Abi.Ffi.Defs
public import Silmaril.X86.Stencils.ByteLoop.Defs
/-! # `Realizes` with call-dependent footprints and results

`Silmaril.Machine.SystemV.Realizes` (integer) and `Silmaril.Machine.SystemV.Abi.Ffi.Realizes`
(`Silmaril.Machine.SystemV.Abi`) take a write footprint, and a result, that depend on the C arguments only. A
function that writes its own stack frame (`right_rot`: sixteen bytes below the entry stack
pointer) or whose result depends on memory (`strlen`: the string length) then gets a
*family* of `Realizes` statements, one per entry stack pointer or length, each with a domain
that pins the index (track A, known problem 1).

`RealizesCall` and `FfiRealizesCall` let the footprint and the result depend on the call
(its entry state). They are new definitions; the ABI model's definitions are unchanged.
`Thms.realizesCall_iff` shows that `Realizes` is the special case of footprints and results
constant in the call, and `Thms.RealizesCall.of_family` collects a family into one statement.

`cstrLen mem s` is the length of the NUL-terminated string at `s` (`0` if there is none),
the call-dependent result of `strlen`.
-/

@[expose] public section
namespace Silmaril.Machine.Abi.CallFootprint

open Silmaril.C.Api (Signature Arguments ReturnValue)
open Silmaril.Machine.SystemV (Call Footprint)
open Silmaril.Machine.SystemV.Abi

/-- An integer System V certificate whose result and write footprint may depend on the call.

**Deprecated as an export** (round 4, the design notes): the
exported certificate of the spec stack is the typed `FfiRealizesCall`. This integer form
is kept for the round-2 `right_rot`/`strlen` families (`Thms`). -/
def RealizesCall (signature : Signature)
    (result : Arguments signature.arguments → Call → ReturnValue signature.result)
    (writes : Arguments signature.arguments → Call → Footprint)
    (domain : Arguments signature.arguments → Call → Prop)
    (execute : Call → Silmaril.X86.MState → Prop) : Prop :=
  ∀ arguments call, Silmaril.C.Api.SysV.Entry signature arguments call →
    domain arguments call → ∃ final, execute call final ∧
      Silmaril.Machine.SystemV.Result signature.result (result arguments call)
        (writes arguments call) call final

/-- A typed FFI certificate (`Silmaril.Machine.SystemV.Abi`) whose result and write footprint may depend on the
call.

**The exported certificate of the spec stack**:
author specs (`Sep.FnSpec`) compile to `FnContract`s, and those export as
`FfiRealizesCall` (`Abi.SpecNotions.contract_export`, `fnSpec_export`). the ABI model's
`Ffi.Realizes` is the call-independent special case (`Thms.ffiRealizesCall_iff`,
`FfiRealizesCall.restrict`). Consumer: rung 12's `len1_composed_abi` carries libmini's
`strlen`/`memcpy` exports in this form. -/
def FfiRealizesCall (signature : Ffi.Signature)
    (result : Ffi.Values signature.arguments → Ffi.Call → Ffi.ResultValue signature.result)
    (writes : Ffi.Values signature.arguments → Ffi.Call → Ffi.Footprint)
    (unaliased : Ffi.Values signature.arguments → Nat → Nat → Prop)
    (domain : Ffi.Values signature.arguments → Ffi.Call → Prop)
    (execute : Ffi.Call → Ffi.State → Prop) : Prop :=
  ∀ arguments call, Ffi.Entry signature arguments call (unaliased arguments) →
    domain arguments call → ∃ final, execute call final ∧
      Ffi.Result signature (result arguments call) (writes arguments call) call final

open Classical in
/-- The length of the NUL-terminated string at `s`, or `0` if there is none. -/
noncomputable def cstrLen (mem : Silmaril.Process.Memory) (s : Nat) : Nat :=
  if h : ∃ k, Silmaril.X86.Stencils.ByteLoop.CStr mem s k then Classical.choose h else 0

end Silmaril.Machine.Abi.CallFootprint
