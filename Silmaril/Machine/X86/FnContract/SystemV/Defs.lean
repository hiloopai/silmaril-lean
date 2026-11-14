module

public import Silmaril.Machine.X86.FnContract.Defs
public import Silmaril.Machine.SystemV.Defs
public import Silmaril.Machine.SystemV.Abi.Ffi.Defs
public import Silmaril.Machine.X86.Decompile.Cert.Defs

/-!
# Function contracts: the System V and decompilation bridges (definitions)

The parts of the contract layer that depend on ports not included here: the
System V ABI model (`Silmaril.Machine.SystemV.Abi.Ffi`, which pulls the Cerberus
port), the integer `Silmaril.Machine.SystemV.Realizes` and the `Decompile` certificates.

* `FnContract.decompiledSpec`: the spec of a decompilation certificate;
* `Open.ffiExecute`: the execution relation of a typed FFI call on the open machine.

The theorems (`toRealizes`, `toFfiRealizes`, `ofDecompiled`) are in `SystemV/Thms.lean`.
Before the split these lived in `FnContract.{Defs,Thms}`; the names are unchanged.
-/

@[expose] public section

namespace Silmaril.Machine.X86

open Silmaril.X86 (State MState Word Byte Reg sysv64)
open Silmaril.Process (Memory)
open Silmaril.Machine.Execution (Reaches)

namespace FnContract

/-- The spec of a decompilation certificate: some entry address satisfies the certificate's
precondition with the entry state's return address as exit; the postcondition is the
certificate's, applied to the decompiled function's value. -/
def decompiledSpec {α β : Type} (Pre : Word → Word → MState → Prop) (args : MState → α)
    (f : α → β) (Post : β → MState → MState → Prop) (footprint : MState → Nat → Prop) :
    Spec MState where
  entry m := ∃ e, Pre e (Open.retOf m.core m.memory) m
  footprint := footprint
  post m fin := Post (f (args m)) m fin

end FnContract

namespace Open

/-- The execution relation of a typed FFI call on the open machine. The integer machine runs
from the call's initial machine state; the vector, x87 and control state that `X86.Ext` and
`Ext8` do not model is carried unchanged. This is a modelling choice, sound for code that
the integer model decodes (it has no instruction touching that state); it is not a semantics
of the extended state. -/
def ffiExecute (call : Silmaril.Machine.SystemV.Abi.Ffi.Call)
    (final : Silmaril.Machine.SystemV.Abi.Ffi.State) : Prop :=
  Reaches step call.initial.machine final.machine ∧
    final = { call.initial with machine := final.machine }

end Open

end Silmaril.Machine.X86
