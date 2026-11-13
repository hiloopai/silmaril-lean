module

public import Silmaril.Machine.Abi.OpenMachine.Defs
public import Silmaril.X86.FnContract.Must.Defs
/-!
# The ABI call relation of a relational machine (`callModelR`)


`OpenMachine.callModel` is the first-return call relation of the deterministic open machine
`Open.step`. Its demonic reading (`Contracts.Sat`: some outcome, and every outcome meets the
post) was justified by determinism (`OpenMachine.callModel_subsingleton`). This file states the
same call relation for **any** relational machine `A : RelIsa MState`
(`Silmaril.X86.RelIsa`):

* `RunsInR` (P1) replaces `OpenMachine.RunsIn`, and `FnContract.ReturnedV` (P2) replaces
  `OpenMachine.Returned`;
* `FirstReturnR A s t`: `t` is the first returned state of *some* run of `A` from `s`;
* `callModelR A`: the outcomes from an FFI state `s` are the first returns of every run of `A`
  from `s.machine`, with the FFI-only state carried unchanged, exactly as in `callModel`.

A nondeterministic `A` can give several outcomes. `Contracts.Sat (callModelR A)` then asks that
every one of them meets the post; the theorems (`Rel/Thms.lean`) get that from a demonic
contract `FnContract.Spec.Must`, without a subsingleton argument.

No declaration here is named `Convention`, and this file does not open
`Silmaril.Compile.Category`.
-/

@[expose] public section
namespace Silmaril.Machine.Abi.OpenMachine

open Silmaril.X86 (MState)
open Silmaril.Logic.Institution.Bridges
open Silmaril.Machine.SystemV.Abi (Ffi.State)
open Silmaril.X86

/-- `t` is the first returned state of some run of the relational machine `A` from `s`: a run
whose every step is taken from a state that is not a return of the call entered at `s`, and
that ends returned. -/
def FirstReturnR (A : RelIsa MState) (s t : MState) : Prop :=
  RelIsa.RunsInR A (fun m => ¬ FnContract.ReturnedV A.toViews s m) s t ∧
    FnContract.ReturnedV A.toViews s t

/-- **The call relation of a relational machine** on FFI states: the first returns of every
run, with the FFI-only state carried unchanged. -/
def callModelR (A : RelIsa MState) : Contracts.Model Ffi.State Ffi.State := fun s =>
  {t | FirstReturnR A s.machine t.machine ∧ t = { s with machine := t.machine }}

end Silmaril.Machine.Abi.OpenMachine
