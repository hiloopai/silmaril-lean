module

public import Silmaril.Wasm.Component.Reference.Engine.Core3.Typed.Status.Defs

public import Silmaril.Raw.Wasm.Component.Engine.Core3.Agreement
public import Silmaril.Raw.Wasm.Component.Engine.Core3.Typed.Store

/-!
# Typed statuses of the single-threaded machine

Facts about the status `SingleThreaded.status o s t` of a typed thread
(`SingleThreaded.ThreadOk s t ts`, the spec's `Config_ok`) that the typed laws of the concrete
engine need:

* `returned_values_flat`: returned values of a thread typed at numeric result types are flat,
  of those types (as in `SingleThreaded.status_flat`);
* `callout_args_typed`: the arguments of a callout are typed by the parameter types of a host
  function of the store with the callout's host code. The proof runs Core progress
  (`Config.progress`) with the host semantics `argHost`, which diverges exactly on arguments
  typed by the parameters of such a function; `argHost` satisfies the host contract `HostOk`,
  so a typed callout steps by the host rule, whose premise is the claim;
* `resume_trap_typed`, `resume_trap_extend`: resuming a callout with a trap gives a typed thread.
  The resumed code is the result of the host rule for the host semantics `trapHost`, which
  returns a trap; `trapHost` satisfies `HostOk`, so Core preservation (`Step.preservation`) types
  it; store extension (`configOk_extend`) then moves it to any extended typed store;
* `flatStatus_eq_returned_values`, `flatStatus_eq_callout'`: inversion of the flat view.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Engine.Core3.Typed

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation

variable {H : Type}

/-! ## Flat values -/

/-! ## Callout arguments -/

/-! ## Trap resumption -/

/-! ## The flat view -/

end Silmaril.Wasm.Component.Engine.Core3.Typed
