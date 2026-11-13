module

public import Silmaril.Wasm.Component.Reference.Engine.Core3.Typed.Defs

public import Silmaril.Raw.Wasm.Component.Engine.Core3
public import Silmaril.Raw.Wasm.Component.Engine.Core3.Agreement
public import Silmaril.Raw.Wasm.Component.Engine.Core3.Typed.Status
public import Silmaril.Raw.Wasm.Component.Engine.Core3.Typed.Prepare

/-!
# The typed laws of the concrete Core 3.0 engine

`core3Typed o : Core3Engine.TypedLaws (core3 o)` instantiates the abstract typing predicates of
`Core3Engine.TypedLaws` (Engine/Core3.lean) with Core 3.0 typing (`Execution/Core/Typing/*`):

* `StoreOkE s`: the store is well typed (`StoreOk`, the spec's `Store_ok`) and every host
  function of `s` has a flat type (`HostFlat`; canon host functions are allocated by
  `allocHost` at `ofFlatType ft`);
* `Ext s s'`: typed store extension `Extend s s'` (the spec's `Extend_store`);
* `ThreadOkE s t rs`: the thread's configuration is typed with the numeric result types `rs`
  (`SingleThreaded.ThreadOk s t (rs.map Ty.num)`, i.e. `Config_ok`);
* `HostTypedE s h ft`: every host function of `s` with code `h` has type `ofFlatType ft` (vacuous
  while there is none).

Each law is a separate theorem in the namespace `Core3.Typed`, named after the field it
discharges. The laws about internal steps, status and resumption go through the agreement with
the single-threaded machine (Engine/Core3/Agreement.lean: `core3_internal_sound`, `statusE_eq`)
and its soundness theorems (`SingleThreaded.status_ne_stuck`, `SingleThreaded.Internal.preserves`,
`SingleThreaded.resume_typed`); internal steps never change the function instances
(`SingleThreaded.Internal.funcs_prefix`), so host typing persists. Flat results and callout
arguments, trap resumption (Engine/Core3/Typed/Status.lean), host allocation, memory writes,
threads in extended stores (Engine/Core3/Typed/Store.lean) and instantiation
(Engine/Core3/Typed/Prepare.lean) are proved from Core 3.0 progress and preservation
(`Config.progress`, `Step.preservation`, `Instantiate.ok`, `invoke_ok`). `running_progress` holds
without typing (`statusE_running_step`). `prepare_ok` does not use its validity and
import-matching hypotheses: `prepareE?` checks both itself (`validate?`, `externAddrsOk?`).
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Engine.Core3

open Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation

variable {H : Type}

/-! ## The typing predicates -/

/-! ## Progress of running threads (no typing needed) -/

/-! ## Host typing and the store's functions -/

/-! ## The laws, one per field of `Core3Engine.TypedLaws` -/

namespace Typed

end Typed

end Silmaril.Wasm.Component.Engine.Core3

namespace Silmaril.Wasm.Component.Engine

open Silmaril.Wasm.Execution.Core Core3

end Silmaril.Wasm.Component.Engine
