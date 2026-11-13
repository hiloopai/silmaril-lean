module

public import Silmaril.Wasm.Resource.ClientExamples.Defs
public import Silmaril.Wasm.Resource.Client.Thms
public import Silmaril.Wasm.Resource.ClientArg.Thms
public import Silmaril.Wasm.Resource.Replay.Thms
public import Silmaril.Wasm.Resource.ReplayExamples.Defs

@[expose] public section

/-!
# Clients of the handle protocol checked by the typestate verifier: results

Every profile `P`, by `resource_client [(0, 1)]` (`checkClient_sound`, kernel evaluation):

* `cliAUF_client`: allocate, use, free in one export call;
* `cliSession_client`: allocation in `a`, use in `b`, flag cleared and free in `c`, for every play
  (every interleaving of export calls, every environment).

`cliUAF_rejected`, `cliDoubleFree_rejected`: the checker returns `false` on use after free and
double free (a refusal of the checker, not a semantic refutation).

Handles in locals, every profile, by `resource_client` (no global pairs):

* `cliLocal_client`, `cliLocalHelper_client` (the handle in the callee's local),
  `cliLocalTwo_client`;
* `cliUaf_rejected`, `cliDoubleFree_rejected'`: the checker refuses the local-variable use after
  free and double free of `Silmaril.Wasm.Resource.ReplayExamples`, which are refuted semantically
  there (`cliUaf_not_client`, `cliDoubleFree_not_client`).

Handles passed to an internal callee (`Silmaril.Wasm.Resource.ClientArg`), every profile, by
`resource_client_arg [4]`:

* `cliArg_client`: a handle allocated, used and handed to a helper that uses and frees it;
* `cliArgUAF_rejected`, `cliArgUAF_not_client`: a freed handle handed to the helper, rejected
  and refuted by replay at every specification profile.
-/

namespace Silmaril.Wasm.Resource.ClientExamples

open Silmaril.Wasm.Spec Silmaril.Wasm.Resource Silmaril.Wasm.Resource.Client
open Silmaril.Wasm.Verify (instOf progOf)
open Silmaril.Wasm.Game (FnType)
open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

theorem cliAUF_imports : 2 < (ifaceOf (instOf cliAUF)).imports.length := by decide +kernel

theorem cliSession_imports : 2 < (ifaceOf (instOf cliSession)).imports.length := by
  decide +kernel

/-- **Allocate, use, free** is a safe client, every profile. -/
theorem cliAUF_client (P : Profile) :
    Models (protoLogic FnType (List Val) (Behaviour Val) (Option (List Val))) (wasmSem P)
      (progOf cliAUF)
      (clientSpec ⟨0, by have := cliAUF_imports; omega⟩ ⟨1, by have := cliAUF_imports; omega⟩
        ⟨2, cliAUF_imports⟩) := by
  resource_client [(0, 1)]

/-- **The session** (allocate in `a`, use in `b`, free in `c`) is a safe client, every profile. -/
theorem cliSession_client (P : Profile) :
    Models (protoLogic FnType (List Val) (Behaviour Val) (Option (List Val))) (wasmSem P)
      (progOf cliSession)
      (clientSpec ⟨0, by have := cliSession_imports; omega⟩
        ⟨1, by have := cliSession_imports; omega⟩ ⟨2, cliSession_imports⟩) := by
  resource_client [(0, 1)]

/-- Use after free is rejected by the checker. -/
theorem cliUAF_rejected : checkClient cliUAF 0 1 2 [(0, 1)] = false := by decide +kernel

/-- Double free is rejected by the checker. -/
theorem cliDoubleFree_rejected : checkClient cliDoubleFree 0 1 2 [(0, 1)] = false := by
  decide +kernel

theorem cliLocal_imports : 2 < (ifaceOf (instOf cliLocal)).imports.length := by decide +kernel

theorem cliLocalHelper_imports : 2 < (ifaceOf (instOf cliLocalHelper)).imports.length := by
  decide +kernel

theorem cliLocalTwo_imports : 2 < (ifaceOf (instOf cliLocalTwo)).imports.length := by
  decide +kernel

/-- **Allocate into a local, use, free** is a safe client, every profile. -/
theorem cliLocal_client (P : Profile) :
    Models (protoLogic FnType (List Val) (Behaviour Val) (Option (List Val))) (wasmSem P)
      (progOf cliLocal)
      (clientSpec ⟨0, by have := cliLocal_imports; omega⟩ ⟨1, by have := cliLocal_imports; omega⟩
        ⟨2, cliLocal_imports⟩) := by
  resource_client

/-- **A handle in the local of a callee frame**, every profile. -/
theorem cliLocalHelper_client (P : Profile) :
    Models (protoLogic FnType (List Val) (Behaviour Val) (Option (List Val))) (wasmSem P)
      (progOf cliLocalHelper)
      (clientSpec ⟨0, by have := cliLocalHelper_imports; omega⟩
        ⟨1, by have := cliLocalHelper_imports; omega⟩ ⟨2, cliLocalHelper_imports⟩) := by
  resource_client

/-- **Two handles in two locals**, every profile. -/
theorem cliLocalTwo_client (P : Profile) :
    Models (protoLogic FnType (List Val) (Behaviour Val) (Option (List Val))) (wasmSem P)
      (progOf cliLocalTwo)
      (clientSpec ⟨0, by have := cliLocalTwo_imports; omega⟩
        ⟨1, by have := cliLocalTwo_imports; omega⟩ ⟨2, cliLocalTwo_imports⟩) := by
  resource_client

/-- Use after free through a local is rejected by the checker. -/
theorem cliUaf_rejected : checkClient ReplayExamples.cliUaf 0 1 2 [] = false := by
  decide +kernel

/-- Double free through a local is rejected by the checker. -/
theorem cliDoubleFree_rejected' : checkClient ReplayExamples.cliDoubleFree 0 1 2 [] = false := by
  decide +kernel

/-! ## Handles passed to internal callees (`Silmaril.Wasm.Resource.ClientArg`) -/

theorem cliArg_imports : 2 < (ifaceOf (instOf cliArg)).imports.length := by decide +kernel

theorem cliArgUAF_imports : 2 < (ifaceOf (instOf cliArgUAF)).imports.length := by
  decide +kernel

/-- **A handle passed to an internal callee**, which uses and frees it: a safe client, every
profile (helper: function `4`). -/
theorem cliArg_client (P : Profile) :
    Models (protoLogic FnType (List Val) (Behaviour Val) (Option (List Val))) (wasmSem P)
      (progOf cliArg)
      (clientSpec ⟨0, by have := cliArg_imports; omega⟩ ⟨1, by have := cliArg_imports; omega⟩
        ⟨2, cliArg_imports⟩) := by
  resource_client_arg [4]

/-- Passing a freed handle to the helper is rejected. -/
theorem cliArgUAF_rejected : Silmaril.Wasm.Resource.ClientArg.checkClientArg cliArgUAF 0 1 2 [] [4] =
    false := by
  decide +kernel

/-- **`cliArgUAF` uses a freed handle inside the callee**, every specification profile. -/
theorem cliArgUAF_not_client (nd : Bool) :
    ¬ Models (protoLogic FnType (List Val) (Behaviour Val) (Option (List Val)))
      (wasmSem (Profile.spec nd {})) (progOf cliArgUAF)
      (clientSpec ⟨0, by have := cliArgUAF_imports; omega⟩
        ⟨1, by have := cliArgUAF_imports; omega⟩ ⟨2, cliArgUAF_imports⟩) := by
  resource_refute_replay

end Silmaril.Wasm.Resource.ClientExamples
