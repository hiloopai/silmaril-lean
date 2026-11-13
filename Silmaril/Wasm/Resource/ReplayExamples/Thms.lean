module

public import Silmaril.Wasm.Resource.ReplayExamples.Defs
public import Silmaril.Wasm.Resource.Replay.Thms

@[expose] public section

/-!
# Replaying environment answers: examples (results)

Refutations at every specification profile `Profile.spec nd {}`, by kernel evaluation of the
replay refuter (the environment answers `alloc` with the handle `7`, `use`/`free` with nothing):

* `cliUaf_not_client`: use after free (`resource_refute_replay`);
* `cliDoubleFree_not_client`: double free;
* `obFreeBorrow_not_ob`: a borrowed handle dropped (`resource_refute_ob`; the first import call
  is the bad one);
* `obFreeTwice_not_ob`: an owned handle dropped twice (through the answer to the first `free`).
-/

namespace Silmaril.Wasm.Resource.ReplayExamples

open Silmaril.Wasm.Spec Silmaril.Wasm.Resource Silmaril.Wasm.Verify Silmaril.Wasm.Game
open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

theorem cliUaf_imports : 2 < (ifaceOf (instOf cliUaf)).imports.length := by
  decide +kernel

theorem cliDoubleFree_imports : 2 < (ifaceOf (instOf cliDoubleFree)).imports.length := by
  decide +kernel

/-- **`cliUaf` uses a handle after freeing it**, every specification profile. -/
theorem cliUaf_not_client (nd : Bool) :
    ¬ Models (protoLogic FnType (List Val) (Behaviour Val) (Option (List Val)))
      (wasmSem (Profile.spec nd {})) (progOf cliUaf)
      (clientSpec ⟨0, by have := cliUaf_imports; omega⟩ ⟨1, by have := cliUaf_imports; omega⟩
        ⟨2, cliUaf_imports⟩) := by
  resource_refute_replay

/-- **`cliDoubleFree` frees a handle twice**, every specification profile. -/
theorem cliDoubleFree_not_client (nd : Bool) :
    ¬ Models (protoLogic FnType (List Val) (Behaviour Val) (Option (List Val)))
      (wasmSem (Profile.spec nd {})) (progOf cliDoubleFree)
      (clientSpec ⟨0, by have := cliDoubleFree_imports; omega⟩
        ⟨1, by have := cliDoubleFree_imports; omega⟩ ⟨2, cliDoubleFree_imports⟩) := by
  resource_refute_replay

/-- **`obFreeBorrow` drops a borrowed handle**, every specification profile. -/
theorem obFreeBorrow_not_ob (nd : Bool) :
    ¬ Models (protoLogic FnType (List Val) (Behaviour Val) (Option (List (Val × Mode))))
      (wasmSem (Profile.spec nd {})) (progOf obFreeBorrow) (obSpec ρRun.toOB) := by
  resource_refute_ob

/-- **`obFreeTwice` drops an owned handle twice**, every specification profile. -/
theorem obFreeTwice_not_ob (nd : Bool) :
    ¬ Models (protoLogic FnType (List Val) (Behaviour Val) (Option (List (Val × Mode))))
      (wasmSem (Profile.spec nd {})) (progOf obFreeTwice) (obSpec ρKeep.toOB) := by
  resource_refute_ob

end Silmaril.Wasm.Resource.ReplayExamples
