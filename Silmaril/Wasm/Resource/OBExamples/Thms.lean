module

public import Silmaril.Wasm.Resource.OBExamples.Defs
public import Silmaril.Wasm.Resource.OBClient.Thms
public import Silmaril.Wasm.Resource.Replay.Thms

@[expose] public section

/-!
# Borrowing clients: results

Every profile `P`, by `resource_ob 0 1` (`checkOB_sound`, kernel evaluation):

* `obBorrowUse_ob`: a function that borrows a handle and uses it;
* `obBorrowAlloc_ob`: borrowed and allocated handles in locals of one activation;
* `obSession_ob`: a lending export and an allocating export, every interleaving of calls.

`obFreeBorrow_rejected`: the checker refuses the function that frees its borrowed argument
(refuted semantically by `Silmaril.Wasm.Resource.ReplayExamples.obFreeBorrow_not_ob`).

Frees of owned handles, every profile, by `resource_of 0 1 2` (`checkOF_sound`):

* `obOwnAUF_ob`: borrowed and allocated handles; the allocated one is freed;
* `obKeepFree_ob`: a handle handed over by the environment is used and freed.

Rejected by `checkOF`: `obFreeBorrow_rejectedF` (free of a borrowed handle),
`obFreeTwice_rejectedF` (double free of an owned handle), `obOwnUAF_rejectedF` (use after free).
`obOwnUAF_not_ob` refutes the last one by replay, at every specification profile.
-/

namespace Silmaril.Wasm.Resource.OBExamples

open Silmaril.Wasm.Spec Silmaril.Wasm.Resource Silmaril.Wasm.Resource.OBClient
open Silmaril.Wasm.Resource.ReplayExamples (ρRun ρKeep obFreeBorrow obFreeTwice)
open Silmaril.Wasm.Verify (progOf)
open Silmaril.Wasm.Game (FnType)
open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

/-- **A function that borrows a handle and uses it** is a safe client of the ownership protocol,
every profile. -/
theorem obBorrowUse_ob (P : Profile) :
    Models (protoLogic FnType (List Val) (Behaviour Val) (Option (List (Val × Mode)))) (wasmSem P)
      (progOf obBorrowUse) (obSpec ρRun.toOB) := by
  resource_ob 0 1

/-- **Borrowed and allocated handles in one activation**, every profile. -/
theorem obBorrowAlloc_ob (P : Profile) :
    Models (protoLogic FnType (List Val) (Behaviour Val) (Option (List (Val × Mode)))) (wasmSem P)
      (progOf obBorrowAlloc) (obSpec ρRun.toOB) := by
  resource_ob 0 1

/-- **A lending export and an allocating export**, every profile. -/
theorem obSession_ob (P : Profile) :
    Models (protoLogic FnType (List Val) (Behaviour Val) (Option (List (Val × Mode)))) (wasmSem P)
      (progOf obSession) (obSpec ρRun.toOB) := by
  resource_ob 0 1

/-- Freeing a borrowed handle is rejected by the checker. -/
theorem obFreeBorrow_rejected : checkOB obFreeBorrow 0 1 ρRun = false := by decide +kernel

/-! ## Frees of owned handles -/

/-- **Borrow, allocate, use both, free the allocated handle**: a safe client of the ownership
protocol, every profile. -/
theorem obOwnAUF_ob (P : Profile) :
    Models (protoLogic FnType (List Val) (Behaviour Val) (Option (List (Val × Mode)))) (wasmSem P)
      (progOf obOwnAUF) (obSpec ρRun.toOB) := by
  resource_of 0 1 2

/-- **A handle handed over is used and freed**, every profile. -/
theorem obKeepFree_ob (P : Profile) :
    Models (protoLogic FnType (List Val) (Behaviour Val) (Option (List (Val × Mode)))) (wasmSem P)
      (progOf obKeepFree) (obSpec ρKeep.toOB) := by
  resource_of 0 1 2

/-- Freeing a borrowed handle is rejected by the checker with frees. -/
theorem obFreeBorrow_rejectedF : checkOF obFreeBorrow 0 1 2 ρRun = false := by decide +kernel

/-- Freeing an owned handle twice is rejected. -/
theorem obFreeTwice_rejectedF : checkOF obFreeTwice 0 1 2 ρKeep = false := by decide +kernel

/-- A use after free of an owned handle is rejected. -/
theorem obOwnUAF_rejectedF : checkOF obOwnUAF 0 1 2 ρRun = false := by decide +kernel

/-- **`obOwnUAF` uses a freed handle**, every specification profile. -/
theorem obOwnUAF_not_ob (nd : Bool) :
    ¬ Models (protoLogic FnType (List Val) (Behaviour Val) (Option (List (Val × Mode))))
      (wasmSem (Silmaril.Wasm.Numerics.Profile.spec nd {})) (progOf obOwnUAF) (obSpec ρRun.toOB) := by
  resource_refute_ob

end Silmaril.Wasm.Resource.OBExamples
