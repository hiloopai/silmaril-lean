module

public import Silmaril.Wasm.Resource.Examples.Defs
public import Silmaril.Proofs.Wasm.Resource.Examples.Basic
public import Silmaril.Wasm.Resource.Check.Thms
public import Silmaril.Wasm.Resource.Component.Thms
public import Silmaril.Wasm.Spec.Component.Litmus.Defs

@[expose] public section

/-!
# Resource protocols: examples (results)

Loose traces (`decide` on the protocol automaton, through `models_progOf_proto_iff`):

* client: `sessionsRun_client` (alloc / use / free across three export calls), negatives
  `uafRun_not_client`, `doubleFreeRun_not_client`, `freeNeverRun_not_client`; blame:
  `envReuseRun_client` (the environment reallocated a live handle, so the program is not blamed);
* provider: `provRun_provider`, `provTwiceRun_not_provider`, `provClientBad_provider` (the client
  freed a dead handle first: environment fault);
* ownership: `borrowRun_ob`, `transferRun_ob`, negatives `dropBorrowRun_not_ob`,
  `outliveRun_not_ob`, `giveRun_not_ob`;
* `externref` handles (untyped moves): `exRun_accepted`, `exUafRun_rejected`;
* components: `handleRun_nud`, `useAfterDrop_not_nud` (the protocol `nudProto`, decided), and
  `handleRun_noUseAfterDrop'`, `useAfterDrop_not_noUseAfterDrop'`: the component logic
  `noUseAfterDrop` decided through `models_noUseAfterDrop_iff`.

Real Core 3.0 modules (every specification profile for refutations, every profile for proofs):

* `cliUseBefore_not_client`: `run` uses handle `7` before any allocation (refuted by the
  first-call refuter, `resource_refute`);
* `cliFreeNever_not_client`: `run` frees the never-allocated handle `7`;
* `cliAllocOnly_client`: the client sentence holds (only dead code uses or frees; proved by the
  call-graph verifier, `resource_check`).
-/

namespace Silmaril.Wasm.Resource.Examples

open Silmaril.Wasm.Spec Silmaril.Wasm.Spec.Litmus Silmaril.Wasm.Resource Silmaril.Wasm.Verify Silmaril.Wasm.Game
open Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

/-- The client sentence on `Xh`. -/
abbrev cli : Protocol (Option (List Val)) (Ev Xh) := clientSpec iA iU iF
/-- The provider sentence on `Xp`. -/
abbrev prov : Protocol (Option (List Val)) (Ev Xp) := providerSpec pA pU pF
/-- The ownership sentence on `Xo`. -/
abbrev ob : Protocol (Option (List (Val × Mode))) (Ev Xo) := obSpec ρo

/-- The loose litmus semantics. -/
abbrev LS : Semantics Unit (List Val) (Behaviour Val) := Semantics.ofSets Unit (List Val) (Behaviour Val)

abbrev PL (S : Type) : Logic Unit (List Val) (Behaviour Val) := protoLogic Unit (List Val) (Behaviour Val) S

/-! ## Client -/

theorem sessionsRun_client : Models (PL _) LS (progOf sessionsRun) cli := by
  rw [models_progOf_proto_iff]; decide

theorem uafRun_not_client : ¬ Models (PL _) LS (progOf uafRun) cli := by
  rw [models_progOf_proto_iff]; decide

theorem doubleFreeRun_not_client : ¬ Models (PL _) LS (progOf doubleFreeRun) cli := by
  rw [models_progOf_proto_iff]; decide

theorem freeNeverRun_not_client : ¬ Models (PL _) LS (progOf freeNeverRun) cli := by
  rw [models_progOf_proto_iff]; decide

theorem envReuseRun_client : Models (PL _) LS (progOf envReuseRun) cli := by
  rw [models_progOf_proto_iff]; decide

/-! ## Provider -/

theorem provRun_provider : Models (PL _) LS (progOf provRun) prov := by
  rw [models_progOf_proto_iff]; decide

theorem provTwiceRun_not_provider : ¬ Models (PL _) LS (progOf provTwiceRun) prov := by
  rw [models_progOf_proto_iff]; decide

theorem provClientBad_provider : Models (PL _) LS (progOf provClientBad) prov := by
  rw [models_progOf_proto_iff]; decide

/-! ## Ownership and borrowing -/

theorem borrowRun_ob : Models (PL _) LS (progOf borrowRun) ob := by
  rw [models_progOf_proto_iff]; decide

theorem transferRun_ob : Models (PL _) LS (progOf transferRun) ob := by
  rw [models_progOf_proto_iff]; decide

theorem dropBorrowRun_not_ob : ¬ Models (PL _) LS (progOf dropBorrowRun) ob := by
  rw [models_progOf_proto_iff]; decide

theorem outliveRun_not_ob : ¬ Models (PL _) LS (progOf outliveRun) ob := by
  rw [models_progOf_proto_iff]; decide

theorem giveRun_not_ob : ¬ Models (PL _) LS (progOf giveRun) ob := by
  rw [models_progOf_proto_iff]; decide

/-! ## `externref` handles -/

theorem exRun_accepted : (uClientSpec 0 1 2).acceptsB exRun = true := by decide

theorem exUafRun_rejected : (uClientSpec 0 1 2).acceptsB exUafRun = false := by decide

/-! ## Components -/

open Silmaril.Wasm.Spec.Component Silmaril.Wasm.Spec.Component.Litmus in
theorem handleRun_nud : (nudProto dropE).acceptsB handleRun = true := by decide

open Silmaril.Wasm.Spec.Component Silmaril.Wasm.Spec.Component.Litmus in
theorem useAfterDrop_not_nud : (nudProto dropE).acceptsB useAfterDrop = false := by decide

open Silmaril.Wasm.Spec.Component Silmaril.Wasm.Spec.Component.Litmus in
/-- **The component logic decided through its protocol**: the litmus program of `handleRun`
satisfies `noUseAfterDrop dropE` (by `models_noUseAfterDrop_iff` and the automaton). -/
theorem handleRun_noUseAfterDrop' :
    Models noUseAfterDrop (Semantics.ofSets CFn (List RVal) Outcome)
      (⟨prefixesOf handleRun, prefixesOf_good _⟩ : (Semantics.ofSets CFn (List RVal) Outcome).Prog Silmaril.Wasm.Spec.Component.Litmus.Xh)
      dropE := by
  rw [models_noUseAfterDrop_iff, models_iff]
  exact (sat_prefixesOf_iff handleRun (nudProto dropE)).2 (by decide)

open Silmaril.Wasm.Spec.Component Silmaril.Wasm.Spec.Component.Litmus in
/-- … and the program of `useAfterDrop` does not. -/
theorem useAfterDrop_not_noUseAfterDrop' :
    ¬ Models noUseAfterDrop (Semantics.ofSets CFn (List RVal) Outcome)
      (⟨prefixesOf useAfterDrop, prefixesOf_good _⟩ :
        (Semantics.ofSets CFn (List RVal) Outcome).Prog Silmaril.Wasm.Spec.Component.Litmus.Xh) dropE := by
  rw [models_noUseAfterDrop_iff, models_iff, sat_prefixesOf_iff]
  decide

/-! ## Real Core 3.0 clients -/

theorem cliUseBefore_imports : 2 < (ifaceOf (instOf cliUseBefore)).imports.length := by
  decide +kernel

theorem cliFreeNever_imports : 2 < (ifaceOf (instOf cliFreeNever)).imports.length := by
  decide +kernel

theorem cliAllocOnly_imports : 2 < (ifaceOf (instOf cliAllocOnly)).imports.length := by
  decide +kernel

/-- **`cliUseBefore` uses a handle before allocating it**, every specification profile. -/
theorem cliUseBefore_not_client (nd : Bool) :
    ¬ Models (protoLogic FnType (List Val) (Behaviour Val) (Option (List Val)))
      (wasmSem (Profile.spec nd {})) (progOf cliUseBefore)
      (clientSpec ⟨0, by have := cliUseBefore_imports; omega⟩
        ⟨1, by have := cliUseBefore_imports; omega⟩
        ⟨2, cliUseBefore_imports⟩) := by
  resource_refute

/-- **`cliFreeNever` frees a never-allocated handle**, every specification profile. -/
theorem cliFreeNever_not_client (nd : Bool) :
    ¬ Models (protoLogic FnType (List Val) (Behaviour Val) (Option (List Val)))
      (wasmSem (Profile.spec nd {})) (progOf cliFreeNever)
      (clientSpec ⟨0, by have := cliFreeNever_imports; omega⟩
        ⟨1, by have := cliFreeNever_imports; omega⟩ ⟨2, cliFreeNever_imports⟩) := by
  resource_refute

/-- **`cliAllocOnly` is a safe client**, every profile. -/
theorem cliAllocOnly_client (P : Profile) :
    Models (protoLogic FnType (List Val) (Behaviour Val) (Option (List Val))) (wasmSem P)
      (progOf cliAllocOnly)
      (clientSpec ⟨0, by have := cliAllocOnly_imports; omega⟩
        ⟨1, by have := cliAllocOnly_imports; omega⟩ ⟨2, cliAllocOnly_imports⟩) := by
  resource_check

end Silmaril.Wasm.Resource.Examples
