module

public import Silmaril.Wasm.Det.Link.Thms
public import Silmaril.Wasm.Game.Linking.Store.Thms
import Silmaril.Proofs.Wasm.Det.Link.Store

/-!
# Determinism of the linked store: the shared-world step (step A)

For a static link `S : Linking.Setup` in the scalar fragment (`S.Scalar`), at **every** profile:

* `linked_callReach_shared`: every call state of the linked store (reached by finished export
  calls, traps included) is related by silmaril-lean's linker relation
  (`StoreRelation.Related`) to a well-typed call state of the shared world (provider and
  consumer instantiated separately in one store);
* `linked_detModule_of_shared`: `DetModule` of the shared store at the exports gives `DetModule`
  of the linked store at the exports: equal outputs **and equal stores**, at every call state,
  including call states after trapped calls;
* `linked_statelessModule_of_shared`: the same for `StatelessModule`.

Both worlds are closed (no host function), so runs have no import call and stops are results.
The proof reverse-simulates each linked run by a shared run with the same result
(`linker_steps_reflect`, from `reachReverse_all`) and recovers the linked final store from the
shared one and the unchanged function instances (`linker_target_eq`).

This is step A of the store-level transfer from the parts. Step B (determinism of the shared
store from `DetModule` of the provider and of the consumer with stubs) is **not** proved; see
`docs/projects/wasm-wasi.md`.

Proofs: `Silmaril.Proofs.Wasm.Det.Link.Store`. New theorems.
-/

public section

namespace Silmaril.Wasm.Det.Link

open Silmaril.Wasm.Game Silmaril.Wasm.Game.Linking Silmaril.Wasm.Det.Core Silmaril.Wasm.Det.Game
  Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Link.GC
open Silmaril.Wasm.Numerics (Profile)

variable {P : Profile} (S : Setup)

/-- Every call state of the linked store is related to a typed call state of the shared
store. -/
theorem linked_callReach_shared (hS : S.Scalar) {E : Nat → Prop} {s' : Store Nat}
    (h : CallReach P E S.sl s') :
    ∃ s, CallReach P E S.sc s ∧ StoreRelation.Related s s' ∧ StoreOk s :=
  Silmaril.Proofs.Wasm.Det.Link.Store.callReach_shared S hS h

/-- **Step A, store level**: determinism of the shared store gives determinism of the linked
store (outputs and stores, at every call state). -/
theorem linked_detModule_of_shared (hS : S.Scalar) (hD : DetModule P (entry S.sharedI) S.sc) :
    DetModule P (entry S.linkedI) S.sl :=
  Silmaril.Proofs.Wasm.Det.Link.Store.linked_detModule_of_shared S hS hD

/-- **Step A, store level, statelessness.** -/
theorem linked_statelessModule_of_shared (hS : S.Scalar)
    (hD : StatelessModule P (entry S.sharedI) S.sc) : StatelessModule P (entry S.linkedI) S.sl :=
  Silmaril.Proofs.Wasm.Det.Link.Store.linked_statelessModule_of_shared S hS hD

end Silmaril.Wasm.Det.Link
