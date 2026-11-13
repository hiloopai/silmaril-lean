module

public import Silmaril.Wasm.Det.Shared.Thms
public import Silmaril.Wasm.Det.NoMem.Litmus.Thms

/-!
# Litmus: a deterministic module under a store-writing host

The module `gcMod` of `Silmaril.Wasm.Det.NoMem.Litmus` (`box`: `struct.new`, `struct.get`, a call
of the import `h`, `i32.add`; `twice`: two calls of `box`) passes the direct-mode check on
`{0, 1, 3}`. So, at every profile, against **every host that keeps the function instances** (it
may write the heap, including the struct `box` allocated, globals, tables and memories):

* `box_detS`: every invocation of `box` in `gcStore` is `DetCfgS`;
* `gc_detModuleS`: `box` and `twice` are deterministic at every store with `gcStore`'s functions
  (`DetModuleS`), whatever the host wrote;
* `gc_detModOn`: the store-passing strategy of every scalar instance whose exports are among
  `{0, 1, 3}` is deterministic modulo traps on the plays whose questions carry stores with
  `gcStore`'s functions and whose answers keep them.

`box_detCall_old` recovers the store-free `DetCall` (`DetCfgS.detCfg`).

New theorems.
-/

public section

namespace Silmaril.Wasm.Det.Shared.Litmus

open Silmaril.Wasm.Game Silmaril.Wasm.Det.Core Silmaril.Wasm.Det.Game Silmaril.Wasm.Det.Shared
  Silmaril.Wasm.Det.NoMem.Litmus Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

theorem gc_closB : Silmaril.Wasm.Det.NoMem.closB gcStore [0, 1, 3] = true := by decide +kernel

/-- **`box` and `twice` are deterministic against store-writing hosts**, every profile. -/
theorem gc_detModuleS (P : Profile) :
    DetModuleS P KeepFuncs (fun s => s.funcs = gcStore.funcs) (· ∈ [0, 1, 3]) :=
  detModuleS_of_closB gc_closB

/-- **Every invocation of `box` is deterministic against store-writing hosts.** -/
theorem box_detS (P : Profile) (vs : List Val) : DetCfgS P KeepFuncs (invoke gcStore 1 vs) :=
  gc_detModuleS P gcStore rfl 1 (by decide) vs

/-- The store-free reading is the special case of answers in the store of the call. -/
theorem box_detCall_old (P : Profile) (vs : List Val) : DetCall P gcStore 1 vs :=
  DetCfgS.detCfg (A := KeepFuncs) (fun _ => rfl) (box_detS P vs)

/-- **The game reading**: for every scalar instance whose exports are among `{0, 1, 3}`. -/
theorem gc_detModOn (P : Profile) (I : ScalarInstance) (hI : ∀ j, I.addr j ∈ [0, 1, 3]) :
    DetModOn (ShOk I KeepFuncs (fun s => s.funcs = gcStore.funcs)) (shTraps I.exports)
      (I.shStrategy P) := by
  refine detModOn_shStrategy fun s hs a ha vs => ?_
  obtain ⟨j, rfl⟩ := ha
  exact gc_detModuleS P s hs _ (hI j) vs

end Silmaril.Wasm.Det.Shared.Litmus
