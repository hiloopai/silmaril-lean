module

public import Silmaril.Wasm.Det.Shared.Untyped.Defs
public import Silmaril.Wasm.Det.Shared.Thms
public import Silmaril.Wasm.Game.Untyped.Thms
import Silmaril.Proofs.Wasm.Det.Shared.Untyped

/-!
# Determinism under store-writing hosts: the untyped game (theorems)

Every statement holds at an arbitrary profile `P`.

* `detModOn_uStrategy`: if every export invocation of the untyped instance `U` in every store of
  `S` is `DetCfgS P A`, the untyped store-passing strategy `U.strategy P` of
  `Silmaril.Wasm.Game.Untyped` is deterministic modulo traps (`uTraps`) on the plays whose export
  questions carry stores of `S` and whose import answers carry stores admissible for their
  question (`UOk U A S`). Interfaces are arbitrary: arguments, results and answers are raw Core
  values, references included.
* `uStrategy_detModOn_storeB`: for **every** untyped instance, on plays whose questions carry
  stores of the memory-free subset (`storeB`) and whose answers keep the function instances.

Proofs: `Silmaril.Proofs.Wasm.Det.Shared.Untyped` (the twin relation of the store-passing game,
over the untyped hidden states). New theorems.
-/

public section

namespace Silmaril.Wasm.Det.Shared

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Det.Core Silmaril.Wasm.Det.Game
  Silmaril.Wasm Silmaril.Wasm.Execution.Core
open Silmaril.Wasm.Numerics (Profile)

variable {P : Profile} {A : Store Nat → Store Nat → Prop}

/-- **A module deterministic against store-writing hosts has a deterministic untyped
store-passing strategy** on admissible plays. -/
theorem detModOn_uStrategy {U : UInstance} {S : Store Nat → Prop}
    (hD : DetModuleS P A S (uEntry U)) :
    DetModOn (UOk U A S) (uTraps U.X) (U.strategy P) :=
  Silmaril.Proofs.Wasm.Det.Shared.Untyped.detModOn_uStrategy fun f hf =>
    hD _ hf _ ⟨f.target, rfl⟩ _

/-- **Every untyped instance**: the untyped store-passing strategy is deterministic modulo traps
on plays whose questions carry stores of the memory-free subset and whose answers keep the
functions. -/
theorem uStrategy_detModOn_storeB (U : UInstance) (P : Profile) :
    DetModOn (UOk U KeepFuncs (fun s => Silmaril.Wasm.Det.NoMem.storeB s = true))
      (uTraps U.X) (U.strategy P) :=
  detModOn_uStrategy (detModuleS_of_storeB _)

end Silmaril.Wasm.Det.Shared
