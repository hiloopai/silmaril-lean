module

public import Silmaril.Wasm.Det.Shared.Defs
public import Silmaril.Wasm.Det.Core.Thms
public import Silmaril.Wasm.Det.NoMem.Thms
public import Silmaril.Wasm.Game.Shared.Thms
import Silmaril.Proofs.Wasm.Det.Shared.Game

/-!
# Determinism under store-writing hosts: theorems

Every statement holds at an arbitrary profile `P`.

* `DetCfgS.detCfg`: with a reflexive admissibility relation, determinism against store-writing
  answers gives the store-free `Silmaril.Wasm.Det.Core.DetCfg` (the old oracle is the special case
  where the returned store is the store at the call).
* `detCfgS_of_closed`: an invariant closed under host-free steps and under resumption in every
  admissible store, whose host-free runs reach at most one non-trapping stop, gives `DetCfgS`.
* `closedS_noMem`, `detModuleS_of_storeB`, `detModuleS_of_closB`: the memory-free subset
  (`Silmaril.Wasm.Det.NoMem`) is deterministic against every host that keeps the function
  instances (`KeepFuncs`; it may write memories, tables, globals and the heap).
* `detModOn_shStrategy` (**the game reading**): if every export invocation in every store of
  `S` is `DetCfgS P A`, the store-passing strategy `I.shStrategy P` of
  `Silmaril.Wasm.Game.Shared` is deterministic modulo traps on the plays whose export questions
  carry stores of `S` and whose import answers carry stores admissible for their question
  (`ShOk I A S`). The proof is a forward twin relation over the store-passing hidden-state system
  (`Silmaril.Proofs.Wasm.Det.Shared.ShTwin`) whose traces carry answers and returned stores.
* `shStrategy_detModOn_storeB`: for **every** scalar instance and every profile, the store-passing
  strategy is deterministic modulo traps on plays whose questions carry stores passing `storeB`
  and whose answers keep the function instances.

The plays are restricted because a question may carry any store, including one whose export
address holds a nondeterministic function, and an answer may replace the function instances.

Proofs: `Silmaril.Proofs.Wasm.Det.Shared.{Basic,Game}`. New theorems.
-/

public section

namespace Silmaril.Wasm.Det.Shared

open Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm.Det.Core Silmaril.Wasm.Det.Game
  Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.SingleThreaded
open Silmaril.Wasm.Numerics (Profile)

variable {P : Profile} {A : Store Nat → Store Nat → Prop}

theorem DetCfgS.detCfg (hA : ∀ s, A s s) {c : Config Nat} (hD : DetCfgS P A c) : DetCfg P c :=
  Silmaril.Proofs.Wasm.Det.Shared.DetCfgS.detCfg hA hD

theorem detCfgS_of_closed {Inv : Config Nat → Prop} (hI : ClosedS P A Inv)
    (hS : ∀ c, Inv c → SegDet P c) {c : Config Nat} (hc : Inv c) : DetCfgS P A c :=
  Silmaril.Proofs.Wasm.Det.Shared.detCfgS_of_closed hI hS hc

theorem closedS_noMem {q : Nat → Bool} {ind : Bool} (P : Profile) :
    ClosedS P KeepFuncs (Silmaril.Wasm.Det.NoMem.Inv q ind) :=
  Silmaril.Proofs.Wasm.Det.Shared.closedS_noMem P

/-- **Full mode**: every function of a store passing `storeB` is deterministic against every
host keeping the function instances. -/
theorem detModuleS_of_storeB (Entry : Nat → Prop) :
    DetModuleS P KeepFuncs (fun s => Silmaril.Wasm.Det.NoMem.storeB s = true) Entry :=
  Silmaril.Proofs.Wasm.Det.Shared.detModuleS_of_storeB Entry

/-- **Direct mode**: the functions of `L` are deterministic against every host keeping the
function instances, at every store with the functions of a store passing `closB s₀ L`. -/
theorem detModuleS_of_closB {s₀ : Store Nat} {L : List Nat}
    (h : Silmaril.Wasm.Det.NoMem.closB s₀ L = true) :
    DetModuleS P KeepFuncs (fun s => s.funcs = s₀.funcs) (· ∈ L) :=
  Silmaril.Proofs.Wasm.Det.Shared.detModuleS_of_closB h

/-- **A module deterministic against store-writing hosts has a deterministic store-passing
strategy** on admissible plays. -/
theorem detModOn_shStrategy {I : ScalarInstance} {S : Store Nat → Prop}
    (hD : DetModuleS P A S (entry I)) :
    DetModOn (ShOk I A S) (shTraps I.exports) (I.shStrategy P) :=
  Silmaril.Proofs.Wasm.Det.Shared.detModOn_shStrategy fun f hf => hD _ hf _ ⟨f.1, rfl⟩ _

/-- **Every scalar instance**: the store-passing strategy is deterministic modulo traps on plays
whose questions carry stores of the memory-free subset and whose answers keep the functions. -/
theorem shStrategy_detModOn_storeB (I : ScalarInstance) (P : Profile) :
    DetModOn (ShOk I KeepFuncs (fun s => Silmaril.Wasm.Det.NoMem.storeB s = true))
      (shTraps I.exports) (I.shStrategy P) :=
  detModOn_shStrategy (detModuleS_of_storeB _)

/-- `DetModOn` with every move admissible is `DetMod`. -/
theorem detModOn_true_iff {E F : Silmaril.Games.Sig.{0}} {tF : Traps F} {σ : Strategy E F} :
    DetModOn (fun _ => True) tF σ ↔ DetMod tF σ :=
  ⟨fun h s m₁ m₂ h₁ h₂ hm₁ hm₂ hs => h s m₁ m₂ h₁ h₂ hm₁ hm₂ hs fun _ _ => trivial,
    fun h s m₁ m₂ h₁ h₂ hm₁ hm₂ hs _ => h s m₁ m₂ h₁ h₂ hm₁ hm₂ hs⟩

end Silmaril.Wasm.Det.Shared
