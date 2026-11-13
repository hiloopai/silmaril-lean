module

public import Silmaril.Wasm.Component.Core3G.Defs
public import Silmaril.Wasm.Component.Reference.Sound.Defs
import Silmaril.Proofs.Wasm.Component.Core3G.Bridge
import Silmaril.Proofs.Wasm.Component.Core3G.Sim
public import Silmaril.Proofs.Wasm.Component.Core3G.Restrict

/-!
# The Core 3.0 game engine against `modSem P`: the bridge

`(core3G P).sem = engineSem (core3P P) NumModule NumModule.mod` gives each numeric module the
game semantics of its engine instance (`Silmaril.Wasm.Component.Param`). `modSem P` gives it the
Core 3.0 instance strategy `ScalarInstance.strategy P` between the flat boundary handlers
`importH`/`exportH` (`Silmaril.Wasm.Component.Reference.Core3Sem`).

**The bridge** (`engineSem_eq_modSem`, `core3G_modSem_bridge : Core3GModSemBridge`): under
`m.IsInst I` and `SameInst P m I`, the two semantics are equal, at every profile `P`. The proof
(`Silmaril.Proofs.Wasm.Component.Core3G.Sim`) is a pair of weak simulations between the engine
transition system `engineLTS` and the parallel composition of the transition systems of
`importH`, `ScalarInstance.lts P` and `exportH` (which denotes the composite strategy,
`LTS.Denotes.comp`). Both run the same machine: stores, threads, the host-free step
`InternalP P` (`Steps (core3P P) = Reach P`) and the status `statusP P`.

**The two discrepancies**, and how they are handled.

1. *Export by name against export by position* (a hypothesis). `engineSem` instantiates by
   `prepare?` on the empty store and finds each export **by name** (`exportAddrs`); `modSem` takes
   the instance of `NumModule.IsInst`, which matches the export **types** only and finds the
   exports **by position** among the module's function exports. A module whose declared export
   names are not its function exports in order has an instance for `modSem` and none for
   `engineSem` (which then traps everywhere). `SameInst P m I` (engine instance = the `IsInst`
   instance: same store, same export addresses) is the hypothesis that removes this; nothing
   else is assumed.
2. *Typed results* (fixed, not assumed). The engine answers an export call with any flat values
   its status returns; `ScalarInstance.strategy` answers only with results of the export's
   declared types (`Answer.ofResult?`). They agree by type soundness of the instance at every
   profile: `ScalarInstance.answer_of_run` from a well-formed store, which persists from call to
   call (`wellFormed_after_run`), starting from the well-formed instantiation store of `IsInst`.

**Restrictions** (`Engine.restrict`). With the bridge, the restriction theorems of
`Silmaril.Wasm.Component.Param` are statements about `modSem P`: a restriction of the Core 3.0
engine refines `modSem P` (`restrict_le_modSem`), and is `modSem P` when the instance respects it
(`restrict_eq_modSem`). The reference-machine property `RefToSpec` is **not** transported to
restrictions (see `docs/projects/spectec/README.md`, track I3 ).

Also: `modSem_eq_of_isInst` (the choice of instance is irrelevant), `engine_two_refuse_iff`,
`bridge_two_ill` (ill-typed questions trap on both sides, with or without instances),
`engineSem_eq_modSem_of_none`, and `core3G_sem_eq_modSem_of` (the two core semantics of the IR
are equal when each module has the same instance on both sides or none on either).

New.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.Param

open Silmaril.Games Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference
open Silmaril.Wasm.Numerics (Profile)

/-- The one-call play answering `q` with `a`. -/
abbrev twoPlay {E F : Sig.{0}} (q : F.Op) (a : F.Ar q) : List (Move E F) :=
  [.inr (.ask q), .inr (.ans q a)]

/-- A question is ill-typed for an export interface: its payload is not flat values of the
export's parameter types. -/
def IllTyped (exps : CoreIface) (q : (CoreIface.sig exps).Op) : Prop :=
  ∀ xs, q.2 = .flat xs → ¬ FlatTyped (exps[q.1]).2.params xs

/-- **The choice of instance in `modSem` is irrelevant.** -/
theorem modSem_eq_of_isInst (P : Profile) {m : NumModule} {I : Silmaril.Wasm.Game.ScalarInstance}
    (hI : m.IsInst I) :
    (modSem P).sem m = (core3Sem P).sem
      { inst := I, imports := [], exports := m.exports, imports_eq := hI.2.1,
        exports_eq := hI.2.2 } :=
  Silmaril.Proofs.Wasm.Component.Core3G.modSem_eq_of_isInst P hI

/-- **An engine instance refuses a question without a callee.** -/
theorem engine_two_refuse_iff (E : Engine) (I : EInstance E) (imps exps : CoreIface)
    {q : (sigN exps.length).Op} (hq : callee? I.addrs exps q = none) (r : Option Payload) :
    twoPlay q r ∈ engineStrategy E I imps exps ↔ r = none :=
  Silmaril.Proofs.Wasm.Component.Core3G.engine_two_refuse_iff E I imps exps hq r

/-- On ill-typed questions the Core 3.0 game engine traps. -/
theorem engineSem_two_ill (P : Profile) (m : NumModule) {q : (CoreIface.sig m.exports).Op}
    (hill : IllTyped m.exports q) (r : Option Payload) :
    twoPlay q r ∈ (engineSem (core3P P) NumModule NumModule.mod).sem m ↔ r = none :=
  Silmaril.Proofs.Wasm.Component.Core3G.engineSem_two_ill P m hill r

/-- On ill-typed questions `modSem P` traps. -/
theorem modSem_two_ill (P : Profile) (m : NumModule) {q : (CoreIface.sig m.exports).Op}
    (hill : IllTyped m.exports q) (r : Option Payload) :
    twoPlay (E := CoreIface.sig []) q r ∈ (modSem P).sem m ↔ r = none :=
  Silmaril.Proofs.Wasm.Component.Core3G.modSem_two_ill P m hill r

/-- **The bridge on ill-typed questions**: both semantics answer exactly by a trap. -/
theorem bridge_two_ill (P : Profile) (m : NumModule) {q : (CoreIface.sig m.exports).Op}
    (hill : IllTyped m.exports q) (r : Option Payload) :
    twoPlay q r ∈ (engineSem (core3P P) NumModule NumModule.mod).sem m ↔ twoPlay q r ∈ (modSem P).sem m :=
  (engineSem_two_ill P m hill r).trans (modSem_two_ill P m hill r).symm

/-- **Without an instance on either side, the two semantics are equal.** -/
theorem engineSem_eq_modSem_of_none (P : Profile) (m : NumModule)
    (he : instOf (core3P P) m.mod [] m.exports = none) (hm : ¬ ∃ I, m.IsInst I) :
    (engineSem (core3P P) NumModule NumModule.mod).sem m = (modSem P).sem m :=
  Silmaril.Proofs.Wasm.Component.Core3G.engineSem_eq_modSem_of_none P m he hm

/-- The engine instance of `m` is the instance `I` of `modSem`: same store, same export
addresses. -/
def SameInst (P : Profile) (m : NumModule) (I : Silmaril.Wasm.Game.ScalarInstance) : Prop :=
  instOf (core3P P) m.mod [] m.exports = some ⟨I.store, I.addrs⟩

/-- **The bridge** (proved below, `core3G_modSem_bridge`). With the same instance on both sides, the game semantics of
the Core 3.0 engine is `modSem P`. Proved below (`core3G_modSem_bridge`). -/
def Core3GModSemBridge : Prop :=
  ∀ (P : Profile) (m : NumModule) (I : Silmaril.Wasm.Game.ScalarInstance), m.IsInst I →
    SameInst P m I → (engineSem (core3P P) NumModule NumModule.mod).sem m = (modSem P).sem m

/-- **The bridge.** With the same instance on both sides (`IsInst I`, `SameInst P m I`), the game
semantics of the Core 3.0 engine at profile `P` is `modSem P`, at every profile. -/
theorem engineSem_eq_modSem (P : Profile) {m : NumModule} {I : Silmaril.Wasm.Game.ScalarInstance}
    (hI : m.IsInst I) (hS : SameInst P m I) :
    (engineSem (core3P P) NumModule NumModule.mod).sem m = (modSem P).sem m :=
  Silmaril.Proofs.Wasm.Component.Core3G.engineSem_eq_modSem P hI hS

/-- The frozen target `Core3GModSemBridge` holds. -/
theorem core3G_modSem_bridge : Core3GModSemBridge :=
  fun P _ _ hI hS => engineSem_eq_modSem P hI hS

/-- **The bridge for the Core 3.0 game engine**: `(core3G P).sem` is `modSem P` on every module
whose engine instance is its `IsInst` instance. -/
theorem core3G_sem_eq_modSem (P : Profile) {m : NumModule} {I : Silmaril.Wasm.Game.ScalarInstance}
    (hI : m.IsInst I) (hS : SameInst P m I) : (core3G P).sem.sem m = (modSem P).sem m :=
  engineSem_eq_modSem P hI hS

/-- **The bridge on every module**: when, for each module, either both sides have the same
instance or neither has one, the two core semantics of the IR are equal. -/
theorem core3G_sem_eq_modSem_of (P : Profile)
    (h : ∀ m : NumModule, (∃ I, m.IsInst I ∧ SameInst P m I) ∨
      (instOf (core3P P) m.mod [] m.exports = none ∧ ¬ ∃ I, m.IsInst I)) :
    ∀ m, (core3G P).sem.sem m = (modSem P).sem m := by
  intro m
  rcases h m with ⟨I, hI, hS⟩ | ⟨he, hm⟩
  · exact core3G_sem_eq_modSem P hI hS
  · exact engineSem_eq_modSem_of_none P m he hm

/-- **A restriction of the Core 3.0 engine refines `modSem P`** on a module with the same instance
on both sides. -/
theorem restrict_le_modSem (P : Profile) (r : Restriction (core3P P)) {m : NumModule}
    {I : Silmaril.Wasm.Game.ScalarInstance} (hI : m.IsInst I) (hS : SameInst P m I) :
    (engineSem (restrict (core3P P) r) NumModule NumModule.mod).sem m ≤ (modSem P).sem m :=
  Silmaril.Proofs.Wasm.Component.Core3G.restrict_le_modSem hI hS

/-- **A restriction of the Core 3.0 engine that the instance respects is `modSem P`.** -/
theorem restrict_eq_modSem (P : Profile) (r : Restriction (core3P P)) {m : NumModule}
    {I : Silmaril.Wasm.Game.ScalarInstance} (hI : m.IsInst I) (hS : SameInst P m I)
    {Sto : (core3P P).Store Nat → Prop}
    (hR : Silmaril.Proofs.Wasm.Component.Param.Respects r ⟨I.store, I.addrs⟩ Sto) :
    (engineSem (restrict (core3P P) r) NumModule NumModule.mod).sem m = (modSem P).sem m :=
  Silmaril.Proofs.Wasm.Component.Core3G.restrict_eq_modSem hI hS hR

end Silmaril.Wasm.Component.Param
