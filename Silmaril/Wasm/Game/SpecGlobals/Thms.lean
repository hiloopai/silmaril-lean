module

public import Silmaril.Wasm.Game.SpecGlobals.Defs
public import Silmaril.Wasm.Game.LinkDiv.Thms
public import Silmaril.Wasm.Game.SpecInst.Defs
import Silmaril.Proofs.Wasm.Game.SpecGlobals.Setup
import Silmaril.Proofs.Wasm.Game.SpecGlobals.SpecAt
import Silmaril.Proofs.Wasm.Game.SpecGlobals.SegSpec
import Silmaril.Proofs.Wasm.Game.SpecGlobals.TrapOutcome
import Silmaril.Proofs.Wasm.Game.SpecGlobals.SegNoFail
import Silmaril.Proofs.Wasm.Game.SpecGlobals.Behaviours
import Silmaril.Proofs.Wasm.Game.SpecGlobals.BehavioursHost
public import Silmaril.Proofs.Wasm.Game.SpecGlobals.StepHostOut
public import Silmaril.Wasm.Behaviour.Semantics.V3.Defs
public import Silmaril.Wasm.Execution.Core.Exec.SegmentInitTrap
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateOnce

/-!
# Static linking through the specification's instantiation, modules with globals

For a linking setup `S` in the fragment of silmaril-lean's linker with scalar interfaces
(`Setup.Scalar`), **globals allowed**, and an **arbitrary** silmaril profile `P` (no
determinism is used):

* `Setup.specStores_nonempty`: the specification's preparation (`prepare?`) of the provider,
  of the consumer against host stubs (into the stubbed spec provider store) and of the linked
  module succeeds; `SpecStores.instantiate`: these configurations are the specification's
  instantiations `Instantiate P host` (the linker's fragment has no segments and no start
  function, so `$instantiate`'s code is empty), for every profile and host.
* `SpecStores.provider_dstrategy`, `consumer_dstrategy`, `linked_dstrategy`: the
  divergence-observing strategies at the spec stores are those at the setup's
  `instantiateOnce?` stores, although the spec stores hold every global twice; also for the
  plain strategies (`*_strategy`), and with the instantiation phase: the spec strategy
  (`ScalarInstance.specStrategy`, instantiation running the `$instantiate` configuration) is
  the one of the setup's store and frame (`*_specStrategy`).
* `SpecStores.link_is_composition_profile` (M3) and `SpecStores.link_is_composition_div`
  (M3 with divergence observed): the strategy of the linked module instantiated by the
  specification is the composite of the strategies of the provider and of the consumer
  instantiated by the specification.
* `prepare_strategy_eq_once`: the same for one module, outside linking: a module without
  segments and global imports, prepared by the specification into a host-free well-typed store,
  has the strategies (plain and divergence-observing) of its `instantiateOnce?` instance, and
  the same function exports.

The bridge is a **global-address embedding** (`Silmaril.Proofs.Wasm.Game.SpecGlobals.Emb`): an
injective map of the once-store's global addresses into the spec store's (the setup's globals
are the spec's second copies, the `$evalglobals` copies are named by no module instance),
under which every host-free Core step is matched one for one in both directions
(`Silmaril.Proofs.Wasm.Game.SpecGlobals.step`, with a left inverse on the range for the reverse
direction); this replaces silmaril-lean's `GlobalRenameSimulation` (a permutation, which
cannot drop the unreachable copies).

* `spec_eq_once_seg`: modules **with data/element segments and global imports**: the
  spec's segment-initialisation code, run by Core `Step P` (any profile), is a forced run to
  the store that `instantiateOnce?` builds directly, so the strategy and the closed program
  with the spec's instantiation phase are those of `instantiateOnce?`'s store and frame;
  `spec_trap_seg`: when the direct initialisation traps (out of bounds), the spec's run is
  forced up to that trap.
* `SpecStores.linked_isSpecInstanceAt`: the linked module instantiated by `$instantiate` is a
  spec instance (`IsSpecInstanceAt`), and M3 holds for that instance's strategy.
* `SpecStores.*_closedSpec`, `linked_closedD`: the closed programs (against any environment)
  are invariant as well.

* `spec_eq_once_seg_valid`, `spec_trap_outcome_valid`: for validated modules (offsets are
  constant by validation): equality with single allocation when it succeeds, and when the
  direct initialisation traps the spec's instantiation fails exactly with `traps` (never ready,
  never diverging); `residue_segments_not_fail`, `prepare_segments_not_fail`: for validated
  modules the direct initialisation never ends in `.fail`, so these two cases are exhaustive.

Scope. The provider and consumer instances of a setup are not
`IsSpecInstanceAt` of their modules (their exports are the stub set and the linked exports).

* `spec_behaviours_eq_residue` (added , an earlier step): the relational behaviours
  `behavioursOf` without host calls. The spec's preparation of a module with globals and the
  residue configuration of single allocation (`$evalglobals`, then the global-free residue)
  have the same host-free behaviours with the start call, at every profile. The store needs
  only that its function instances name existing globals (no well-typedness, no restriction
  to Wasm functions), and the imports are typed.

Proofs: `Silmaril.Proofs.Wasm.Game.SpecGlobals.*`. New.
-/

public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game

open CategoryTheory Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Validation Silmaril.Wasm.Link.GC

/-- **Spec preparation and single allocation give the same strategies**, every profile: for a
module without data/element segments and without global imports, instantiated into a
host-free well-typed store, the store that the specification's `prepare?` produces (every
global allocated twice) and the store of `instantiateOnce?` (every global once) give every
scalar instance the same divergence-observing and plain strategies; the configuration has no
code and the same function exports; and the strategy whose instantiation phase is the spec's
`$instantiate` configuration (`specStrategy`, the module's start function included) is the one
running the start call from the single-allocation frame and store. -/
theorem prepare_strategy_eq_once {s s' : Store Nat} {m : Module} {xas : List ExternAddr}
    {f' : Frame} {st : Option FuncIdx} (hs : StoreOk s)
    (hw : ∀ fi ∈ s.funcs, ∃ f, fi.code = .wasm f) (hxg : ExternAddr.globals xas = [])
    (hseg : m.data = [] ∧ m.elems = []) (ho : instantiateOnce? s m xas = some (s', f', st)) :
    ∃ c : Config Nat, prepare? evalConst? s m xas = some (c, st) ∧ c.code = [] ∧
      exportFuncAddrs c.frame.module = exportFuncAddrs f'.module ∧
      ∀ (I : ScalarInstance) (P : Profile),
        I.dstrategy P c.store = I.dstrategy P s' ∧ I.strategy P c.store = I.strategy P s' ∧
        I.specStrategy P (c.withStart st) =
          I.instStrategyT P s' (configThread ((⟨s', f', []⟩ : Config Nat).withStart st)) :=
  Silmaril.Proofs.Wasm.Game.SpecGlobals.prepare_strategy_eq_once hs hw hxg hseg ho

/-- **Spec instantiation with data/element segments and global imports plays as single
allocation**, every profile: for a module whose active-segment offsets are constant
instructions, instantiated into a host-free well-typed store against addresses whose global
imports exist, if `instantiateOnce?` succeeds, then the strategy and the closed program whose
instantiation phase is the spec's `$instantiate` configuration (segment initialisation run by
Core `Step P`, then the start call) are those whose instantiation phase runs the start call
from `instantiateOnce?`'s store and frame. -/
theorem spec_eq_once_seg {s s' : Store Nat} {m : Module} {xas : List ExternAddr} {f' : Frame}
    {st : Option FuncIdx} (hs : StoreOk s) (hw : ∀ fi ∈ s.funcs, ∃ f, fi.code = .wasm f)
    (hxb : ∀ a ∈ ExternAddr.globals xas, a < s.globals.length)
    (hm : (∀ e ∈ m.elems, ∀ y off, e.mode = .active y off → ∀ i ∈ off, i.IsConstI) ∧
      ∀ d ∈ m.data, ∀ y off, d.mode = .active y off → ∀ i ∈ off, i.IsConstI)
    (ho : instantiateOnce? s m xas = some (s', f', st)) :
    ∃ c : Config Nat, prepare? evalConst? s m xas = some (c, st) ∧
      ∀ (I : ScalarInstance) (P : Profile),
        I.specStrategy P (c.withStart st) =
          I.instStrategyT P s' (configThread ((⟨s', f', []⟩ : Config Nat).withStart st)) ∧
        ∀ K : Env I.E, I.closedSpec P (c.withStart st) K =
          I.closedInstT P s' (configThread ((⟨s', f', []⟩ : Config Nat).withStart st)) K :=
  Silmaril.Proofs.Wasm.Game.SpecGlobals.spec_eq_once_seg hs hw hxb hm ho

/-- **Trapping segment initialisation**, every profile: when the residue preparation of single
allocation succeeds and its direct segment initialisation traps (`initSegmentsT? = .trap`, so
`instantiateOnce?` fails), the spec's instantiation plays as the thread stopped at that trap
(after a forced, deterministic prefix). -/
theorem spec_trap_seg {s : Store Nat} {m : Module} {xas : List ExternAddr} (hs : StoreOk s)
    (hw : ∀ fi ∈ s.funcs, ∃ f, fi.code = .wasm f)
    (hxb : ∀ a ∈ ExternAddr.globals xas, a < s.globals.length)
    (hm : (∀ e ∈ m.elems, ∀ y off, e.mode = .active y off → ∀ i ∈ off, i.IsConstI) ∧
      ∀ d ∈ m.data, ∀ y off, d.mode = .active y off → ∀ i ∈ off, i.IsConstI)
    {s₁ : Store Nat} {f₁ : Frame} {vs : List Val}
    (hg : evalGlobals? evalConst? s ⟨[], ModuleInst.initial s m xas⟩ (Module.closedGlobalTypes m)
      (m.globals.map Global.init) = some (s₁, f₁, vs))
    {c₁ : Config Nat} {st : Option FuncIdx}
    (hp : prepare? evalConst? s₁ m.globalResidue
      (xas ++ globalAddrs s.globals.length m.globals.length) = some (c₁, st))
    {s'' : Store Nat}
    (htrap : initSegmentsT? evalConst? c₁.store c₁.frame m.globalResidue = .trap s'') :
    ∃ c : Config Nat, prepare? evalConst? s m xas = some (c, st) ∧
      ∀ (I : ScalarInstance) (P : Profile), ∃ (W : List Val) (R : List Admin),
        I.specStrategy P (c.withStart st) =
          I.instStrategyT P s'' (configThread ⟨s'', c₁.frame, vals W ++ .trap :: R⟩) ∧
        ∀ K : Env I.E, I.closedSpec P (c.withStart st) K =
          I.closedInstT P s'' (configThread ⟨s'', c₁.frame, vals W ++ .trap :: R⟩) K :=
  Silmaril.Proofs.Wasm.Game.SpecGlobals.spec_trap_seg hs hw hxb hm hg hp htrap

/-- **`spec_eq_once_seg` for validated modules**: validation makes the active-segment offsets
constant. -/
theorem spec_eq_once_seg_valid {s s' : Store Nat} {m : Module} {mt : CModuleType}
    {xas : List ExternAddr} {f' : Frame} {st : Option FuncIdx} (hv : validate? m = some mt)
    (hs : StoreOk s) (hw : ∀ fi ∈ s.funcs, ∃ f, fi.code = .wasm f)
    (hxb : ∀ a ∈ ExternAddr.globals xas, a < s.globals.length)
    (ho : instantiateOnce? s m xas = some (s', f', st)) :
    ∃ c : Config Nat, prepare? evalConst? s m xas = some (c, st) ∧
      ∀ (I : ScalarInstance) (P : Profile),
        I.specStrategy P (c.withStart st) =
          I.instStrategyT P s' (configThread ((⟨s', f', []⟩ : Config Nat).withStart st)) ∧
        ∀ K : Env I.E, I.closedSpec P (c.withStart st) K =
          I.closedInstT P s' (configThread ((⟨s', f', []⟩ : Config Nat).withStart st)) K :=
  Silmaril.Proofs.Wasm.Game.SpecGlobals.spec_eq_once_seg_valid hv hs hw hxb ho

/-- **Trapping segment initialisation fails instantiation with `traps`**, validated modules,
every profile and environment: when the residue preparation of single allocation succeeds and
its direct segment initialisation traps (so `instantiateOnce?` fails), the closed program whose
instantiation phase is the spec's `$instantiate` configuration is never ready, never diverges
during instantiation, and fails exactly with `traps`. -/
theorem spec_trap_outcome_valid {s : Store Nat} {m : Module} {mt : CModuleType}
    {xas : List ExternAddr} (hv : validate? m = some mt) (hs : StoreOk s)
    (hw : ∀ fi ∈ s.funcs, ∃ f, fi.code = .wasm f)
    (hxb : ∀ a ∈ ExternAddr.globals xas, a < s.globals.length)
    {s₁ : Store Nat} {f₁ : Frame} {vs : List Val}
    (hg : evalGlobals? evalConst? s ⟨[], ModuleInst.initial s m xas⟩ (Module.closedGlobalTypes m)
      (m.globals.map Global.init) = some (s₁, f₁, vs))
    {c₁ : Config Nat} {st : Option FuncIdx}
    (hp : prepare? evalConst? s₁ m.globalResidue
      (xas ++ globalAddrs s.globals.length m.globals.length) = some (c₁, st))
    {s'' : Store Nat}
    (htrap : initSegmentsT? evalConst? c₁.store c₁.frame m.globalResidue = .trap s'') :
    ∃ c : Config Nat, prepare? evalConst? s m xas = some (c, st) ∧
      ∀ (I : ScalarInstance) (P : Profile) (K : Env I.E),
        ¬ (I.closedSpec P (c.withStart st) K).InstReady ∧
        ¬ (I.closedSpec P (c.withStart st) K).InstDiverges ∧
        ∀ b, (I.closedSpec P (c.withStart st) K).InstFails b ↔ b = .traps :=
  Silmaril.Proofs.Wasm.Game.SpecGlobals.spec_trap_outcome_valid hv hs hw hxb hg hp htrap

/-- **Direct segment initialisation never fails for validated modules** (it succeeds or traps),
on the residue configuration of single allocation. -/
theorem residue_segments_not_fail {s : Store Nat} {m : Module} {xas : List ExternAddr}
    {xtI xtE : List CExternType} (hm : ModuleOk m ⟨xtI, xtE⟩) (hs : StoreOk s)
    (hw : ∀ fi ∈ s.funcs, ∃ f, fi.code = .wasm f) (hxas : List.Forall₂ (ExternAddrOk s) xas xtI)
    {s₁ : Store Nat} {f₁ : Frame} {vs : List Val}
    (hg : evalGlobals? evalConst? s ⟨[], ModuleInst.initial s m xas⟩ (Module.closedGlobalTypes m)
      (m.globals.map Global.init) = some (s₁, f₁, vs))
    {c₁ : Config Nat} {st : Option FuncIdx}
    (hp : prepare? evalConst? s₁ m.globalResidue
      (xas ++ globalAddrs s.globals.length m.globals.length) = some (c₁, st)) :
    initSegmentsT? evalConst? c₁.store c₁.frame m.globalResidue ≠ .fail :=
  Silmaril.Proofs.Wasm.Game.SpecGlobals.residue_segments_not_fail hm hs hw hxas hg hp

/-- **Direct segment initialisation never fails for validated modules**, on the spec's
`prepare?` configuration. -/
theorem prepare_segments_not_fail {s : Store Nat} {m : Module} {xas : List ExternAddr}
    {xtI xtE : List CExternType} {c : Config Nat} {st : Option FuncIdx}
    (hm : ModuleOk m ⟨xtI, xtE⟩) (hs : StoreOk s) (hxas : List.Forall₂ (ExternAddrOk s) xas xtI)
    (hp : prepare? evalConst? s m xas = some (c, st)) :
    initSegmentsT? evalConst? c.store c.frame m ≠ .fail :=
  Silmaril.Proofs.Wasm.Game.SpecGlobals.prepare_segments_not_fail hm hs hxas hp

/-- **Spec preparation and single allocation have the same host-free behaviours**, every
profile: for a store whose function instances name only existing globals and typed imports,
if `$evalglobals` and the preparation of the global-free residue succeed (the first two phases
of `instantiateOnce?`), the specification's `prepare?` succeeds, and with the start call its
configuration has the residue configuration's behaviours without host calls. -/
theorem spec_behaviours_eq_residue {s : Store Nat}
    (hb : ∀ fi ∈ s.funcs, (∀ a ∈ fi.module.globals, a < s.globals.length) ∧
      ∀ e ∈ fi.module.exports, ∀ a, e.addr = .global a → a < s.globals.length)
    {m : Module} {xas : List ExternAddr} {xts : List CExternType}
    (hxas : List.Forall₂ (ExternAddrOk s) xas xts)
    {s₁ : Store Nat} {f₁ : Frame} {vs : List Val}
    (hg : evalGlobals? evalConst? s ⟨[], ModuleInst.initial s m xas⟩ (Module.closedGlobalTypes m)
      (m.globals.map Global.init) = some (s₁, f₁, vs))
    {c₁ : Config Nat} {st : Option FuncIdx}
    (hp : prepare? evalConst? s₁ m.globalResidue
      (xas ++ globalAddrs s.globals.length m.globals.length) = some (c₁, st)) :
    ∃ c : Config Nat, prepare? evalConst? s m xas = some (c, st) ∧
      ∀ P : Profile, behavioursOf P (fun _ _ _ _ => False) (c.withStart st) =
        behavioursOf P (fun _ _ _ _ => False) (c₁.withStart st) :=
  Silmaril.Proofs.Wasm.Game.SpecGlobals.spec_behaviours_eq_residue hb hxas hg hp

/-- **Spec preparation and single allocation have the same behaviours with a host blind to
globals and functions**, every profile: `spec_behaviours_eq_residue` for a host that keeps the
store's globals and functions (`keeps`) and whose calls are unchanged when they are replaced
(`ret`, `div`). -/
theorem spec_behaviours_eq_residue_host {host : HostSemantics Nat}
    (keeps : ∀ h s vs s' r, host h s vs (.returned s' r) →
      s'.globals = s.globals ∧ s'.funcs = s.funcs)
    (ret : ∀ h s vs s' r gs fs, host h s vs (.returned s' r) →
      host h { s with globals := gs, funcs := fs } vs
        (.returned { s' with globals := gs, funcs := fs } r))
    (div : ∀ h s vs gs fs, host h s vs .diverged →
      host h { s with globals := gs, funcs := fs } vs .diverged)
    {s : Store Nat}
    (hb : ∀ fi ∈ s.funcs, (∀ a ∈ fi.module.globals, a < s.globals.length) ∧
      ∀ e ∈ fi.module.exports, ∀ a, e.addr = .global a → a < s.globals.length)
    {m : Module} {xas : List ExternAddr} {xts : List CExternType}
    (hxas : List.Forall₂ (ExternAddrOk s) xas xts)
    {s₁ : Store Nat} {f₁ : Frame} {vs : List Val}
    (hg : evalGlobals? evalConst? s ⟨[], ModuleInst.initial s m xas⟩ (Module.closedGlobalTypes m)
      (m.globals.map Global.init) = some (s₁, f₁, vs))
    {c₁ : Config Nat} {st : Option FuncIdx}
    (hp : prepare? evalConst? s₁ m.globalResidue
      (xas ++ globalAddrs s.globals.length m.globals.length) = some (c₁, st)) :
    ∃ c : Config Nat, prepare? evalConst? s m xas = some (c, st) ∧
      ∀ P : Profile, behavioursOf P host (c.withStart st) =
        behavioursOf P host (c₁.withStart st) :=
  Silmaril.Proofs.Wasm.Game.SpecGlobals.spec_behaviours_eq_residueH
    (Silmaril.Proofs.Wasm.Game.SpecGlobals.HostEmb.blind ⟨keeps, ret, div⟩) hb hxas hg hp

/-- **Single-allocation residue behaviours are spec behaviours with a host commuting with the
embeddings on well-behaved targets**, every profile: for a host satisfying
`HostEmbR Good` (it commutes with every global-address embedding whose target holds only `Good`
globals outside the image, and keeps that property), if the spec preparation's store holds only
`Good` globals, each behaviour of the residue configuration with the start call is a behaviour
of the spec configuration. `HostEmbR` is exported from
`Silmaril.Proofs.Wasm.Game.SpecGlobals.StepHostOut`. -/
theorem spec_behaviours_sub_residue_hostR {Good : GlobalInst → Prop}
    {host : HostSemantics Nat}
    (hh : Silmaril.Proofs.Wasm.Game.SpecGlobals.HostEmbR Good host) {s : Store Nat}
    (hb : ∀ fi ∈ s.funcs, (∀ a ∈ fi.module.globals, a < s.globals.length) ∧
      ∀ e ∈ fi.module.exports, ∀ a, e.addr = .global a → a < s.globals.length)
    {m : Module} {xas : List ExternAddr} {xts : List CExternType}
    (hxas : List.Forall₂ (ExternAddrOk s) xas xts)
    {s₁ : Store Nat} {f₁ : Frame} {vs : List Val}
    (hg : evalGlobals? evalConst? s ⟨[], ModuleInst.initial s m xas⟩ (Module.closedGlobalTypes m)
      (m.globals.map Global.init) = some (s₁, f₁, vs))
    {c₁ : Config Nat} {st : Option FuncIdx}
    (hp : prepare? evalConst? s₁ m.globalResidue
      (xas ++ globalAddrs s.globals.length m.globals.length) = some (c₁, st))
    (hgood : ∀ c st', prepare? evalConst? s m xas = some (c, st') →
      ∀ g ∈ c.store.globals, Good g) :
    ∃ c : Config Nat, prepare? evalConst? s m xas = some (c, st) ∧
      ∀ P : Profile, behavioursOf P host (c₁.withStart st) ⊆
        behavioursOf P host (c.withStart st) :=
  Silmaril.Proofs.Wasm.Game.SpecGlobals.spec_behaviours_sub_residueHR hh hb hxas hg hp hgood

/--
info: 'Silmaril.Wasm.Game.spec_behaviours_sub_residue_hostR' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms spec_behaviours_sub_residue_hostR

namespace Linking.Setup

variable {S : Setup}

/-- **Spec preparation succeeds** for every linking setup. -/
theorem specStores_nonempty (S : Setup) : Nonempty S.SpecStores :=
  Silmaril.Proofs.Wasm.Game.SpecGlobals.SetupSpec.specStores_nonempty S

namespace SpecStores

variable (X : S.SpecStores)

/-- **The spec stores are the specification's instantiations**, every profile and host. -/
theorem instantiate (P : Profile) (host : HostSemantics Nat) :
    Instantiate P host S.base S.provider (Preparation.imports []) X.cp ∧
    Instantiate P host (stubOut S.base.funcs.length S.stubs X.cp.store) S.consumer
      (Preparation.imports (S.assembly.imports.map (fun f => S.base.funcs.length + f.toNat)))
      X.ccs ∧
    Instantiate P host S.base S.linked (Preparation.imports []) X.cl :=
  Silmaril.Proofs.Wasm.Game.SpecGlobals.SetupSpec.specStores_instantiate X P host

/-- The provider at its spec store has the strategy of the setup's provider. -/
theorem provider_dstrategy (P : Profile) :
    S.providerI.dstrategy P X.cp.store = S.providerI.dstrategy P S.sp :=
  Silmaril.Proofs.Wasm.Game.SpecGlobals.SetupSpec.provider_dstrategy X P

/-- The consumer at its spec store has the strategy of the setup's consumer. -/
theorem consumer_dstrategy (P : Profile) :
    S.consumerI.dstrategy P X.ccs.store = S.consumerI.dstrategy P S.scs :=
  Silmaril.Proofs.Wasm.Game.SpecGlobals.SetupSpec.consumer_dstrategy X P

/-- The linked module at its spec store has the strategy of the setup's linked module. -/
theorem linked_dstrategy (P : Profile) :
    S.linkedI.dstrategy P X.cl.store = S.linkedI.dstrategy P S.sl :=
  Silmaril.Proofs.Wasm.Game.SpecGlobals.SetupSpec.linked_dstrategy X P

/-- With the instantiation phase: the spec's `$instantiate` of the provider (no code to run)
plays as the setup's provider instantiated by `instantiateOnce?`. -/
theorem provider_specStrategy (P : Profile) :
    S.providerI.specStrategy P X.cp =
      S.providerI.instStrategyT P S.sp (configThread ⟨S.sp, S.fp, []⟩) :=
  Silmaril.Proofs.Wasm.Game.SpecGlobals.SetupSpec.provider_specStrategy X P

theorem consumer_specStrategy (P : Profile) :
    S.consumerI.specStrategy P X.ccs =
      S.consumerI.instStrategyT P S.scs (configThread ⟨S.scs, S.fcs, []⟩) :=
  Silmaril.Proofs.Wasm.Game.SpecGlobals.SetupSpec.consumer_specStrategy X P

theorem linked_specStrategy (P : Profile) :
    S.linkedI.specStrategy P X.cl =
      S.linkedI.instStrategyT P S.sl (configThread ⟨S.sl, S.fl, []⟩) :=
  Silmaril.Proofs.Wasm.Game.SpecGlobals.SetupSpec.linked_specStrategy X P

theorem provider_strategy (P : Profile) :
    S.providerI.strategy P X.cp.store = S.providerI.σ P := by
  have h := congrArg DStrategy.forget (X.provider_dstrategy P)
  rwa [ScalarInstance.forget_dstrategy, ScalarInstance.forget_dstrategy] at h

theorem consumer_strategy (P : Profile) :
    S.consumerI.strategy P X.ccs.store = S.consumerI.σ P := by
  have h := congrArg DStrategy.forget (X.consumer_dstrategy P)
  rwa [ScalarInstance.forget_dstrategy, ScalarInstance.forget_dstrategy] at h

theorem linked_strategy (P : Profile) :
    S.linkedI.strategy P X.cl.store = S.linkedI.σ P := by
  have h := congrArg DStrategy.forget (X.linked_dstrategy P)
  rwa [ScalarInstance.forget_dstrategy, ScalarInstance.forget_dstrategy] at h

/-- **M3 through the specification's instantiation, modules with globals, every profile.**
The strategy of the linked module instantiated by `$instantiate` is the composite of the
strategies of the provider and of the consumer (against host stubs) instantiated by
`$instantiate`. -/
theorem link_is_composition_profile (hS : S.Scalar) (P : Profile) :
    (S.linkedI.strategy P X.cl.store : ifaceSig [] ⟶ ifaceSig S.exportTypes) =
      CategoryStruct.comp (obj := Sig) (X := ifaceSig []) (Y := ifaceSig S.stubTypes)
        (Z := ifaceSig S.exportTypes) (S.providerI.strategy P X.cp.store)
        (S.consumerI.strategy P X.ccs.store) := by
  rw [X.linked_strategy, X.provider_strategy, X.consumer_strategy]
  exact S.link_is_composition_profile hS P

/-- **M3 through the specification's instantiation, divergence observed, modules with
globals, every profile.** -/
theorem link_is_composition_div (hS : S.Scalar) (P : Profile) :
    S.linkedI.dstrategy P X.cl.store =
      (S.providerI.dstrategy P X.cp.store).comp (S.consumerI.dstrategy P X.ccs.store) := by
  rw [X.linked_dstrategy, X.provider_dstrategy, X.consumer_dstrategy]
  exact S.link_is_composition_div hS P

/-- The closed program of the provider instantiated by `$instantiate` against an environment
is the one of the setup's provider. -/
theorem provider_closedSpec (P : Profile) (K : Env S.providerI.E) :
    S.providerI.closedSpec P X.cp K =
      S.providerI.closedInstT P S.sp (configThread ⟨S.sp, S.fp, []⟩) K :=
  Silmaril.Proofs.Wasm.Game.SpecGlobals.SetupSpec.provider_closedSpec X P K

theorem consumer_closedSpec (P : Profile) (K : Env S.consumerI.E) :
    S.consumerI.closedSpec P X.ccs K =
      S.consumerI.closedInstT P S.scs (configThread ⟨S.scs, S.fcs, []⟩) K :=
  Silmaril.Proofs.Wasm.Game.SpecGlobals.SetupSpec.consumer_closedSpec X P K

theorem linked_closedSpec (P : Profile) (K : Env S.linkedI.E) :
    S.linkedI.closedSpec P X.cl K =
      S.linkedI.closedInstT P S.sl (configThread ⟨S.sl, S.fl, []⟩) K :=
  Silmaril.Proofs.Wasm.Game.SpecGlobals.SetupSpec.linked_closedSpec X P K

/-- The closed linked program (export calls only) at the spec store is the one at the setup's
store. -/
theorem linked_closedD (P : Profile) (K : Env S.linkedI.E) :
    S.linkedI.closedD P X.cl.store K = S.linkedI.closedD P S.sl K :=
  Silmaril.Proofs.Wasm.Game.SpecGlobals.SetupSpec.linked_closedD X P K

/-- **The linked module instantiated by `$instantiate` is a spec instance**, and (M3,
divergence observed, every profile) its strategy is the composite of the provider's and the
consumer's at their spec stores. -/
theorem linked_isSpecInstanceAt (hS : S.Scalar) (P : Profile) :
    ∃ mt, IsSpecInstanceAt S.base (Preparation.imports []) S.linked mt
        { S.linkedI with store := X.cl.store } X.cl ∧
      ({ S.linkedI with store := X.cl.store } : ScalarInstance).dstrategy P X.cl.store =
        (S.providerI.dstrategy P X.cp.store).comp (S.consumerI.dstrategy P X.ccs.store) := by
  obtain ⟨mt, hmt⟩ := Silmaril.Proofs.Wasm.Game.SpecGlobals.linked_isSpecInstanceAt hS X
  refine ⟨mt, hmt, ?_⟩
  rw [Silmaril.Proofs.Wasm.Game.SpecGlobals.dstrategy_with_store]
  exact X.link_is_composition_div hS P

end SpecStores

end Linking.Setup

end Silmaril.Wasm.Game
