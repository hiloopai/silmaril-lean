module

public import Silmaril.Wasm.Game.Instantiate.Defs
public import Silmaril.Wasm.Link.GC
public import Silmaril.Wasm.Link.Recipe
public import Silmaril.Wasm.Link.Preparation

/-!
# The data of a static link in the scalar fragment

The games that the statement "static linking is composition"
(`Silmaril.Wasm.Game.Linking.Thms`) compares.

## The fragment

silmaril-lean's GC static linker `link?` (`Silmaril.Wasm.Link.GC`) fixes the
fragment (`Recipe.Assembly`): the provider has no imports, every consumer
import is a provider function, no memories, tables, tags, data or element
segments, no start function. Hence the linked module is **closed**. On top of
`link?` we require scalar interfaces: every provider function the consumer
side can reach and every linked export has a scalar type (`Setup.Scalar`).

## The four instances

All stores come from `instantiateOnce?` over a host-free, well-typed base
store `base` (consumer imports resolved to the provider functions); no start
function runs:

* the **provider** `providerI`: closed, store `sp`, exporting the *stub set*
  `stubs` of provider functions (those the consumer imports and the provider
  functions the linked module exports);
* the **consumer with stubs** `consumerI`: the consumer instantiated in
  `stubOut sp`, the provider store whose stub-set functions are replaced by
  host functions (`.host k` is import `k`, the `k`-th stub). Its exports are
  *all* linked exports, at the same addresses as in the linked module: a
  linked export that is a provider function is a stub there, so calling it is
  a pass-through;
* the **shared** world `sharedI` (store `sc`): provider and consumer
  instantiated separately into one store, the consumer's imports resolved to
  the provider's functions;
* the **linked** module `linkedI`: closed, store `sl`, the same exports.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game

open Silmaril.Games Silmaril.Wasm Silmaril.Wasm.Execution.Core Silmaril.Wasm.Validation
  Silmaril.Wasm.SingleThreaded Silmaril.Wasm.Link.GC

/-- The upper projections of the plays of an instance (for a closed instance, the plays of
an object whose state is its store). -/
def ScalarInstance.objPlays (I : ScalarInstance) (P : Profile) (s : Store Nat) :
    Set (List (Ev I.F)) :=
  upper '' I.plays P s

/-- The upper projections of the plays of `N` whose lower projection lies in `V` (the
interaction of a set of lower behaviours with a set of plays). -/
def interact {E F : Sig.{0}} (V : Set (List (Ev E))) (N : Set (List (Move E F))) :
    Set (List (Ev F)) :=
  {t | ∃ p ∈ N, lower p ∈ V ∧ upper p = t}

namespace Linking

/-- Replace the provider functions of the stub set by host stubs: the function at address
`base + stubs[k]` gets code `.host k` (import `k`). Types and module instances are kept. -/
def stubOut (base : Nat) (stubs : List Nat) (s : Store Nat) : Store Nat :=
  { s with funcs := s.funcs.mapIdx fun a fi =>
      if base ≤ a ∧ a - base ∈ stubs then { fi with code := .host (stubs.idxOf (a - base)) }
      else fi }

/-- The canonical stub set: the provider functions the consumer imports, then the provider
functions among the linked exports (addresses `linkedExports` in a store whose provider
functions start at `base`), without duplicates. -/
def canonicalStubs (imports : List FuncIdx) (base nprov : Nat) (linkedExports : List Nat) :
    List Nat :=
  (imports.map (fun f => f.toNat) ++
    linkedExports.filterMap fun a => if base ≤ a ∧ a < base + nprov then some (a - base) else none).dedup

/-- The data of a static link in the scalar fragment (all instantiations succeed, no start
function). -/
structure Setup where
  namespaceName : String
  provider : Module
  consumer : Module
  linked : Module
  assembly : Recipe.Assembly namespaceName provider consumer linked
  link : link? namespaceName provider consumer = some linked
  /-- The base store, without host functions. -/
  base : Store Nat
  baseHostFree : ∀ fi ∈ base.funcs, ∃ f, fi.code = .wasm f
  baseOk : StoreOk base
  sp : Store Nat
  sc : Store Nat
  scs : Store Nat
  sl : Store Nat
  fp : Frame
  fc : Frame
  fcs : Frame
  fl : Frame
  /-- Provider functions exposed to the consumer side (indices into `provider.funcs`). -/
  stubs : List Nat
  stubs_nodup : stubs.Nodup
  stubs_lt : ∀ k ∈ stubs, k < provider.funcs.length
  imports_stubbed : ∀ f ∈ assembly.imports, f.toNat ∈ stubs
  exports_stubbed : ∀ a ∈ exportFuncAddrs fl.module, base.funcs.length ≤ a →
    a < base.funcs.length + provider.funcs.length → a - base.funcs.length ∈ stubs
  /-- Scalar types of the stubs and of the linked exports. -/
  stubTypes : List FnType
  exportTypes : List FnType
  provInst : instantiateOnce? base provider (Preparation.imports []) = some (sp, fp, none)
  sharedInst : instantiateOnce? sp consumer
    (Preparation.imports (assembly.imports.map (fun f => base.funcs.length + f.toNat))) =
      some (sc, fc, none)
  stubInst : instantiateOnce? (stubOut base.funcs.length stubs sp) consumer
    (Preparation.imports (assembly.imports.map (fun f => base.funcs.length + f.toNat))) =
      some (scs, fcs, none)
  linkedInst : instantiateOnce? base linked (Preparation.imports []) = some (sl, fl, none)

namespace Setup

variable (S : Setup)

/-- The provider: closed, exporting the stubs. -/
def providerI : ScalarInstance :=
  ⟨[], S.stubTypes, S.stubs.map (S.base.funcs.length + ·), S.sp⟩

/-- The consumer with host stubs for the provider: imports the stubs, exports all linked
exports. -/
def consumerI : ScalarInstance :=
  ⟨S.stubTypes, S.exportTypes, exportFuncAddrs S.fl.module, S.scs⟩

/-- #1936's shared world: provider and consumer in one store, closed. -/
def sharedI : ScalarInstance :=
  ⟨[], S.exportTypes, exportFuncAddrs S.fl.module, S.sc⟩

/-- The linked module, closed. -/
def linkedI : ScalarInstance :=
  ⟨[], S.exportTypes, exportFuncAddrs S.fl.module, S.sl⟩

/-- The scalar-interface fragment: the four instances are well formed. -/
structure Scalar : Prop where
  provider : S.providerI.Ok
  consumer : S.consumerI.Ok
  shared : S.sharedI.Ok
  linked : S.linkedI.Ok

end Setup

end Linking

end Silmaril.Wasm.Game
