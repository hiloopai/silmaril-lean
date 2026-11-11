module

public import Silmaril.Wasm.Game.Start.Defs
public import Silmaril.Wasm.Execution.Core.Exec.InstantiateInit

/-!
# Spec-faithful instantiation: the configuration of `$instantiate` as the start phase

The Wasm 3.0 specification instantiates a module `m` against external addresses
`xas` in two parts (§4.4, `$instantiate`): allocation (`$evalglobals`, the table
and element initialisers, `$allocmodule`), which yields a store and a module
instance, and then a **configuration**
`(s, {module := mi}, runelem* rundata* (call start)?)` that the ordinary
reduction relation runs: element and data segment initialisation, then the
start function. silmaril-lean's `Instantiate P host s m xas c` is that
specification, `c` the configuration; `prepare?` computes its allocation part
and its segment-initialisation code (`prepare?_sound`: `c.withStart st`
satisfies `Instantiate P host s m xas` for **every** profile and host).

Here the instantiation phase of the game is that configuration, run by
**unchanged Core 3.0 reduction** under an arbitrary profile:

* `importAddrs mt`: the import addresses `0, …, n - 1` (fresh host functions
  in `importStore`).
* `configThread c`: the thread of a configuration (its frame and code), so
  that `(configThread c).config c.store = c`.
* `IsSpecInstance m mt I c₀`: `m` validates with type `mt`, its imports are
  functions of the scalar types `I.imports`, `prepare?` allocates it into
  `importStore` with store `I.store` and export function addresses `I.addrs`,
  and `c₀` is the configuration of `$instantiate` (segment initialisation, then
  `call x` for the module's actual `start` field, if any); the exports have the
  scalar types `I.exports`. Nothing is assumed about the start function: its
  type is checked by validation, and segment initialisation may trap.
* `IsSpecInstanceAt s xas m mt I c₀`: the same against an arbitrary typed
  store `s` and external addresses `xas` of the module's import types
  (`ExternAddrOk`, so imports are matched up to subtyping as in the spec). The
  imports may be **globals, memories, tables, tags and functions**; the host
  functions of `s` are the imports of the game (`I.HostTyped s`), everything
  else in `s` (imported state, Wasm functions of other instances) is owned by
  the closed program. This is a sound restriction on environments, the one of
  `hostOf`: the environment answers import calls and never reads or writes the
  store, so imported state is not shared with it. `IsSpecInstance` is the case
  `s = importStore …`, `xas = importAddrs mt`.
* `I.specSys P c₀`, `I.specStrategy P c₀`: the instantiable system and the
  divergence-observing strategy of the instance whose instantiation question
  runs `c₀` (`instSysT` at the thread of `c₀`); `I.closedSpec P c₀ K`: the
  closed program against an environment `K`.
* `InstantiatesTo P host c₀ s'`: the spec's instantiation run returns at the
  store `s'`.

Unlike `IsInstanceStart` (which uses silmaril-lean's `instantiateOnce?`, a
deviation allocating every global once and running segment initialisation as a
function), the store and the code here are exactly the specification's: the
globals are allocated twice as `$evalglobals` and `$allocmodule` do, and the
segment initialisation is the `memory.init`/`table.init`/`data.drop`/
`elem.drop` code reduced step by step under the profile `P`.

New definitions.
-/

@[expose] public section

open Silmaril.Wasm.Numerics (Profile)

namespace Silmaril.Wasm.Game

open Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm Silmaril.Wasm.Execution.Core
  Silmaril.Wasm.Validation Silmaril.Wasm.SingleThreaded

/-- The thread of a Core configuration: its frame and its code. -/
def configThread (c : Config Nat) : Thread := .active c.frame c.code

/-- The host functions of the store `s` are imports of `I`, of their scalar types: a function of
`s` with host code `h` is the import `h` of `I`. -/
def ScalarInstance.HostTyped (I : ScalarInstance) (s : Store Nat) : Prop :=
  ∀ (a : Nat) (fi : FuncInst Nat) (h : Nat), s.funcs[a]? = some fi →
    fi.code = .host h → ∃ hlt : h < I.imports.length, Expand fi.type (I.imports.get ⟨h, hlt⟩).toComp

/-- `I` is the instance of the module `m` (of validated type `mt`) instantiated by the
specification into the store `s` against the external addresses `xas`, and `c₀` is the
configuration of `$instantiate`. The store `s` may hold anything typed: imported globals,
memories, tables and tags, Wasm functions of other instances, and host functions, which are the
imports `I.imports` of the game (`HostTyped`). Everything in `s` other than the host functions
is owned by the closed program: the environment answers host calls and does not access the
store (see the module docstring). -/
structure IsSpecInstanceAt (s : Store Nat) (xas : List ExternAddr) (m : Module)
    (mt : CModuleType) (I : ScalarInstance) (c₀ : Config Nat) : Prop where
  valid : validate? m = some mt
  storeOk : StoreOk s
  importsOk : List.Forall₂ (ExternAddrOk s) xas mt.imports
  hostTyped : I.HostTyped s
  prepared : ∃ (c : Config Nat) (st : Option FuncIdx),
    prepare? evalConst? s m xas = some (c, st) ∧
      c₀ = c.withStart st ∧ c.store = I.store ∧ exportFuncAddrs c.frame.module = I.addrs
  exportTypes : List.Forall₂
    (fun a ft => ∃ fi : FuncInst Nat, I.store.funcs[a]? = some fi ∧
      FnType.ofDefType? fi.type = some ft) I.addrs I.exports

/-- `I` is the instance of the module `m` (of validated type `mt`) against fresh host functions
for its imports, and `c₀` is the configuration of the specification's `$instantiate` (segment
initialisation, then the call of the module's start function); see the module docstring. -/
structure IsSpecInstance (m : Module) (mt : CModuleType) (I : ScalarInstance)
    (c₀ : Config Nat) : Prop where
  valid : validate? m = some mt
  funcImports : ∀ xt ∈ mt.imports, ∃ d, xt = .func d
  importTypes : List.Forall₂ (fun d ft => FnType.ofDefType? d = some ft)
    (CExternType.funcs mt.imports) I.imports
  prepared : ∃ (c : Config Nat) (st : Option FuncIdx),
    prepare? evalConst? (importStore (CExternType.funcs mt.imports)) m (importAddrs mt) =
        some (c, st) ∧
      c₀ = c.withStart st ∧ c.store = I.store ∧ exportFuncAddrs c.frame.module = I.addrs
  exportTypes : List.Forall₂
    (fun a ft => ∃ fi : FuncInst Nat, I.store.funcs[a]? = some fi ∧
      FnType.ofDefType? fi.type = some ft) I.addrs I.exports

/-- The spec's instantiation run from `c₀` returns `values []` at the store `s'`. -/
def InstantiatesTo (P : Profile) (host : HostSemantics Nat) (c₀ : Config Nat)
    (s' : Store Nat) : Prop :=
  ∃ c', Steps P host c₀ c' ∧ c'.code = (Result.values []).toAdmin ∧ c'.store = s'

namespace ScalarInstance

variable (I : ScalarInstance)

/-- The instantiable system whose instantiation question runs the configuration `c₀`. -/
noncomputable def specSys (P : Profile) (c₀ : Config Nat) :
    InstSystem I.E I.F (Behaviour Val) :=
  I.instSysT P c₀.store (configThread c₀)

/-- **The strategy of a module instance including the spec's instantiation**, divergence
observed. -/
noncomputable def specStrategy (P : Profile) (c₀ : Config Nat) :
    DStrategy I.E (I.F.withInst (Behaviour Val)) :=
  DStrategy.ofInst (I.specSys P c₀)

/-- **The closed program including the spec's instantiation**, divergence observed. -/
noncomputable def closedSpec (P : Profile) (c₀ : Config Nat) (K : Env I.E) :
    DStrategy Sig.empty (I.F.withInst (Behaviour Val)) :=
  I.closedInstT P c₀.store (configThread c₀) K

end ScalarInstance

end Silmaril.Wasm.Game
