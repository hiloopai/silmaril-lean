module

public import Silmaril.Wasm.Category.Institution.Defs
public import Silmaril.Compile.Category.PassAPI
public import Silmaril.Wasm.Game.Instantiate.Thms
public import Silmaril.Wasm.Game.DivAdequacy.Thms
public import Silmaril.Wasm.Game.Adequacy.Thms

@[expose] public section

/-!
# Scalar modules, instances and their strategies as languages of closed-world observations

Three further objects of the category of Wasm programs. All share the interfaces `ScalarIface`
(import and export function types over store-independent scalar types, `Silmaril.Wasm.Game`) and
the observations `ClosedObs`: an environment `K` answering the imports, an export call `f`
(export index and typed arguments) and a behaviour `b`.

* `instLang P`: well-formed scalar instances (`ScalarInstance.Ok`). The behaviours are the
  **Core 3.0 behaviours** `behaviours P (hostOf I.imports K) I.store (I.addr f) args` of the
  export call against the host induced by `K`, at an arbitrary profile `P`, for every
  environment `K` throwing only exceptions of the store (`ThrowsBelow`).
* `modLang P`: Core 3.0 modules; the behaviours of a module are those of its instance
  (`IsInstance`: validated, function imports only, no start function, scalar interfaces,
  instantiated by `instantiateOnce?` against fresh host functions); a module without one has
  none.
* `dgameLang`: divergence-observing strategies `DStrategy (ifaceSig imports) (ifaceSig
  exports)` with a bound `n` on the exception addresses environments may answer; the
  behaviours are the observations `dcompositeObs (K.dstrategy.comp δ) f` of the composite with
  the environment's strategy.

Morphisms (`Silmaril.Wasm.Category.Closed.Thms`): `instantiate : modLang P ⟶ instLang P`, a
partial compiler (instantiation), exact on instantiable modules (`instantiateR`), and the
semantic map `denoteR P : Realiser (instLang P) dgameLang`, `I ↦ I.dstrategy P I.store`,
**exact by adequacy** (`ScalarInstance.adequacy_div_comp`): its behaviours are the instance's
Core behaviours. The plain strategy `I.σ P` is its finite part (`forget_dstrategy`).
-/

namespace Silmaril.Wasm.Category

open CategoryTheory Silmaril.Compile.Category Silmaril.Games Silmaril.Wasm.Game Silmaril.Wasm
  Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics Silmaril.Wasm.Validation

/-- A scalar interface: the import and export function types. -/
abbrev ScalarIface : Type := List FnType × List FnType

/-- A closed-world observation at a scalar interface: an environment answering the imports, an
export call and its behaviour. -/
structure ClosedObs where
  /-- The interface observed. -/
  iface : ScalarIface
  /-- The environment of the imports. -/
  env : Env (ifaceSig iface.1)
  /-- The export call (export index and typed arguments). -/
  call : (ifaceSig iface.2).Op
  /-- The observed behaviour. -/
  beh : Behaviour Val

/-- The scalar interface of an instance. -/
abbrev sIface (I : ScalarInstance) : ScalarIface := (I.imports, I.exports)

/-- The Core 3.0 closed-world behaviours of an instance at store `s`, as observations. -/
def instObs (P : Profile) (I : ScalarInstance) (s : Store Nat) : Set ClosedObs :=
  {o | ∃ (K : Env I.E) (f : I.F.Op) (b : Behaviour Val), o = ⟨sIface I, K, f, b⟩ ∧
    ThrowsBelow K s.exns.length ∧ b ∈ behaviours P (hostOf I.imports K) s (I.addr f.1) f.2.1}

/-- **Well-formed scalar instances observed in closed worlds**, through Core 3.0 at profile
`P`. -/
def instLang (P : Profile) : Language.{0} where
  Iface := ScalarIface
  Prog := {I : ScalarInstance // I.Ok}
  iface I := sIface I.1
  Obs := ClosedObs
  beh I := instObs P I.1 I.1.store

/-- A module has an instance. -/
def Instantiable (m : Module) : Prop := ∃ mt I, IsInstance m mt I

/-- The instance of an instantiable module (unique, `IsInstance.unique`). -/
noncomputable def instOf {m : Module} (h : Instantiable m) : ScalarInstance := h.choose_spec.choose

theorem instOf_spec {m : Module} (h : Instantiable m) : IsInstance m h.choose (instOf h) :=
  h.choose_spec.choose_spec

open Classical in
/-- The scalar interface of a module: that of its instance, if any. -/
noncomputable def moduleIface (m : Module) : ScalarIface :=
  if h : Instantiable m then sIface (instOf h) else ([], [])

/-- **Core 3.0 modules observed in closed worlds**: the behaviours of their instance. -/
noncomputable def modLang (P : Profile) : Language.{0} where
  Iface := ScalarIface
  Prog := Module
  iface := moduleIface
  Obs := ClosedObs
  beh m := {o | ∃ mt I, IsInstance m mt I ∧ o ∈ instObs P I I.store}

/-- A program of the divergence-observing game language: an interface, a bound on the exception
addresses its environments may answer, and a divergence-observing strategy. -/
structure DProg where
  /-- The interface. -/
  iface : ScalarIface
  /-- Environments may only throw exceptions with addresses below `bound`. -/
  bound : Nat
  /-- The strategy. -/
  δ : DStrategy (ifaceSig iface.1) (ifaceSig iface.2)

/-- The closed-world observations of a divergence-observing strategy. -/
def DProg.obs (p : DProg) : Set ClosedObs :=
  {o | ∃ (K : Env (ifaceSig p.iface.1)) (f : (ifaceSig p.iface.2).Op) (b : Behaviour Val),
    o = ⟨p.iface, K, f, b⟩ ∧ ThrowsBelow K p.bound ∧
      b ∈ dcompositeObs (K.dstrategy.comp p.δ) f}

/-- **Divergence-observing strategies observed in closed worlds.** -/
def dgameLang : Language.{0} where
  Iface := ScalarIface
  Prog := DProg
  iface p := p.iface
  Obs := ClosedObs
  beh p := p.obs

/-- The denotation of a well-formed instance as a divergence-observing strategy. -/
noncomputable def denote (P : Profile) (I : ScalarInstance) : DProg :=
  ⟨sIface I, I.store.exns.length, I.dstrategy P I.store⟩

end Silmaril.Wasm.Category
