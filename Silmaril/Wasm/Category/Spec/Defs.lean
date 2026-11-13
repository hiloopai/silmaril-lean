module

public import Silmaril.Wasm.Category.Session.Defs
public import Silmaril.Wasm.Category.Closed.Defs
public import Silmaril.Wasm.Game.SpecInst.Thms

@[expose] public section

/-!
# Sessions, spec instantiation and closed games: the session ↔ closed-world edge

Three objects of the category of Wasm programs connecting the export-session world
(`Silmaril.Wasm.Category.Session`) with the game world, all observed through Core 3.0
`Step P host` at an arbitrary profile `P`.

* `envSession P`: Core 3.0 modules observed by export sessions **against environments**: an
  observation `⟨ts, K, o⟩` is an observation `o` of `coreSession P (hostOf ts K)` (the
  admissibility of instantiation or the trace of a session, `moduleObs`) under the host induced
  by the environment `K` for the import types `ts`. For each `ts`, `K` its fibre is
  `coreSession P (hostOf ts K)` (`envToCore`).
* `specLang P`: modules instantiated **by the specification** (`Silmaril.Wasm.Game.SpecInst`:
  `IsSpecInstance m mt I c₀`, `c₀` the configuration of `$instantiate`: segment
  initialisation, then the start function; nothing assumed about either). Observations
  (`SpecObs`): `inst ts K b`, `b ∈ behavioursOf P (hostOf ts K) c₀` (the instantiation run,
  divergence included), and `call S K x f b`, export name `x` resolving to export `f.1`
  (`exportIndex?`), `b` a Core behaviour of the call `f` at a store the instantiation run may
  return at. Environments throw only exceptions of the store (`ThrowsBelow`). The instance is
  chosen (`specOf`); the definitions do not need its uniqueness.
* `closedGameLang`: environment-indexed closed divergence-observing strategies with an
  instantiation phase (`DStrategy Sig.empty (F.withInst (Behaviour Val))`, Silmaril.Games.Inst)
  and an export-name map; observations `instObs` and `obsAfterInst`.

Morphisms (`Silmaril.Wasm.Category.Spec.Thms`): `envToCore P ts K` (projection to a fibre),
`sessionToSpec P : envSession P ⟶ specLang P` (sound: every spec observation is matched by
a session observation of the same module), and `specDenoteR P`, exact by
`IsSpecInstance.adequacy_inst`/`adequacy_after_inst`.
-/

namespace Silmaril.Wasm.Category

open CategoryTheory Silmaril.Compile.Category Silmaril.Games Silmaril.Games.Inst Silmaril.Wasm.Game
  Silmaril.Wasm Silmaril.Wasm.Binaryen Silmaril.Wasm.Execution.Core Silmaril.Wasm.Numerics
  Silmaril.Wasm.Validation

/-! ## Sessions against environments -/

/-- An export-session observation under the host induced by an environment. -/
structure EnvObs where
  /-- The import types. -/
  ts : List FnType
  /-- The environment. -/
  K : Env (ifaceSig ts)
  /-- The session observation under `hostOf ts K`. -/
  o : Exe.CompilerPass.Observation Nat

/-- **Core 3.0 modules observed by export sessions against environments.** -/
def envSession (P : Profile) : Language.{0} where
  Iface := Unit
  Prog := Module
  iface _ := ()
  Obs := EnvObs
  beh m := {e | e.o ∈ (coreSession P (hostOf e.ts e.K)).beh m}

/-! ## Spec instantiation, closed-world observations -/

/-- Observations of a spec-instantiated module in closed worlds. -/
inductive SpecObs where
  /-- The instantiation run under the environment `K` has behaviour `b`. -/
  | inst (ts : List FnType) (K : Env (ifaceSig ts)) (b : Behaviour Val)
  /-- After instantiation, the export named `x` (export `f.1`) called with `f.2` has
  behaviour `b`. -/
  | call (S : ScalarIface) (K : Env (ifaceSig S.1)) (x : String) (f : (ifaceSig S.2).Op)
      (b : Behaviour Val)

open Classical in
/-- The export of `I` that the export name `x` resolves to in the module instance `mi`. -/
noncomputable def exportIndex? (I : ScalarInstance) (mi : ModuleInst) (x : String) :
    Option (Fin I.exports.length) :=
  if h : ∃ j, exportFunc? mi x = some (I.addr j) then some h.choose else none

/-- The Core 3.0 observations of the spec instance `I` with instantiation configuration `c₀`. -/
def specObs (P : Profile) (I : ScalarInstance) (c₀ : Config Nat) : Set SpecObs :=
  {o | ∃ (K : Env I.E) (b : Behaviour Val), o = .inst I.imports K b ∧
      ThrowsBelow K I.store.exns.length ∧ b ∈ behavioursOf P (hostOf I.imports K) c₀} ∪
  {o | ∃ (K : Env I.E) (x : String) (f : I.F.Op) (b : Behaviour Val),
      o = .call (sIface I) K x f b ∧ ThrowsBelow K I.store.exns.length ∧
      exportIndex? I c₀.frame.module x = some f.1 ∧
      ∃ s', InstantiatesTo P (hostOf I.imports K) c₀ s' ∧
        b ∈ behaviours P (hostOf I.imports K) s' (I.addr f.1) f.2.1}

/-- A module has a spec instance. -/
def SpecInstantiable (m : Module) : Prop := ∃ mt I c₀, IsSpecInstance m mt I c₀

/-- The chosen spec instance of a module. -/
noncomputable def specOf {m : Module} (h : SpecInstantiable m) : ScalarInstance × Config Nat :=
  (h.choose_spec.choose, h.choose_spec.choose_spec.choose)

theorem specOf_spec {m : Module} (h : SpecInstantiable m) :
    IsSpecInstance m h.choose (specOf h).1 (specOf h).2 :=
  h.choose_spec.choose_spec.choose_spec

open Classical in
/-- **Modules instantiated by the specification, observed in closed worlds.** -/
noncomputable def specLang (P : Profile) : Language.{0} where
  Iface := Unit
  Prog := Module
  iface _ := ()
  Obs := SpecObs
  beh m := if h : SpecInstantiable m then specObs P (specOf h).1 (specOf h).2 else ∅

/-! ## Closed games with an instantiation phase -/

/-- A program of the closed-game language: environment-indexed closed strategies with an
instantiation phase, an exception bound and an export-name map. -/
structure CGProg where
  /-- The interface. -/
  iface : ScalarIface
  /-- Environments may only throw exceptions below `bound`. -/
  bound : Nat
  /-- The export names. -/
  names : String → Option (Fin iface.2.length)
  /-- The closed program against each environment. -/
  ρ : Env (ifaceSig iface.1) → DStrategy Sig.empty ((ifaceSig iface.2).withInst (Behaviour Val))

/-- The observations of a closed game. -/
def CGProg.obs (p : CGProg) : Set SpecObs :=
  {o | ∃ (K : Env (ifaceSig p.iface.1)) (b : Behaviour Val), o = .inst p.iface.1 K b ∧
      ThrowsBelow K p.bound ∧ b ∈ Silmaril.Wasm.Game.instObs (p.ρ K)} ∪
  {o | ∃ (K : Env (ifaceSig p.iface.1)) (x : String) (f : (ifaceSig p.iface.2).Op)
      (b : Behaviour Val), o = .call p.iface K x f b ∧ ThrowsBelow K p.bound ∧
      p.names x = some f.1 ∧ b ∈ obsAfterInst (p.ρ K) f}

/-- **Closed games with an instantiation phase.** -/
def closedGameLang : Language.{0} where
  Iface := Unit
  Prog := CGProg
  iface _ := ()
  Obs := SpecObs
  beh p := p.obs

/-- The closed game of a spec instance: its closed programs `I.closedSpec P c₀ K`. -/
noncomputable def denoteSpec (P : Profile) (I : ScalarInstance) (c₀ : Config Nat) : CGProg :=
  ⟨sIface I, I.store.exns.length, exportIndex? I c₀.frame.module, fun K => I.closedSpec P c₀ K⟩

end Silmaril.Wasm.Category
