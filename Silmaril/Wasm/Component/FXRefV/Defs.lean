module

public import Silmaril.Wasm.Component.FXEngineV.Defs

/-!
# The reference-machine half for components whose modules carry FX functions: definitions

`FXRefE.refToSpecE_fx` covers simple components whose core module is a Core module seen as an
FX module with no FX functions (`FXRef.ofCoreFX`). This module states the machine half for
components whose module **carries FX functions**, over the WasmFX engine with suspension
`fxEV P` (`Silmaril.Wasm.Component.FXEngineV`), where FX functions are in the function index space
of the FX code, threads run by `StepFX'`, and code can suspend and resume.

* `fxIface fxs`: the flat interface of FX function declarations (export name, flat type);
* `SimpleFX`: a simple component over an FX module: a Core module with its Core function
  exports (`core : NumModule`), FX function declarations `fxs`, and lifted exports `exports`
  whose index `x.core` points into the Core exports followed by the FX exports;
  * `SimpleFX.mod`: its IR module (Core exports, then FX exports);
  * `SimpleFX.toSimple`: the `Simple` component with that module, so that the reference
    component `c.toSimple.toRef` and the fragment conditions `Good`, `FloatFree`, `Arity` are
    those of `Simple`;
  * `SimpleFX.ofCore`: the core module map of the reference machine: the Core module with the
    FX functions `fxs` attached; `SimpleFX.emb`: the same on IR modules;
  * `SimpleFX.Inst`: the Core part is instantiated as the IR assumes (`Simple.Inst` of the Core
    part), FX export names are distinct and are not export names of the Core module;
  * `SimpleFX.Typed P c`: **FX type soundness at the export types**, as an engine property:
    every value list returned by a call of a lifted export on lowered well-typed arguments, in
    the `fxEV P` engine instance, has the flat result types of the export;
* `RefToSpecFX P`: **the machine half for FX-carrying components**: for a component in the
  fragment of `Reference.refToSpec_of_arity` (`Good`, `FloatFree`, `Inst`, `Arity`) whose engine
  runs are typed, every behaviour of calling export `x` of the reference component, run by the
  reference component machine over `fxEV P`, is an outcome of the engine's own canonical-ABI
  specification `exportSpecE (fxEV P) c.emb`.

`SimpleFX.Typed` is a hypothesis of `RefToSpecFX`. For Core exports it is Core type soundness;
for FX exports it is type soundness of `StepFX'` runs, which is open (`TypedFX` types only
straight-line FX code and has no preservation theorem).

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Component.FXRefV

open Silmaril.Wasm.Component Silmaril.Wasm.Component.Reference Silmaril.Wasm.Component.Param
open Silmaril.Wasm.Component.FXEngine Silmaril.Wasm.Component.FXEngineV
open Silmaril.Wasm.Numerics (Profile)

/-- The flat interface of FX function declarations. -/
def fxIface (fxs : List FXDecl) : CoreIface :=
  fxs.map fun d => (d.name, ⟨d.type.params, d.type.results⟩)

/-- A simple component over an FX module. -/
structure SimpleFX where
  /-- The Core module, with its Core function exports. -/
  core : NumModule
  /-- The FX functions of the module. -/
  fxs : List FXDecl
  /-- The lifted exports (indices into the Core exports, then the FX exports). -/
  exports : List SimpleExport

namespace SimpleFX

/-- The IR module: Core exports, then FX exports. -/
def mod (c : SimpleFX) : NumModule := ⟨c.core.mod, c.core.exports ++ fxIface c.fxs⟩

/-- The component as a `Simple` component. -/
def toSimple (c : SimpleFX) : Simple := ⟨c.mod, c.exports⟩

/-- The core module map of the reference machine: attach the FX functions. -/
def ofCore (c : SimpleFX) (m : Silmaril.Wasm.Module) : ModuleFX := ⟨m, c.fxs⟩

/-- The FX module of an IR module. -/
def emb (c : SimpleFX) (m : NumModule) : ModuleFX := ⟨m.mod, c.fxs⟩

/-- The Core part, as a simple component with no exports. -/
def coreSimple (c : SimpleFX) : Simple := ⟨c.core, []⟩

/-- **The module of `c` is instantiated as the IR assumes.** -/
structure Inst (c : SimpleFX) : Prop where
  /-- The Core part is instantiated as the IR assumes. -/
  core : c.coreSimple.Inst
  /-- FX export names are distinct. -/
  nodup : (c.fxs.map (·.name)).Nodup
  /-- FX export names are not export names of the Core module. -/
  fresh : ∀ d ∈ c.fxs, d.name ∉ c.core.mod.exports.map (·.name)

/-- **FX type soundness at the export types**: returned values of the engine instance's export
calls on lowered well-typed arguments have the export's flat result types. -/
def Typed (P : Profile) (c : SimpleFX) : Prop :=
  ∀ J, instOf (fxEV P) (c.emb c.mod) [] c.mod.exports = some J →
    ∀ x ∈ c.exports, ∀ vs, ValTy.checkList x.ty.params vs = true →
      ∀ ys, some ys ∈ engineOut (fxEV P) J x.core (lowerArgs x.ty.params vs) →
        ys.map (·.type) = ValTy.flatList x.ty.results

end SimpleFX

/-- **The reference-machine half for components whose modules carry FX functions**, over the
WasmFX engine with suspension. -/
def RefToSpecFX (P : Profile) : Prop :=
  ∀ (prof : Silmaril.Wasm.Component.ProfileKind) (c : SimpleFX), c.toSimple.Good →
    c.toSimple.FloatFree → c.Inst → c.toSimple.Arity → c.Typed P →
    ∀ x ∈ c.exports, ∀ vs, ValTy.checkList x.ty.params vs = true →
      exportBehaviours prof (refHostE (fxEV P)) () (c.toSimple.toRef.map c.ofCore) [] x.name
          (vs.map toRefVal) ⊆
        exportSpecE (fxEV P) c.emb c.toSimple x vs

end Silmaril.Wasm.Component.FXRefV
