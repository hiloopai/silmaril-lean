module

public import Silmaril.Wasm.Institution.Games.Defs
public import Silmaril.Wasm.Component.Pipeline.Thms

@[expose] public section

/-!
# Modules versus components, as institutions

Logics over the component IR `Silmaril.Wasm.Component`, all instances of the strategy semantics of
`Silmaril.Wasm.Institution.Games` (`GameIfaces.stratSem`). They are parametric in the core module
type `M` (with `CoreModule M`) and in a core semantics `C : CoreSem M`, an arbitrary strategy
per module.

## Interfaces and semantic objects

Components are denoted over the universal signature `sigU` (`Comp.denU C c : Strategy sigU
sigU`): an operation is a function index with a payload. `compIfaces` takes sets of export
indices `X : Set Nat` as interfaces; `compSig X` has the operations of `sigU` whose index lies in
`X`. The reduct hides the exports outside `X`. Semantic objects at `X` are strategies
`Strategy sigU (compSig X)`: the lower side is the components' imports (`sigU`), and the upper
side the observed exports. `ιU : Sig.Hom (compSig univ) sigU` is an isomorphism with inverse
`ιU'`, so restriction along it reflects refinement (`restrict_ιU_le_iff` in `Thms`).

## The logics (`compIfaces`, lower signature `sigU`)

* `moduleSem C`: programs are core modules `m : M`, denoting `modU C m`: `C.sem m` between the
  boundary handlers `narrowH` (imports) and `widenH` (exports), out-of-range calls trapping;
* `compSem C`: programs are nested components, denoting `Comp.denU C`;
* `linkedSem C`: flat components, `Linked.denU C`;
* `programSem C`: programs (components with observed exports), `Program.denU C`;
* the component game logic `gameSem compIfaces sigU` (programs are strategies).

Sentences are refinements `⊑` and equations `≐` (strategy refinement, i.e. inclusion of plays,
observed through the scope), and conjunctions. Operators are environments
`τ : Strategy sigU sigU` linked below (`τ.comp σ`: an implementation of the imports).

## The trivial wrapping component

`wrap m` is the component with the imports of `m`, one core instance of `m` whose imports are
forwarded (`Impl.fwd i`), and exports forwarding the instance's exports. The wrapping is at the
**core level**: there are no canonical-ABI `lift`/`lower` adapters, since with them the
component's meaning is the module's composed with the adapter handlers. The function types of
the wrapper's interface are placeholders (`⟨[], []⟩`); the component semantics is dynamically
typed and only uses the interface lengths.

`WrapAdequate C` (every `wrap m` denotes `modU C m`) is the statement that wrapping preserves
meaning. It is proved for every `C` in `Silmaril.Proofs.Wasm.Institution.Components.Wrap`
(`wrapAdequate`), from the pairing laws and a right-projection law. The translations here take
the proof, and the pairing laws for flattening, as arguments; `Silmaril.Wasm.Institution.CompGraph`
instantiates them.
-/

namespace Silmaril.Wasm.Institution.Components

open CategoryTheory ObsSemantics Silmaril.Wasm.Institution.Games
open Silmaril.Wasm.Component

/-- The signature of the exports with index in `X`. -/
def compSig (X : Set Nat) : Silmaril.Games.Sig.{0} :=
  ⟨{q : Nat × Payload // q.1 ∈ X}, fun _ => Option Payload⟩

/-- Sets of export indices as game interfaces. -/
def compIfaces : GameIfaces where
  I := Set Nat
  sig := compSig
  hom f := ⟨fun q => ⟨q.1, f.le q.2⟩, fun _ n => n⟩
  hom_id _ := rfl
  hom_comp _ _ := rfl
  top := Set.univ
  toTop X := homOfLE (Set.subset_univ X)
  toTop_top := rfl

/-- The full export signature is `sigU`. -/
def ιU : Silmaril.Games.Sig.Hom (compSig Set.univ) sigU := ⟨fun q => q.1, fun _ n => n⟩

/-- The inverse of `ιU`. -/
def ιU' : Silmaril.Games.Sig.Hom sigU (compSig Set.univ) := ⟨fun q => ⟨q, trivial⟩, fun _ n => n⟩

/-- A strategy over `sigU` at the top component interface. -/
def top (σ : Silmaril.Games.Strategy sigU sigU) :
    Silmaril.Games.Strategy sigU (compIfaces.sig compIfaces.top) :=
  σ.restrict ιU

variable {M : Type} [CoreModule M] (C : CoreSem M)

/-- A core module over `sigU`: its strategy between the boundary handlers. -/
def modU (m : M) : Silmaril.Games.Strategy sigU sigU :=
  (Silmaril.Games.Strategy.ofHandler (narrowH (CoreModule.imports m).length)).comp
    ((C.sem m).comp (Silmaril.Games.Strategy.ofHandler (widenH (CoreModule.exports m).length)))

/-- The core-module logic. -/
abbrev moduleSem : ObsSemantics compIfaces.I :=
  compIfaces.stratSem sigU M fun m => top (modU C m)

/-- The nested-component logic. -/
abbrev compSem : ObsSemantics compIfaces.I :=
  compIfaces.stratSem sigU (Comp M) fun c => top (c.denU C)

/-- The flat-component logic. -/
abbrev linkedSem : ObsSemantics compIfaces.I :=
  compIfaces.stratSem sigU (Linked M) fun l => top (l.denU C)

/-- The program logic (components with observed exports). -/
abbrev programSem : ObsSemantics compIfaces.I :=
  compIfaces.stratSem sigU (Program M) fun p => top (p.denU C)

/-- The component game logic. -/
abbrev compGameSem : ObsSemantics compIfaces.I := gameSem compIfaces sigU

/-- Placeholder function type of the wrapper's interface (the semantics only uses lengths). -/
def anyTy : FuncTy := ⟨[], []⟩

/-- **The trivial component wrapping a core module** (core-level, no ABI adapters). -/
def wrap (m : M) : Comp M :=
  .mk ((CoreModule.imports m).map fun x => (x.1, anyTy))
    [.core m ((List.range (CoreModule.imports m).length).map Impl.fwd)]
    ((List.range (CoreModule.exports m).length).map fun j =>
      ⟨((CoreModule.exports m)[j]?.map Prod.fst).getD "", anyTy,
        Impl.fwd ((CoreModule.imports m).length + j)⟩)

/-- **Wrapping preserves meaning**: the wrapper of every module denotes the module (proved as
`wrapAdequate`). -/
def WrapAdequate : Prop := ∀ m : M, (wrap m).denU C = modU C m

/-- A core semantics given by reduction semantics of the modules. -/
def CoreSem.ofReduction (red : ∀ m : M, Silmaril.Games.Reduction (CoreIface.sig (CoreModule.imports m))
    (CoreIface.sig (CoreModule.exports m))) : CoreSem M :=
  ⟨fun m => Silmaril.Games.Strategy.ofReduction (red m)⟩

/-! ## Translations -/

/-- Flat components into nested ones (`Linked.toComponent`). -/
def linkedToComp : Translation (𝟭 compIfaces.I) (linkedSem C) (compSem C) :=
  stratT compIfaces sigU Linked.toComponent fun l => by
    show top (l.toComponent.denU C) = top (l.denU C)
    rw [Linked.denU_toComponent]

/-- **Flattening** nested components, for a proof of `PairLaws` (e.g. `pairLaws`). -/
def flattenTr (L : PairLaws) : Translation (𝟭 compIfaces.I) (compSem C) (linkedSem C) :=
  stratT compIfaces sigU flatten fun c => by
    show top ((flatten c).denU C) = top (c.denU C)
    rw [denU_flatten L]

/-- Components into programs observing all exports. -/
def compToProgram : Translation (𝟭 compIfaces.I) (compSem C) (programSem C) :=
  stratT compIfaces sigU (fun c => ⟨c, none⟩) fun _ => rfl

/-- **Modules into components**, by wrapping, for a proof of `WrapAdequate C` (e.g.
`wrapAdequate C`). -/
def wrapTr (h : WrapAdequate C) : Translation (𝟭 compIfaces.I) (moduleSem C) (compSem C) :=
  stratT compIfaces sigU wrap fun m => by
    show top ((wrap m).denU C) = top (modU C m)
    rw [h m]

/-- Modules into games (`modU`). -/
def moduleToGame : Translation (𝟭 compIfaces.I) (moduleSem C) (compGameSem) :=
  stratT compIfaces sigU (fun m => top (modU C m)) fun _ => rfl

/-- **Components into games**: a component goes to its strategy (`Comp.denU`). -/
def compToGame : Translation (𝟭 compIfaces.I) (compSem C) (compGameSem) :=
  stratT compIfaces sigU (fun c => top (c.denU C)) fun _ => rfl

/-- Flat components into games. -/
def linkedToGame : Translation (𝟭 compIfaces.I) (linkedSem C) (compGameSem) :=
  stratT compIfaces sigU (fun l => top (l.denU C)) fun _ => rfl

/-- Programs into games. -/
def programToGame : Translation (𝟭 compIfaces.I) (programSem C) (compGameSem) :=
  stratT compIfaces sigU (fun p => top (p.denU C)) fun _ => rfl

end Silmaril.Wasm.Institution.Components
