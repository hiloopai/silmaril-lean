module

public import Silmaril.Wasm.Institution.GameInst.Defs
public import Silmaril.Wasm.Institution.Components.Defs
public import Silmaril.Wasm.Game.Env.Defs

/-!
# Scalar Wasm instances and components in the institution of game semantics

The maps of `docs/projects/spectec/README.md` §2 from the Wasm game semantics into `Silmaril.Games.GInst`.

## Components (`Comp.denU`)

`compCoHom C : Inst.CoHom (compSem C).inst GInst`: the logic of components over a core semantics
`C` (`Silmaril.Wasm.Institution.Components.compSem`, programs denoting `Comp.denU C`) composed with
the comorphism `compToGame` into the component game logic and `GameInst.coHom` into `GInst`. Also
`moduleCoHom C` (core modules, `modU C`), `linkedCoHom C` (flat components) and `programCoHom C`
(programs with observed exports).

## Scalar instances (M2)

* `subIfaces S`: the subsets of the operations of a signature `S` as game interfaces (inclusions
  rename operations; the top interface is everything), with `fromTop S : Sig.Hom (sig ⊤) S`;
* `scalarInst imps exps p`: the scalar instance with import types `imps`, export types `exps`,
  export addresses `p.1` and store `p.2`;
* `scalarSem P imps exps`: the strategy semantics whose programs are such instances, denoting
  their M2 strategies `ScalarInstance.strategy P` (`Silmaril.Wasm.Game.Strategy`);
* `scalarCoHom P imps exps : Inst.CoHom (scalarSem P imps exps).inst GInst`: through the
  identity-on-strategies translation into the game logic and `GameInst.coHom`.

The adequacy theorem M2 read in `GInst` (`m2_answers_iff`) is in `Thms`.

New definitions.
-/

@[expose] public section

namespace Silmaril.Wasm.Institution.GameInstMaps

open CategoryTheory Silmaril.Logic.Institution
open Silmaril.Games (GInst)
open Silmaril.Wasm.Institution.Games (GameIfaces gameSem stratT)
open Silmaril.Wasm.Institution.Components
open Silmaril.Wasm.Component (CoreSem CoreModule)
open Silmaril.Wasm.Numerics (Profile)

/-! ## Components -/

section Components

variable {M : Type} [CoreModule M] (C : CoreSem M)

/-- **Components into `GInst`** (`Comp.denU`). -/
noncomputable def compCoHom : Inst.CoHom (compSem C).inst GInst :=
  (compToGame C).coHom.comp (GameInst.coHom compIfaces Silmaril.Wasm.Component.sigU)

/-- Core modules into `GInst` (`modU`). -/
noncomputable def moduleCoHom : Inst.CoHom (moduleSem C).inst GInst :=
  (moduleToGame C).coHom.comp (GameInst.coHom compIfaces Silmaril.Wasm.Component.sigU)

/-- Programs (components with observed exports) into `GInst` (`Program.denU`). -/
noncomputable def programCoHom : Inst.CoHom (programSem C).inst GInst :=
  (programToGame C).coHom.comp (GameInst.coHom compIfaces Silmaril.Wasm.Component.sigU)

end Components

/-! ## Scalar instances -/

/-- The subsets of the operations of `S` as game interfaces. -/
def subIfaces (S : Silmaril.Games.Sig.{0}) : GameIfaces where
  I := Set S.Op
  sig X := ⟨{q // q ∈ X}, fun q => S.Ar q.1⟩
  hom f := ⟨fun q => ⟨q.1, f.le q.2⟩, fun _ n => n⟩
  hom_id _ := rfl
  hom_comp _ _ := rfl
  top := Set.univ
  toTop X := homOfLE (Set.subset_univ X)
  toTop_top := rfl

/-- The top interface of `subIfaces S` renames into `S`. -/
def fromTop (S : Silmaril.Games.Sig.{0}) :
    Silmaril.Games.Sig.Hom ((subIfaces S).sig (subIfaces S).top) S :=
  ⟨fun q => q.1, fun _ n => n⟩

open Silmaril.Wasm.Game (ScalarInstance ifaceSig FnType)

/-- The scalar instance with the given interface types, export addresses and store. -/
def scalarInst (imps exps : List FnType)
    (p : List Nat × Silmaril.Wasm.Execution.Core.Store Nat) : ScalarInstance :=
  ⟨imps, exps, p.1, p.2⟩

/-- The M2 strategy of a scalar instance, at the top interface of `subIfaces`. -/
noncomputable def scalarTop (P : Profile) (imps exps : List FnType)
    (p : List Nat × Silmaril.Wasm.Execution.Core.Store Nat) :
    Silmaril.Games.Strategy (ifaceSig imps) ((subIfaces (ifaceSig exps)).sig (subIfaces _).top) :=
  ((scalarInst imps exps p).strategy P p.2).restrict (fromTop (ifaceSig exps))

/-- **The M2 logic of scalar instances**: programs are instances, denoting their strategies. -/
noncomputable def scalarSem (P : Profile) (imps exps : List FnType) :
    ObsSemantics (subIfaces (ifaceSig exps)).I :=
  (subIfaces (ifaceSig exps)).stratSem (ifaceSig imps)
    (List Nat × Silmaril.Wasm.Execution.Core.Store Nat) (scalarTop P imps exps)

/-- The M2 logic into the game logic: identity on strategies. -/
noncomputable def scalarToGame (P : Profile) (imps exps : List FnType) :
    ObsSemantics.Translation (𝟭 _) (scalarSem P imps exps)
      (gameSem (subIfaces (ifaceSig exps)) (ifaceSig imps)) :=
  stratT _ _ (scalarTop P imps exps) fun _ => rfl

/-- **Scalar Wasm instances (M2) into `GInst`.** -/
noncomputable def scalarCoHom (P : Profile) (imps exps : List FnType) :
    Inst.CoHom (scalarSem P imps exps).inst GInst :=
  (scalarToGame P imps exps).coHom.comp
    (GameInst.coHom (subIfaces (ifaceSig exps)) (ifaceSig imps))

end Silmaril.Wasm.Institution.GameInstMaps
