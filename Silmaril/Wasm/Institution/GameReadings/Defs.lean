module

public import Silmaril.Logic.Inst.Thms
public import Silmaril.Wasm.Institution.GameInst.Defs
public import Silmaril.Wasm.Institution.SpecGInst.Defs

/-!
# The comorphisms into `GInst` as game readings

The two comorphisms into the institution of game semantics,

* `GameInst.coHom G E : Inst.CoHom (gameSem G E).inst GInst` (`Silmaril.Wasm.Institution.GameInst`)
  and
* `SpecGInst.specCoHom L : Inst.CoHom (traceInst L) GInst` (`Silmaril.Wasm.Institution.SpecGInst`),

are defined as the comorphisms of the game readings `GameInst.reading G E` and
`SpecGInst.reading L` (builder `GInst.Reading.coHom`, `Silmaril.Games.InstFacade.Defs`): a game per
signature, a reading of strategies as models, and the naturality of the reading. Their
corridors and naturality are `Reading.corridor` and `Reading.sen_map`.

This module states the translations of the two comorphisms in the facade's names
(`Silmaril.Inst`: `Comorphism.sig`, `Comorphism.sen`, `Comorphism.mod`, `⊨[A]`):

* `GameInst.coHom_sig`, `coHom_sen'`, `coHom_mod`, `coHom_sat_iff`;
* `SpecGInst.specCoHom_sig`, `specCoHom_sen`, `specCoHom_mod`, `specCoHom_sat_iff`.

Model-expansiveness of `GameInst.coHom` is in `Silmaril.Wasm.Institution.GameReadings.Thms`.

New lemmas (all `rfl`).
-/

@[expose] public section

open CategoryTheory Silmaril.Logic.Institution Silmaril.Inst
open Silmaril.Games (Game GSen GInst)

namespace Silmaril.Wasm.Institution.GameInst

open Silmaril.Wasm.Institution.Games (GameIfaces gameSem)

variable (G : GameIfaces) (E : Silmaril.Games.Sig.{0})

@[simp] theorem coHom_sig (A : Silmaril.Wasm.Institution.Sig G.I) :
    Comorphism.sig (coHom G E) A = gameOf G E A := rfl

@[simp] theorem coHom_sen' (A : Silmaril.Wasm.Institution.Sig G.I) (s : (gameSem G E).Sen A) :
    Comorphism.sen (coHom G E) A s = senOf G E A s := rfl

@[simp] theorem coHom_mod (A : Silmaril.Wasm.Institution.Sig G.I) (σ : (gameOf G E A).Model) :
    Comorphism.mod (coHom G E) A σ = modOf G E A σ := rfl

/-- **Satisfaction transfer along `coHom`**, in the facade's notation: a strategy satisfies the
translated sentence iff its model assignment satisfies the sentence. -/
theorem coHom_sat_iff (A : Silmaril.Wasm.Institution.Sig G.I) (σ : (gameOf G E A).Model)
    (s : (gameSem G E).Sen A) :
    σ ⊨[GInst] Comorphism.sen (coHom G E) A s ↔ modOf G E A σ ⊨[(gameSem G E).inst] s :=
  Iff.rfl

end Silmaril.Wasm.Institution.GameInst

namespace Silmaril.Wasm.Institution.SpecGInst

open Silmaril.Wasm.Spec (Logic Sen)

variable {Ty A R : Type} (L : Logic Ty A R)

@[simp] theorem specCoHom_sig (X : IfaceB Ty) :
    Comorphism.sig (specCoHom L) X = GameInst.specGame A R X.X := rfl

@[simp] theorem specCoHom_sen (X : IfaceB Ty) (s : Sen L X.X) :
    Comorphism.sen (specCoHom L) X s = senOf L X s := rfl

@[simp] theorem specCoHom_mod (X : IfaceB Ty) (σ : (GameInst.specGame A R X.X).Model) :
    Comorphism.mod (specCoHom L) X σ = (traceModel (A := A) (R := R) X).obj σ := rfl

/-- **Satisfaction transfer along `specCoHom`**, in the facade's notation: a strategy satisfies the
translated sentence iff its trace model does. -/
theorem specCoHom_sat_iff (X : IfaceB Ty) (σ : (GameInst.specGame A R X.X).Model)
    (s : Sen L X.X) :
    σ ⊨[GInst] Comorphism.sen (specCoHom L) X s ↔
      (traceModel (A := A) (R := R) X).obj σ ⊨[traceInst L] s :=
  Iff.rfl

end Silmaril.Wasm.Institution.SpecGInst
